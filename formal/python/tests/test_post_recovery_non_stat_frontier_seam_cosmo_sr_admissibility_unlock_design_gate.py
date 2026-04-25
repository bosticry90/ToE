from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_seam_cosmo_sr_admissibility_unlock_design_20260424_v0.json"
)
PHASE8_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase8_staging_final_readout_20260424_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_non_stat_frontier_seam_cosmo_sr_admissibility_unlock_design_gate() -> None:
    report = _read_json(REPORT_PATH)
    phase8 = _read_json(PHASE8_PATH)

    assert report["schema_id"] == "POST_RECOVERY_NON_STAT_FRONTIER_SEAM_COSMO_SR_ADMISSIBILITY_UNLOCK_DESIGN_20260424_v0"
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_seam_cosmo_sr_admissibility_unlock_design_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_NON_STAT_FRONTIER_SEAM_COSMO_SR_ADMISSIBILITY_UNLOCK_DESIGN_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE8_STAGING_FINAL_READOUT"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_non_stat_frontier_phase8_staging_final_readout_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_SEAM_ADMISSIBILITY_UNLOCK_DESIGN"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["design_only"] is True
    assert boundary["seam_execution_allowed"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    assert phase8["posture_readout"]["terminal_outcome"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert phase8["posture_readout"]["execution_authorization"] == "NONE"

    unlock = report["unlock_contract"]
    assert unlock["target_lane"] == "COSMO-SR"
    assert unlock["target_row_id"] == "ROW-SEAM-COSMO-SR-001"
    assert unlock["baseline_reference"] == "COSMO_SR_CYCLE08_NEGATIVE_BASELINE"
    assert len(unlock["required_unlock_elements"]) == 4

    readout = unlock["current_unlock_readout"]
    assert readout["materially_different_discriminator_declared"] is False
    assert readout["machine_pinned_observable_binding_present"] is False
    assert readout["non_replay_basis_declared"] is False
    assert readout["strict_filter_ready"] is False

    decision = report["design_decision"]
    assert decision["terminal_outcome"] == "SEAM_COSMO_SR_ADMISSIBILITY_UNLOCK_DESIGN_DEFINED_NOT_READY"
    assert decision["unlock_ready"] is False
    assert decision["execution_authorization"] == "NONE"

    for disallowed in (
        "author_cosmo_sr_fresh_hypothesis_execution_packet",
        "authorize_cosmo_sr_execution",
        "open_packet05",
        "open_seam_work",
        "open_gr_work",
        "open_rl10_work",
        "invoke_master_action",
        "claim_promotion_or_closure",
    ):
        assert disallowed in report["disallowed_next_actions"]

    validation = report["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_non_stat_frontier_seam_cosmo_sr_admissibility_unlock_design_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
