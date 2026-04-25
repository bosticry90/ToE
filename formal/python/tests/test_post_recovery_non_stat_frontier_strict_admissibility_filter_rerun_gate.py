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
    / "post_recovery_non_stat_frontier_strict_admissibility_filter_rerun_20260424_v0.json"
)
PHASE8_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase8_staging_final_readout_20260424_v0.json"
)
UNLOCK_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_seam_cosmo_sr_admissibility_unlock_design_20260424_v0.json"
)
PHASE3_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_20260424_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_non_stat_frontier_strict_admissibility_filter_rerun_gate() -> None:
    report = _read_json(REPORT_PATH)
    phase8 = _read_json(PHASE8_PATH)
    unlock = _read_json(UNLOCK_PATH)
    phase3 = _read_json(PHASE3_PATH)

    assert report["schema_id"] == "POST_RECOVERY_NON_STAT_FRONTIER_STRICT_ADMISSIBILITY_FILTER_RERUN_20260424_v0"
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_strict_admissibility_filter_rerun_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_NON_STAT_FRONTIER_STRICT_ADMISSIBILITY_FILTER_RERUN_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_NON_STAT_FRONTIER_SEAM_COSMO_SR_ADMISSIBILITY_UNLOCK_DESIGN"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_non_stat_frontier_seam_cosmo_sr_admissibility_unlock_design_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_STRICT_ADMISSIBILITY_FILTER_RERUN"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["filter_only"] is True
    assert boundary["seam_execution_allowed"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    assert phase8["posture_readout"]["terminal_outcome"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert unlock["design_decision"]["unlock_ready"] is False
    assert phase3["filter_summary"]["admissible_lane_ids"] == []

    inputs = report["rerun_inputs"]
    assert inputs["cosmo_sr_unlock_ready"] is False
    assert inputs["materially_different_discriminator_declared"] is False
    assert inputs["machine_pinned_observable_binding_present"] is False
    assert inputs["non_replay_basis_declared"] is False
    assert inputs["rl10_ready"] is False
    assert inputs["gr_ready"] is False

    result = report["rerun_result"]
    assert result["lanes_evaluated"] == 3
    assert result["admissible_lane_ids"] == []
    assert result["admissible_non_stat_lane_exists"] is False
    assert result["selected_lane"] == "NONE"
    assert result["execution_authorization"] == "NONE"
    assert result["terminal_outcome"] == "STRICT_ADMISSIBILITY_FILTER_RERUN_COMPLETE_NO_ADMISSIBLE_NON_STAT_LANE"

    posture = report["posture"]
    assert posture["terminal_posture"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert posture["execution_authorization"] == "NONE"
    assert posture["selected_lane"] == "NONE"
    assert posture["cosmo_sr_fresh_hypothesis_authorized"] is False

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
    assert "test_post_recovery_non_stat_frontier_strict_admissibility_filter_rerun_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
