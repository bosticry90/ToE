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
    / "post_recovery_non_stat_frontier_seam_cosmo_sr_materially_different_discriminator_definition_20260424_v0.json"
)
RERUN_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_strict_admissibility_filter_rerun_20260424_v0.json"
)
UNLOCK_PATH = (
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


def test_post_recovery_non_stat_frontier_seam_cosmo_sr_materially_different_discriminator_definition_gate() -> None:
    report = _read_json(REPORT_PATH)
    rerun = _read_json(RERUN_PATH)
    unlock = _read_json(UNLOCK_PATH)
    phase8 = _read_json(PHASE8_PATH)

    assert report["schema_id"] == (
        "POST_RECOVERY_NON_STAT_FRONTIER_SEAM_COSMO_SR_MATERIALLY_DIFFERENT_DISCRIMINATOR_DEFINITION_20260424_v0"
    )
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_seam_cosmo_sr_materially_different_discriminator_definition_20260424_v0"
    assert report["status"] == (
        "DECLARATION_ONLY_NON_STAT_FRONTIER_SEAM_COSMO_SR_MATERIALLY_DIFFERENT_DISCRIMINATOR_DEFINITION_NONCLAIM"
    )

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_NON_STAT_FRONTIER_STRICT_ADMISSIBILITY_FILTER_RERUN"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_non_stat_frontier_strict_admissibility_filter_rerun_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_SEAM_MATERIAL_DIFFERENT_DISCRIMINATOR_DEFINITION"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["definition_only"] is True
    assert boundary["seam_execution_allowed"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    assert rerun["posture"]["terminal_posture"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert rerun["posture"]["execution_authorization"] == "NONE"
    assert unlock["design_decision"]["unlock_ready"] is False
    assert phase8["posture_readout"]["execution_authorization"] == "NONE"

    definition = report["discriminator_definition"]
    assert definition["target_lane"] == "COSMO-SR"
    assert definition["target_row_id"] == "ROW-SEAM-COSMO-SR-001"
    assert definition["baseline_reference"] == "COSMO_SR_CYCLE08_NEGATIVE_BASELINE"
    assert definition["baseline_discriminator_id"] == "COSMOSR_CYCLE08_BASELINE_DSCRIM_v0"
    assert definition["proposed_new_discriminator_id"] == "COSMOSR_MATERIAL_DIFFERENCE_DSCRIM_CANDIDATE_A_v0"
    assert len(definition["material_difference_axes"]) == 3

    observable = definition["observable_binding_contract"]
    assert observable["machine_pinned_observable_binding_present"] is False
    assert observable["binding_artifact_pointer"] == "NONE_DECLARED"
    assert observable["binding_reproducibility_contract_declared"] is False

    non_replay = definition["non_replay_basis_contract"]
    assert non_replay["explicit_non_replay_basis_declared"] is False
    assert non_replay["comparison_against_cycle08_declared"] is False
    assert non_replay["fresh_hypothesis_discriminator_link_declared"] is False

    assert len(definition["acceptance_criteria_for_unlock_consumption"]) == 4

    readout = definition["current_definition_readout"]
    assert readout["materially_different_discriminator_declared"] is False
    assert readout["observable_binding_contract_ready"] is False
    assert readout["non_replay_basis_ready"] is False
    assert readout["definition_ready_for_strict_filter_consumption"] is False

    decision = report["definition_decision"]
    assert decision["terminal_outcome"] == "SEAM_COSMO_SR_MATERIALLY_DIFFERENT_DISCRIMINATOR_DEFINED_NOT_READY"
    assert decision["unlock_element_satisfied"] is False
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
    assert (
        "test_post_recovery_non_stat_frontier_seam_cosmo_sr_materially_different_discriminator_definition_gate.py"
        in validation["targeted_gate_command"]
    )

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
