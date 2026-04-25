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
    / "post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_20260424_v0.json"
)
PHASE1_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase1_baseline_lock_20260424_v0.json"
)
PHASE2_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase2_candidate_intake_20260424_v0.json"
)
NON_REPLAY_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_non_replay_frontier_reassessment_20260424_v0.json"
)
COSMO_SR_BASELINE_STOP_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_cosmo_sr_negative_baseline_frontier_stop_20260424_v0.json"
)
RL10_LIMITATION_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_discrete_transition_bridge_limitation_review_20260422_v2.json"
)
GR_TRANCHE_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_gate() -> None:
    report = _read_json(REPORT_PATH)
    phase1 = _read_json(PHASE1_PATH)
    phase2 = _read_json(PHASE2_PATH)
    non_replay = _read_json(NON_REPLAY_PATH)
    cosmo_sr_baseline_stop = _read_json(COSMO_SR_BASELINE_STOP_PATH)
    rl10_limitation = _read_json(RL10_LIMITATION_PATH)
    gr_tranche = _read_json(GR_TRANCHE_PATH)

    assert report["schema_id"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE3_STRICT_ADMISSIBILITY_FILTER_20260424_v0"
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_NON_STAT_FRONTIER_PHASE3_STRICT_ADMISSIBILITY_FILTER_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE2_CANDIDATE_INTAKE"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_non_stat_frontier_phase2_candidate_intake_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_PHASE3_STRICT_ADMISSIBILITY_FILTER"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["records_readout_only"] is True
    assert boundary["filter_only"] is True
    assert boundary["review_counts_theorem_gap_delta"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    carryforward = report["baseline_token_carryforward"]
    assert carryforward["required_entry_condition"] == "EXACT_MATCH_WITH_LOCKED_BASELINE_INVARIANTS"
    assert carryforward["phase1_token_set"] == phase1["phase_lock_contract"]["baseline_token_set"]
    assert carryforward["token_set_match_phase1"] is True
    assert carryforward["baseline_drift_detected"] is False

    # Phase linkage and posture continuity
    assert phase2["intake_decision"]["phase2_candidate_intake_complete"] is True
    assert phase2["intake_decision"]["execution_authorization"] == "NONE"
    assert non_replay["decision"]["execution_held"] is True

    filter_contract = report["strict_filter_contract"]
    assert filter_contract["applies_to_lanes"] == ["COSMO-SR", "RL10", "GR"]
    assert filter_contract["execution_authorization_after_filter"] == "NONE"
    assert filter_contract["bounded_fallback_order"] == ["RL10", "GR"]

    lane_results = report["lane_filter_results"]
    assert len(lane_results) == 3

    cosmo = lane_results[0]
    assert cosmo["lane_id"] == "COSMO-SR"
    assert cosmo["candidate_id"] == "SEAM-COSMO-SR::POST_RECOVERY_FRESH_HYPOTHESIS_DESIGN"
    assert cosmo["admissibility_result"] == "FAIL"
    assert cosmo["required_prerequisites"]["materially_different_discriminator_machine_pinned"] is False
    assert cosmo["execution_authorization"] == "NONE"

    rl10 = lane_results[1]
    assert rl10["lane_id"] == "RL10"
    assert rl10["admissibility_result"] == "FAIL"
    assert rl10["required_prerequisites"]["uplift_precondition_present"] is False
    assert rl10["required_prerequisites"]["anti_alias_proof_readiness_present"] is False

    gr = lane_results[2]
    assert gr["lane_id"] == "GR"
    assert gr["admissibility_result"] == "FAIL"
    assert gr["required_prerequisites"]["fresh_non_replay_signal_present"] is False
    assert gr["required_prerequisites"]["retry_path_authoritative"] is False

    assert cosmo_sr_baseline_stop["alternative_hypothesis_review"][
        "machine_pinned_materially_different_cosmo_sr_candidate_found"
    ] is False
    assert rl10_limitation["summary"]["review_outcome"] == "LIMITATION_INTERPRETATION_SCOPE_HOLD"
    assert (
        gr_tranche["summary"]["terminal_outcome"]
        == "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"
    )

    summary = report["filter_summary"]
    assert summary["lanes_evaluated"] == 3
    assert summary["lanes_passed"] == 0
    assert summary["lanes_failed"] == 3
    assert summary["admissible_lane_ids"] == []
    assert summary["primary_lane_cosmo_sr_admissible"] is False
    assert summary["fallback_lane_rl10_admissible"] is False
    assert summary["fallback_lane_gr_admissible"] is False
    assert summary["execution_authorization"] == "NONE"
    assert summary["terminal_outcome"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE3_STRICT_FILTER_COMPLETE_NO_ADMISSIBLE_LANE"

    decision = report["decision"]
    assert decision["phase3_strict_filter_complete"] is True
    assert decision["admissible_non_stat_lane_exists"] is False
    assert decision["selected_lane_if_any"] == "NONE"
    assert decision["execution_authorization"] == "NONE"

    for disallowed in (
        "rerun_der01_attempt_without_new_authorization",
        "rerun_der02_attempt_without_new_authorization",
        "count_theorem_gap_delta_without_machine_pinned_negative_delta",
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
    assert "test_post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
