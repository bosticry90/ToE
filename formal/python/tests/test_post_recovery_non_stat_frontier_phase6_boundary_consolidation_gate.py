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
    / "post_recovery_non_stat_frontier_phase6_boundary_consolidation_20260424_v0.json"
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
PHASE3_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_20260424_v0.json"
)
PHASE4_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase4_decision_packet_20260424_v0.json"
)
PHASE5_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase5_fallback_hold_design_packet_20260424_v0.json"
)
NON_REPLAY_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_non_replay_frontier_reassessment_20260424_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_non_stat_frontier_phase6_boundary_consolidation_gate() -> None:
    report = _read_json(REPORT_PATH)
    phase1 = _read_json(PHASE1_PATH)
    phase2 = _read_json(PHASE2_PATH)
    phase3 = _read_json(PHASE3_PATH)
    phase4 = _read_json(PHASE4_PATH)
    phase5 = _read_json(PHASE5_PATH)
    non_replay = _read_json(NON_REPLAY_PATH)

    assert report["schema_id"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE6_BOUNDARY_CONSOLIDATION_20260424_v0"
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_phase6_boundary_consolidation_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_NON_STAT_FRONTIER_PHASE6_BOUNDARY_CONSOLIDATION_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE5_FALLBACK_HOLD_DESIGN_PACKET"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_non_stat_frontier_phase5_fallback_hold_design_packet_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_PHASE6_BOUNDARY_CONSOLIDATION"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["consolidation_only"] is True
    assert boundary["review_counts_theorem_gap_delta"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    checks = report["chain_consumption_checks"]
    assert checks["baseline_carried_forward"] is True
    assert checks["candidate_intake_consumed_baseline"] is True
    assert checks["admissibility_filter_consumed_intake"] is True
    assert checks["decision_packet_consumed_filter"] is True
    assert checks["fallback_hold_consumed_decision"] is True
    assert checks["phase1_to_phase5_chain_unbroken"] is True

    assert phase1["decision"]["phase1_baseline_lock_complete"] is True
    assert phase2["intake_decision"]["phase2_candidate_intake_complete"] is True
    assert phase3["decision"]["phase3_strict_filter_complete"] is True
    assert phase4["frontier_decision"]["terminal_outcome"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert phase5["decision"]["phase5_fallback_hold_design_complete"] is True

    invariants = report["boundary_invariant_consolidation"]
    assert invariants["execution_authorization"] == "NONE"
    assert invariants["selected_lane"] == "NONE"
    assert invariants["cosmo_sr_fresh_hypothesis_authorized"] is False
    assert invariants["all_disallowed_actions_blocked"] is True

    assert phase4["frontier_decision"]["execution_authorization"] == "NONE"
    assert phase4["frontier_decision"]["selected_lane"] == "NONE"
    assert phase5["decision"]["execution_authorization"] == "NONE"
    assert phase5["decision"]["selected_lane"] == "NONE"
    assert phase5["decision"]["cosmo_sr_fresh_hypothesis_authorized"] is False
    assert non_replay["decision"]["execution_held"] is True

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
        assert disallowed in invariants["disallowed_action_set"]

    for disallowed in (
        "author_cosmo_sr_fresh_hypothesis_design_packet_under_current_hold",
        "authorize_cosmo_sr_hypothesis_execution",
        "select_lane_without_new_admissible_filter_pass",
    ):
        assert disallowed in invariants["phase5_additional_disallowed_actions"]

    validation = report["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_non_stat_frontier_phase6_boundary_consolidation_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
