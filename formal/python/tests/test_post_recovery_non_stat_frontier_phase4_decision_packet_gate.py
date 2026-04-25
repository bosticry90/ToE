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
    / "post_recovery_non_stat_frontier_phase4_decision_packet_20260424_v0.json"
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


def test_post_recovery_non_stat_frontier_phase4_decision_packet_gate() -> None:
    report = _read_json(REPORT_PATH)
    phase1 = _read_json(PHASE1_PATH)
    phase2 = _read_json(PHASE2_PATH)
    phase3 = _read_json(PHASE3_PATH)
    non_replay = _read_json(NON_REPLAY_PATH)

    assert report["schema_id"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE4_DECISION_PACKET_20260424_v0"
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_phase4_decision_packet_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_NON_STAT_FRONTIER_PHASE4_DECISION_PACKET_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE3_STRICT_ADMISSIBILITY_FILTER"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_PHASE4_FRONTIER_DECISION"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["decision_only"] is True
    assert boundary["records_readout_only"] is True
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

    assert phase2["intake_decision"]["phase2_candidate_intake_complete"] is True
    assert phase3["decision"]["phase3_strict_filter_complete"] is True
    assert phase3["decision"]["admissible_non_stat_lane_exists"] is False
    assert phase3["filter_summary"]["admissible_lane_ids"] == []
    assert non_replay["decision"]["execution_held"] is True

    imported = report["phase3_summary_import"]
    assert imported["lanes_evaluated"] == phase3["filter_summary"]["lanes_evaluated"]
    assert imported["lanes_passed"] == phase3["filter_summary"]["lanes_passed"]
    assert imported["lanes_failed"] == phase3["filter_summary"]["lanes_failed"]
    assert imported["admissible_lane_ids"] == phase3["filter_summary"]["admissible_lane_ids"]
    assert imported["primary_lane_cosmo_sr_admissible"] is False
    assert imported["fallback_lane_rl10_admissible"] is False
    assert imported["fallback_lane_gr_admissible"] is False

    decision = report["frontier_decision"]
    assert decision["terminal_outcome"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert decision["decision_class"] == "HOLD"
    assert decision["selected_lane"] == "NONE"
    assert decision["execution_authorization"] == "NONE"
    assert decision["admissible_non_stat_lane_exists"] is False

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
    assert "test_post_recovery_non_stat_frontier_phase4_decision_packet_gate.py" in validation["targeted_gate_command"]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
