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
    / "post_recovery_stat_non_der_theorem_row_candidate_search_design_20260424_v0.json"
)
NON_REPLAY_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_non_replay_frontier_reassessment_20260424_v0.json"
)
EXHAUSTION_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_post_der_cycle_exhaustion_readout_review_20260424_v0.json"
)
DER01_CLOSEOUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der01_post_attempt_nonmovement_closeout_review_20260424_v0.json"
)
DER02_CLOSEOUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_post_attempt_nonmovement_closeout_review_20260424_v0.json"
)
STAT_EVIDENCE_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
)
QUALIFICATION_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_non_der_theorem_row_candidate_search_design_gate() -> None:
    report = _read_json(REPORT_PATH)
    non_replay = _read_json(NON_REPLAY_PATH)
    exhaustion = _read_json(EXHAUSTION_PATH)
    der01 = _read_json(DER01_CLOSEOUT_PATH)
    der02 = _read_json(DER02_CLOSEOUT_PATH)
    evidence = _read_json(STAT_EVIDENCE_PATH)
    qualification = _read_json(QUALIFICATION_PATH)

    assert report["schema_id"] == "POST_RECOVERY_STAT_NON_DER_THEOREM_ROW_CANDIDATE_SEARCH_DESIGN_20260424_v0"
    assert report["artifact_id"] == "post_recovery_stat_non_der_theorem_row_candidate_search_design_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_STAT_NON_DER_CANDIDATE_SEARCH_DESIGN_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_STAT_NON_REPLAY_FRONTIER_REASSESSMENT"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_stat_non_replay_frontier_reassessment_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_CANDIDATE_SEARCH_DESIGN"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["search_only"] is True
    assert boundary["review_counts_theorem_gap_delta"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    checkpoint = report["known_state_checkpoint"]
    assert checkpoint["der01_cycle_closed_nonmoving"] is True
    assert checkpoint["der02_cycle_closed_nonmoving"] is True
    assert checkpoint["remaining_der_attempt_authorization"] == 0
    assert checkpoint["theorem_gap_delta"] == 0
    assert checkpoint["theorem_gap_delta_counted"] == 0
    assert checkpoint["fresh_movement_machine_pinned"] is False
    assert checkpoint["non_replay_execution_frontier_opened"] is False
    assert checkpoint["execution_authorization"] == "NONE"

    assert non_replay["decision"]["execution_held"] is True
    assert non_replay["decision"]["new_stat_theorem_row_candidate_declared"] is False
    assert exhaustion["readout_decision"]["theorem_gap_delta_counted"] == 0
    assert der01["attempt_cycle_state"]["remaining_der01_discharge_attempt_authorization"] == 0
    assert der02["attempt_cycle_state"]["remaining_der02_discharge_attempt_authorization"] == 0

    search = report["candidate_search_protocol"]
    assert search["candidate_must_be_non_der"] is True
    assert search["candidate_must_target_row"] == "ROW-PILLAR-STAT-001"
    assert search["candidate_must_specify_blocker_class"] == "THEOREM_GAP"
    assert search["candidate_admissibility_gate"].startswith("DECLARATION_ONLY_CANDIDATE_SPEC_PRESENT")
    assert search["execution_authorization_after_candidate_declaration"] == "NONE_UNTIL_SEPARATE_AUTHORIZATION_REVIEW"

    readout = report["current_search_readout"]
    assert readout["new_non_der_candidate_declared"] is False
    assert readout["new_candidate_id"] == "NONE"
    assert readout["admissible_now"] is False

    assert evidence["summary"]["fresh_movement_machine_pinned"] is False
    assert evidence["summary"]["theorem_gap_delta"] == 0
    assert qualification["summary"]["selected_row"] == "NONE"

    for disallowed in (
        "rerun_der01_attempt_without_new_authorization",
        "rerun_der02_attempt_without_new_authorization",
        "open_packet05",
        "open_seam_work",
        "open_gr_work",
        "open_rl10_work",
        "invoke_master_action",
        "claim_promotion_or_closure",
        "count_theorem_gap_delta_without_machine_pinned_negative_delta",
    ):
        assert disallowed in report["disallowed_next_actions"]

    decision = report["decision"]
    assert decision["terminal_outcome"] == "STAT_NON_DER_CANDIDATE_SEARCH_DESIGN_DEFINED_NO_CANDIDATE_DECLARED"
    assert decision["search_protocol_defined"] is True
    assert decision["new_non_der_candidate_declared"] is False
    assert decision["execution_held"] is True

    validation = report["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_non_der_theorem_row_candidate_search_design_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})