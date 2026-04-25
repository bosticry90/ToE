from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_20260424_v0.json"
)
DER01_CLOSEOUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der01_post_attempt_nonmovement_closeout_review_20260424_v0.json"
)
STAT_EVIDENCE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
)
QUALIFICATION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json"
)
PACKET05_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_packet05_lane_eligibility_review_20260420_v0.json"
)

EXPECTED_ARTIFACT_ID = "post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_20260424_v0"
EXPECTED_SCHEMA_ID = "POST_RECOVERY_STAT_DER02_DECLARATION_ONLY_RESERVE_SOURCE_REASSESSMENT_PACKET_20260424_v0"
EXPECTED_OUTCOME = "STAT_DER02_DECLARATION_ONLY_RESERVE_SOURCE_REASSESSMENT_SELECTED_NEXT_CANDIDATE_NO_EXECUTION"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_gate() -> None:
    packet = _read_json(PACKET_PATH)
    der01_closeout = _read_json(DER01_CLOSEOUT_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    qualification = _read_json(QUALIFICATION_REPORT_PATH)
    packet05 = _read_json(PACKET05_REPORT_PATH)

    assert packet["schema_id"] == EXPECTED_SCHEMA_ID
    assert packet["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert packet["status"] == "POST_RECOVERY_STAT_DER02_DECLARATION_ONLY_RESERVE_SOURCE_REASSESSMENT_PACKET_NONCLAIM"

    trigger = packet["trigger"]
    assert trigger["source"] == "DER01_POST_ATTEMPT_NONMOVEMENT_CLOSEOUT"
    assert trigger["closeout_report"] == (
        "formal/output/reports/post_recovery_stat_der01_post_attempt_nonmovement_closeout_review_20260424_v0.json"
    )
    assert trigger["required_terminal_outcome"] == der01_closeout["closeout_decision"]["terminal_outcome"]

    closeout = der01_closeout["closeout_decision"]
    assert closeout["terminal_outcome"] == (
        "STAT_DER01_POST_ATTEMPT_NONMOVEMENT_CLOSEOUT_DER01_CLOSED_DER02_DECLARATION_REASSESSMENT_NEXT"
    )
    assert closeout["authorized_attempt_consumed"] is True
    assert closeout["remaining_der01_discharge_attempt_authorization"] == 0
    assert closeout["theorem_gap_delta_counted"] == 0
    assert closeout["fresh_movement_machine_pinned"] is False

    boundary = packet["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_RESERVE_SOURCE_REASSESSMENT"
    assert boundary["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert boundary["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["der02_execution_allowed"] is False
    assert boundary["theorem_gap_delta_counted"] == 0
    assert boundary["packet05_allowed"] is False
    assert boundary["seam_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_claim_allowed"] is False

    question = packet["reassessment_question"]
    assert question["question"] == (
        "Given DER01 nonmovement closeout, should TOE-STAT-DER-02 become the next STAT-attributable theorem-gap delta source candidate?"
    )
    assert question["answer"] == "YES_DECLARATION_ONLY_DER02_NEXT_SOURCE_CANDIDATE"

    candidate = packet["candidate_assessment"]
    assert candidate["candidate_source_id"] == "STAT_DER02_REGIME_CLOSURE_COUPLING_DELTA_SOURCE_v0"
    assert candidate["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert candidate["selected_as_next_candidate_now"] is True
    assert candidate["candidate_validated_now"] is False
    assert candidate["machine_pinned_negative_theorem_gap_delta"] is False
    assert candidate["theorem_gap_delta"] == 0
    assert candidate["theorem_gap_delta_counted"] == 0
    assert candidate["fresh_movement_machine_pinned"] is False
    assert len(candidate["known_der02_scaffold_tuple"]) == 5

    for blocked in (
        "execute_der02",
        "count_theorem_gap_delta",
        "open_packet05",
        "open_seam_work",
        "open_gr_work",
        "open_rl10_work",
        "invoke_master_action",
        "claim_der02_discharge",
        "promote_toe_stat_der_02",
        "claim_pillar_or_theory_closure",
    ):
        assert blocked in candidate["disallowed_actions_in_this_packet"]

    decision = packet["decision"]
    assert decision["terminal_outcome"] == EXPECTED_OUTCOME
    assert decision["der02_selected_as_next_candidate_now"] is True
    assert decision["der02_execution_authorization"] == "NONE"
    assert decision["der02_execution_allowed"] is False
    assert decision["theorem_gap_delta_counted"] == 0
    assert decision["fresh_movement_machine_pinned"] is False

    assert evidence["summary"]["fresh_movement_machine_pinned"] is False
    assert evidence["summary"]["theorem_gap_delta"] == 0
    assert qualification["summary"]["selected_row"] == "NONE"
    assert packet05["summary"]["eligible_for_packet05_bootstrap"] is False

    expected_bundle = packet["expected_new_artifacts_for_next_commit_bundle"]
    for required in (
        "formal/output/stat_der01_entropy_production_sign_definiteness_witness_binding_v0.json",
        "formal/python/tests/test_stat_der01_entropy_production_sign_definiteness_witness_binding_gate.py",
        "formal/output/stat_der01_bounded_discharge_attempt_surface_v0.json",
        "formal/python/tests/test_stat_der01_bounded_discharge_attempt_surface_gate.py",
        "formal/output/stat_der01_bounded_discharge_attempt_execution_packet_v0.json",
        "formal/python/tests/test_stat_der01_bounded_discharge_attempt_execution_packet_gate.py",
        "formal/output/reports/post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_20260424_v0.json",
        "formal/python/tests/test_post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_gate.py",
    ):
        assert required in expected_bundle

    validation = packet["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert packet["payload_sha256"] == _canonical_hash({k: v for k, v in packet.items() if k != "payload_sha256"})
