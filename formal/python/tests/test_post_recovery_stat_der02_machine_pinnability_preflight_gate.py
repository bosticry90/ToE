from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PREFLIGHT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_machine_pinnability_preflight_20260424_v0.json"
)
REASSESSMENT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_20260424_v0.json"
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

EXPECTED_SCHEMA_ID = "POST_RECOVERY_STAT_DER02_MACHINE_PINNABILITY_PREFLIGHT_20260424_v0"
EXPECTED_ARTIFACT_ID = "post_recovery_stat_der02_machine_pinnability_preflight_20260424_v0"
EXPECTED_OUTCOME = "STAT_DER02_DELTA_PREFLIGHT_FUTURE_SOURCE_USABLE_NOT_MACHINE_PINNED"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_der02_machine_pinnability_preflight_gate() -> None:
    preflight = _read_json(PREFLIGHT_PATH)
    reassessment = _read_json(REASSESSMENT_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    qualification = _read_json(QUALIFICATION_REPORT_PATH)
    packet05 = _read_json(PACKET05_REPORT_PATH)

    assert preflight["schema_id"] == EXPECTED_SCHEMA_ID
    assert preflight["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert preflight["status"] == "DECLARATION_ONLY_DER02_MACHINE_PINNABILITY_PREFLIGHT_NONCLAIM"

    trigger = preflight["trigger"]
    assert trigger["source"] == "POST_RECOVERY_STAT_DER02_DECLARATION_ONLY_RESERVE_SOURCE_REASSESSMENT_PACKET"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_stat_der02_declaration_only_reserve_source_reassessment_packet_20260424_v0.json"
    )
    assert trigger["selected_candidate_source_id"] == reassessment["candidate_assessment"]["candidate_source_id"]

    boundary = preflight["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_FRONTIER_DESIGN"
    assert boundary["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert boundary["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert boundary["blocker_class"] == "THEOREM_GAP"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["stat_execution_packet_allowed"] is False
    assert boundary["stat_packet05_bootstrap_allowed"] is False
    assert boundary["der02_execution_allowed_now"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["master_action_allowed"] is False

    question = preflight["preflight_question"]
    assert question["question"] == (
        "Given DER-01 nonmovement closeout and DER-02 reserve-source selection, can TOE-STAT-DER-02 serve as a future machine-pinnable STAT theorem-gap delta source?"
    )
    assert question["answer"] == "YES_AS_DECLARATION_ONLY_FUTURE_SOURCE_CANDIDATE_NOT_MACHINE_PINNED_NOW"

    tuple_under_review = preflight["der02_tuple_under_review"]
    assert tuple_under_review["selected_candidate_source_id"] == "STAT_DER02_REGIME_CLOSURE_COUPLING_DELTA_SOURCE_v0"
    assert tuple_under_review["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert len(tuple_under_review["required_candidate_artifacts"]) == 4
    assert len(tuple_under_review["supporting_candidate_artifacts"]) == 1

    closeness = preflight["closeness_preflight"]
    assert closeness["closeness_to_future_source_candidate"] is True
    assert closeness["machine_pinnable_now"] is False
    assert closeness["criteria"]["row_local_der02_tuple_present"] is True
    assert closeness["criteria"]["doc_artifact_gate_tuple_present"] is True
    assert closeness["criteria"]["regime_closure_slots_present"] is True
    assert closeness["criteria"]["theorem_body_slots_present"] is True
    assert closeness["criteria"]["discharge_slots_present"] is True
    assert closeness["criteria"]["object_surface_slots_present"] is True
    assert closeness["criteria"]["scope_boundary_slots_present"] is True
    assert closeness["criteria"]["no_packet05_dependency"] is True
    assert closeness["criteria"]["no_seam_dependency"] is True
    assert closeness["criteria"]["no_master_action_dependency"] is True
    assert closeness["criteria"]["current_payload_selected_row_stat"] is False
    assert closeness["criteria"]["current_payload_theorem_gap_delta_negative"] is False
    assert closeness["criteria"]["current_payload_fresh_movement_machine_pinned"] is False

    supporting = closeness["supporting_evidence"]
    assert supporting["regime_closure_required_components_count"] == 8
    assert supporting["theorem_body_required_components_count"] == 5
    assert supporting["discharge_required_components_count"] == 5
    assert supporting["object_surface_required_components_count"] == 5
    assert supporting["scope_boundary_required_dependency_slots_count"] == 7
    assert supporting["all_required_der02_artifacts_placeholder_nonclaim"] is True
    assert supporting["all_required_der02_artifacts_link_to_toe_stat_der_02"] is True

    assert len(closeness["blocking_gaps_before_machine_pin"]) == 6

    requirements = preflight["future_machine_pinning_requirements"]
    assert requirements["required_payload"]["selected_row"] == "ROW-PILLAR-STAT-001"
    assert requirements["required_payload"]["theorem_gap_delta"] == "NEGATIVE_INTEGER"
    assert requirements["required_payload"]["fresh_movement_machine_pinned"] is True
    assert len(requirements["der02_specific_required_delta_evidence"]) == 4

    current = preflight["current_machine_pinnability_state"]
    assert current["selected_row"] == "NONE"
    assert current["theorem_gap_delta"] == 0
    assert current["fresh_movement_machine_pinned"] is False
    assert current["candidate_validated_now"] is False
    assert current["theorem_gap_delta_counted"] == 0
    assert current["execution_authorization"] == "NONE"
    assert current["stat_evidence_surface_terminal_outcome"] == evidence["summary"]["terminal_outcome"]

    exclusions = preflight["explicit_exclusions"]
    assert exclusions["stat_execution_authorization"] == "NONE"
    assert exclusions["der02_execution_allowed"] is False
    assert exclusions["theorem_gap_delta_counted"] == 0
    assert exclusions["packet05_allowed"] is False
    assert exclusions["seam_work_allowed"] is False
    assert exclusions["master_action_allowed"] is False
    assert exclusions["promotion_or_closure_claim_allowed"] is False

    decision = preflight["preflight_decision"]
    assert decision["terminal_outcome"] == EXPECTED_OUTCOME
    assert decision["der02_retained_as_selected_source_candidate"] is True
    assert decision["close_enough_for_future_machine_pinnable_delta_search"] is True
    assert decision["machine_pinned_now"] is False
    assert decision["candidate_validated_now"] is False
    assert decision["theorem_gap_delta_counted"] == 0
    assert decision["execution_authorization"] == "NONE"

    assert evidence["summary"]["fresh_movement_machine_pinned"] is False
    assert evidence["summary"]["theorem_gap_delta"] == 0
    assert qualification["summary"]["selected_row"] == "NONE"
    assert packet05["summary"]["eligible_for_packet05_bootstrap"] is False

    validation = preflight["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_der02_machine_pinnability_preflight_gate.py" in validation["targeted_gate_command"]

    assert preflight["payload_sha256"] == _canonical_hash({k: v for k, v in preflight.items() if k != "payload_sha256"})