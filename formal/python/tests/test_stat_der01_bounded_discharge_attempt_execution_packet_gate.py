from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
EXECUTION_PACKET_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_bounded_discharge_attempt_execution_packet_v0.json"
)
AUTHORIZATION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der01_discharge_attempt_authorization_readiness_review_20260424_v0.json"
)
SURFACE_PATH = REPO_ROOT / "formal" / "output" / "stat_der01_bounded_discharge_attempt_surface_v0.json"
WITNESS_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_der01_entropy_production_sign_definiteness_witness_binding_v0.json"
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
THEOREM_BODY_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_theorem_body_scaffold_cycle01_v0.json"
)
DISCHARGE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json"
)
OBJECT_SURFACE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_object_surface_scaffold_cycle01_v0.json"
)
THEOREM_SURFACE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json"
)

EXPECTED_ARTIFACT_ID = "stat_der01_bounded_discharge_attempt_execution_packet_v0"
EXPECTED_PACKET_ID = "STAT_DER01_BOUNDED_DISCHARGE_ATTEMPT_EXECUTION_PACKET_v0"
EXPECTED_OUTCOME = "STAT_DER01_BOUNDED_DISCHARGE_ATTEMPT_BLOCKER_UNCHANGED"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_der01_bounded_discharge_attempt_execution_packet_gate.py"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _consumed_input(payload: dict, input_id: str) -> dict:
    matches = [item for item in payload["consumed_inputs"] if item["input_id"] == input_id]
    assert len(matches) == 1
    return matches[0]


def test_stat_der01_bounded_discharge_attempt_execution_packet_gate() -> None:
    execution = _read_json(EXECUTION_PACKET_PATH)
    authorization = _read_json(AUTHORIZATION_REPORT_PATH)
    surface = _read_json(SURFACE_PATH)
    witness = _read_json(WITNESS_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    qualification = _read_json(QUALIFICATION_REPORT_PATH)
    packet05 = _read_json(PACKET05_REPORT_PATH)
    theorem_body = _read_json(THEOREM_BODY_PATH)
    discharge = _read_json(DISCHARGE_PATH)
    object_surface = _read_json(OBJECT_SURFACE_PATH)
    theorem_surface = _read_json(THEOREM_SURFACE_PATH)

    execution_packets = sorted(
        path.name for path in (REPO_ROOT / "formal" / "output").glob("stat_der01_bounded_discharge_attempt_execution_packet*.json")
    )
    assert execution_packets == ["stat_der01_bounded_discharge_attempt_execution_packet_v0.json"]

    assert execution["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert execution["artifact_version"] == "v0"
    assert execution["placeholder_template"] is False
    assert execution["payload_sha256"] == _payload_hash(execution["payload"])

    payload = execution["payload"]
    assert payload["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert payload["pillar_id"] == "PILLAR-STAT"
    assert payload["target_id"] == "TARGET-TH-ENTROPY-PLAN"
    assert payload["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert payload["results_row_id"] == "TOE-STAT-DER-01"
    assert payload["status"] == "bounded_discharge_attempt_executed_blocker_unchanged"
    assert payload["execution_packet_id"] == EXPECTED_PACKET_ID
    assert payload["execution_packet_result"] == EXPECTED_OUTCOME
    assert payload["execution_packet_scope"] == "ONE_BOUNDED_DER01_THEOREM_BODY_TO_DISCHARGE_ATTEMPT"

    auth_decision = authorization["authorization_decision"]
    assert auth_decision["one_bounded_der01_discharge_attempt_authorized"] is True
    assert auth_decision["bounded_discharge_attempt_executed_now"] is False
    assert auth_decision["execution_authorization"] == "ONE_BOUNDED_DER01_DISCHARGE_ATTEMPT_ONLY"
    assert auth_decision["theorem_gap_delta_counted"] == 0
    assert EXPECTED_OUTCOME in authorization["allowed_next_packet_outcomes"]

    consumed = payload["authorization_consumed"]
    assert consumed["authorization_report"] == (
        "formal/output/reports/post_recovery_stat_der01_discharge_attempt_authorization_readiness_review_20260424_v0.json"
    )
    assert consumed["authorization_id"] == authorization["authorized_attempt_scope"]["authorization_id"]
    assert consumed["authorized_next_packet"] == authorization["authorized_attempt_scope"]["authorized_next_packet"]
    assert consumed["authorized_attempt_count"] == 1
    assert consumed["consumed_attempt_count"] == 1
    assert consumed["authorization_remaining_after_packet"] == 0
    assert consumed["authorization_state_after_packet"] == "CONSUMED_NO_REMAINING_DER01_DISCHARGE_ATTEMPT_AUTHORIZATION"

    source_hashes = {
        "DER01_PINNED_SIGN_DEFINITENESS_WITNESS": witness["payload_sha256"],
        "DER01_BOUNDED_DISCHARGE_ATTEMPT_SURFACE": surface["payload_sha256"],
        "DER01_THEOREM_BODY_SCAFFOLD": theorem_body["payload_sha256"],
        "DER01_DISCHARGE_SCAFFOLD": discharge["payload_sha256"],
        "DER01_OBJECT_SURFACE_SCAFFOLD": object_surface["payload_sha256"],
        "DER01_THEOREM_SURFACE_SCAFFOLD": theorem_surface["payload_sha256"],
    }
    for input_id, expected_hash in source_hashes.items():
        item = _consumed_input(payload, input_id)
        assert item["expected_payload_sha256"] == expected_hash
        assert item["consumed"] is True

    assert witness["payload"]["status"] == payload["pre_attempt_state"]["witness_status"]
    assert witness["payload"]["sign_definiteness_witness_result"] == payload["pre_attempt_state"]["witness_result"]
    assert surface["payload"]["status"] == payload["pre_attempt_state"]["bounded_discharge_attempt_surface_status"]
    assert surface["payload"]["surface_result"] == payload["pre_attempt_state"]["bounded_discharge_attempt_surface_result"]
    assert theorem_body["payload"]["status"] == payload["pre_attempt_state"]["theorem_body_status"]
    assert discharge["payload"]["status"] == payload["pre_attempt_state"]["discharge_status"]
    assert _consumed_input(payload, "DER01_THEOREM_BODY_SCAFFOLD")["observed_status"] == theorem_body["payload"]["status"]
    assert _consumed_input(payload, "DER01_DISCHARGE_SCAFFOLD")["observed_status"] == discharge["payload"]["status"]

    attempt = payload["attempt_execution"]
    assert attempt["attempt_number"] == 1
    assert attempt["attempt_executed_now"] is True
    assert attempt["surface_success_discriminator_consumed"] is True
    assert attempt["surface_failure_discriminator_consumed"] is True
    assert attempt["witness_artifact_consumed"] is True
    assert attempt["theorem_body_entropy_production_source_placeholder_replaced"] is False
    assert attempt["discharge_future_sign_definiteness_derivation_slot_replaced"] is False
    assert attempt["claim_checkable_derivation_payload_materialized"] is False
    assert attempt["success_event_materialized"] is False
    assert attempt["failure_event_materialized"] is True
    assert attempt["contract_violation_detected"] is False
    assert "theorem_body_entropy_production_source_slot_still_unreplaced_after_attempt" in attempt["failure_triggered_conditions"]
    assert "discharge_future_sign_definiteness_slot_still_unreplaced_after_attempt" in attempt["failure_triggered_conditions"]
    assert "fresh_movement_surface_remains_unpinned" in attempt["failure_triggered_conditions"]

    readout = payload["attempt_readout"]
    assert readout["terminal_outcome"] == EXPECTED_OUTCOME
    assert readout["allowed_outcome_from_authorization"] is True
    assert readout["machine_pinned_negative_theorem_gap_delta"] is False
    assert readout["theorem_gap_delta"] == 0
    assert readout["theorem_gap_delta_counted"] == 0
    assert readout["fresh_movement_machine_pinned"] is False
    assert readout["blocker_reduction_counted_now"] is False
    assert readout["der01_discharge_claimed"] is False
    assert readout["row_truth_change_detected"] is False
    assert readout["promotion_earned"] is False

    post_attempt = payload["post_attempt_state"]
    assert post_attempt["execution_authorization_before_packet"] == "ONE_BOUNDED_DER01_DISCHARGE_ATTEMPT_ONLY"
    assert post_attempt["execution_authorization_after_packet"] == "CONSUMED_NO_REMAINING_DER01_DISCHARGE_ATTEMPT_AUTHORIZATION"
    assert post_attempt["selected_row"] == "NONE"
    assert post_attempt["theorem_gap_delta"] == 0
    assert post_attempt["theorem_gap_delta_counted"] == 0
    assert post_attempt["fresh_movement_machine_pinned"] is False
    assert post_attempt["blocker_reduction_counted_now"] is False
    assert post_attempt["further_der01_discharge_attempt_authorization"] == "NONE"

    assert evidence["summary"]["terminal_outcome"] == post_attempt["stat_evidence_surface_terminal_outcome"]
    assert evidence["summary"]["fresh_movement_machine_pinned"] is False
    assert evidence["summary"]["theorem_gap_delta"] == 0
    assert qualification["summary"]["selected_row"] == "NONE"
    assert qualification["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_NO_ROW_SELECTED"
    assert packet05["summary"]["eligible_for_packet05_bootstrap"] is False
    assert packet05["summary"]["terminal_outcome"] == "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_NOT_ELIGIBLE_UNDER_CURRENT_BOOTSTRAP"

    assert all(value is False for value in payload["forbidden_dependencies"].values())
    for disallowed in (
        "rerun_this_der01_discharge_attempt_without_new_authorization",
        "count_theorem_gap_delta_from_this_attempt",
        "claim_der01_discharge",
        "promote_toe_stat_der_01",
        "open_packet05",
        "inspect_der02_as_compensation",
        "open_seam_work",
        "invoke_master_action",
    ):
        assert disallowed in payload["disallowed_next_actions"]

    gate_contract = payload["gate_contract"]
    assert gate_contract["gate_path"] == EXPECTED_GATE_REL
    assert gate_contract["passing_this_gate_counts_theorem_gap_delta"] is False
    assert gate_contract["passing_this_gate_claims_der01_discharge"] is False
    assert gate_contract["passing_this_gate_authorizes_another_attempt"] is False
    assert gate_contract["passing_this_gate_flips_stat_evidence_surface"] is False

    for required_boundary in (
        "single_bounded_der01_discharge_attempt_readout_only",
        "no_success_event_materialized",
        "no_machine_pinned_negative_theorem_gap_delta",
        "no_theorem_gap_delta_counted",
        "no_der01_discharge_claim",
        "no_additional_der01_attempt_authorization",
        "no_packet05_bootstrap",
        "no_der02_inspection",
        "no_seam_work",
        "no_master_action",
        "no_external_truth_claim",
    ):
        assert required_boundary in payload["non_claim_boundary"]

    for expected_bundle_member in (
        "formal/output/stat_der01_entropy_production_sign_definiteness_witness_binding_v0.json",
        "formal/python/tests/test_stat_der01_entropy_production_sign_definiteness_witness_binding_gate.py",
        "formal/output/stat_der01_bounded_discharge_attempt_surface_v0.json",
        "formal/python/tests/test_stat_der01_bounded_discharge_attempt_surface_gate.py",
        "formal/output/stat_der01_bounded_discharge_attempt_execution_packet_v0.json",
        EXPECTED_GATE_REL,
    ):
        assert expected_bundle_member in payload["expected_new_artifacts_for_next_commit_bundle"]
        assert expected_bundle_member in payload["cross_surface_pointers"] or expected_bundle_member == (
            "formal/output/stat_der01_bounded_discharge_attempt_execution_packet_v0.json"
        )
