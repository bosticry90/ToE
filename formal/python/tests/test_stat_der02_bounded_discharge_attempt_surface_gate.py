from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SURFACE_PATH = REPO_ROOT / "formal" / "output" / "stat_der02_bounded_discharge_attempt_surface_v0.json"
READINESS_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_post_witness_discharge_readiness_review_20260424_v0.json"
)
WITNESS_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_consistency_witness_binding_v0.json"
)
WITNESS_GATE_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tests"
    / "test_stat_der02_regime_closure_consistency_witness_binding_gate.py"
)
STAT_EVIDENCE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
)
THEOREM_BODY_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json"
)
DISCHARGE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json"
)
OBJECT_SURFACE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_object_surface_scaffold_cycle01_v0.json"
)
COUPLING_SURFACE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
)
SCOPE_BOUNDARY_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
)

EXPECTED_ARTIFACT_ID = "stat_der02_bounded_discharge_attempt_surface_v0"
EXPECTED_SURFACE_ID = "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_SURFACE_v0"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_der02_bounded_discharge_attempt_surface_gate.py"
EXPECTED_WITNESS_REL = "formal/output/stat_der02_regime_closure_consistency_witness_binding_v0.json"
EXPECTED_WITNESS_GATE_REL = "formal/python/tests/test_stat_der02_regime_closure_consistency_witness_binding_gate.py"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _has_slot(payload: dict, slot: str) -> bool:
    slot_fields = (
        "required_theorem_body_components",
        "required_discharge_components",
        "required_object_surface_components",
        "closure_coupling_requirements",
        "required_dependency_slots",
    )
    return any(slot in payload.get(field, []) for field in slot_fields)


def test_stat_der02_bounded_discharge_attempt_surface_gate() -> None:
    surface = _read_json(SURFACE_PATH)
    readiness = _read_json(READINESS_REPORT_PATH)
    witness = _read_json(WITNESS_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    assert WITNESS_GATE_PATH.exists()

    dependencies = {
        "formal/output/stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json": _read_json(
            THEOREM_BODY_PATH
        )["payload"],
        "formal/output/stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json": _read_json(
            DISCHARGE_PATH
        )["payload"],
        "formal/output/stat_der02_regime_closure_object_surface_scaffold_cycle01_v0.json": _read_json(
            OBJECT_SURFACE_PATH
        )["payload"],
        "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json": _read_json(
            COUPLING_SURFACE_PATH
        )["payload"],
        "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json": _read_json(
            SCOPE_BOUNDARY_PATH
        )["payload"],
    }

    assert surface["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert surface["artifact_version"] == "v0"
    assert surface["placeholder_template"] is False
    assert isinstance(surface["payload"], dict)
    assert surface["payload_sha256"] == _payload_hash(surface["payload"])

    payload = surface["payload"]
    assert payload["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert payload["pillar_id"] == "PILLAR-STAT"
    assert payload["target_id"] == "TARGET-TH-ENTROPY-PLAN"
    assert payload["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert payload["results_row_id"] == "TOE-STAT-DER-02"
    assert payload["results_row_expected_label"] == "T-PROVED"
    assert payload["status"] == "bounded_discharge_attempt_surface_pinned_nonclaim"
    assert payload["surface_id"] == EXPECTED_SURFACE_ID
    assert (
        payload["surface_result"]
        == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_SURFACE_PINNED_NONCLAIM_NOT_EXECUTED"
    )
    assert payload["source_missing_component_id"] == EXPECTED_SURFACE_ID
    assert payload["terminal_outcome"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_SURFACE_AUTHORED_NONCLAIM_NOT_EXECUTED"
    assert payload["artifact_sha256"] == "TOP_LEVEL_payload_sha256"

    readiness_decision = readiness["readiness_decision"]
    assert readiness_decision["terminal_outcome"] == (
        "STAT_DER02_POST_WITNESS_DISCHARGE_READINESS_NOT_READY_ATTEMPT_SURFACE_MISSING"
    )
    assert readiness_decision["witness_binding_prerequisite_satisfied"] is True
    assert readiness_decision["bounded_discharge_attempt_ready_now"] is False
    assert readiness_decision["remaining_missing_component"] == payload["source_missing_component_id"]
    assert readiness_decision["execution_authorization"] == "NONE"
    assert readiness_decision["theorem_gap_delta_counted"] == 0

    witness_payload = witness["payload"]
    assert witness["artifact_id"] == "stat_der02_regime_closure_consistency_witness_binding_v0"
    assert witness["payload_sha256"] == _payload_hash(witness_payload)
    assert witness_payload["status"] == "regime_closure_consistency_witness_binding_pinned_nonclaim"
    assert witness_payload["regime_closure_consistency_witness_result"] == "REGIME_CLOSURE_CONSISTENCY_WITNESS_PINNED_NONCLAIM"
    assert witness_payload["current_delta_boundary"]["execution_authorization"] == "NONE"
    assert witness_payload["current_delta_boundary"]["theorem_gap_delta_counted"] == 0

    attempt_object = payload["discharge_attempt_object"]
    assert attempt_object["object_id"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_OBJECT_v0"
    assert attempt_object["object_class"] == "DECLARATION_ONLY_THEOREM_BODY_TO_DISCHARGE_ATTEMPT_BOUNDARY"
    assert attempt_object["attempt_scope"] == "THEOREM_BODY_TO_DISCHARGE_ONLY"
    assert attempt_object["attempt_executed_now"] is False
    assert attempt_object["attempt_authorized_now"] is False

    required_inputs = {item["input_id"]: item for item in payload["allowed_inputs"]}
    witness_input = required_inputs["DER02_PINNED_REGIME_CLOSURE_CONSISTENCY_WITNESS"]
    assert witness_input["artifact"] == EXPECTED_WITNESS_REL
    assert witness_input["required_status"] == witness_payload["status"]
    assert witness_input["required_result"] == witness_payload["regime_closure_consistency_witness_result"]

    for input_id, item in required_inputs.items():
        if input_id == "DER02_PINNED_REGIME_CLOSURE_CONSISTENCY_WITNESS":
            continue
        dependency_payload = dependencies[item["artifact"]]
        assert dependency_payload["pillar_id"] == "PILLAR-STAT"
        assert dependency_payload["target_id"] == "TARGET-TH-ENTROPY-PLAN"
        assert dependency_payload["results_row_id"] == "TOE-STAT-DER-02"
        assert _has_slot(dependency_payload, item["required_slot"])

    assert "formal/output/reports/post_recovery_stat_der02_post_witness_discharge_readiness_review_20260424_v0.json" in payload[
        "required_gate_inputs"
    ]
    assert EXPECTED_WITNESS_REL in payload["required_gate_inputs"]
    assert EXPECTED_WITNESS_GATE_REL in payload["required_gate_inputs"]

    success = payload["success_discriminator"]
    assert success["success_event_id"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_SUCCESS_EVENT_v0"
    assert success["evaluated_now"] is False
    assert success["current_success_state"] is False
    assert "theorem_body_closure_coupling_constraint_slot_replaced_by_claim_checkable_witness_binding" in success[
        "future_success_requires"
    ]
    assert "discharge_closure_coupling_consistency_slot_replaced_by_matching_claim_checkable_derivation" in success[
        "future_success_requires"
    ]
    assert "theorem_gap_delta_less_than_zero_is_machine_pinned_by_a_later_authorized_surface" in success[
        "future_success_requires"
    ]

    failure = payload["failure_discriminator"]
    assert failure["failure_event_id"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_FAILURE_EVENT_v0"
    assert failure["evaluated_now"] is False
    assert failure["current_failure_state"] is False
    assert "attempt_requires_packet05_seam_master_action_or_promotion_surface" in failure["future_failure_conditions"]

    authorization = payload["authorization_boundary"]
    assert authorization["execution_authorization"] == "NONE"
    assert authorization["stat_execution_packet_authored"] is False
    assert authorization["bounded_discharge_attempt_executed_now"] is False
    assert authorization["authorization_conversion_required_before_execution"] is True
    assert authorization["passing_this_surface_gate_authorizes_execution"] is False

    delta_boundary = payload["current_delta_boundary"]
    assert delta_boundary["selected_row"] == "NONE"
    assert delta_boundary["theorem_gap_delta"] == 0
    assert delta_boundary["fresh_movement_machine_pinned"] is False
    assert delta_boundary["theorem_gap_delta_counted"] == 0
    assert delta_boundary["blocker_reduction_counted_now"] is False
    assert delta_boundary["execution_authorization"] == "NONE"
    assert delta_boundary["stat_evidence_surface_terminal_outcome"] == evidence["summary"]["terminal_outcome"]
    assert evidence["summary"]["fresh_movement_machine_pinned"] is False
    assert evidence["summary"]["theorem_gap_delta"] == 0

    gate_contract = payload["gate_contract"]
    assert gate_contract["gate_path"] == EXPECTED_GATE_REL
    assert gate_contract["passing_this_gate_authorizes_execution"] is False
    assert gate_contract["passing_this_gate_counts_theorem_gap_delta"] is False
    assert gate_contract["passing_this_gate_claims_der02_discharge"] is False
    assert gate_contract["passing_this_gate_flips_stat_evidence_surface"] is False

    assert all(value is False for value in payload["forbidden_dependencies"].values())
    for required_boundary in (
        "no_bounded_discharge_attempt_execution",
        "no_der02_discharge_claim",
        "no_theorem_gap_delta_counted",
        "no_fresh_movement_machine_pinned_claim",
        "no_stat_execution_authorization",
        "no_packet05_bootstrap",
        "no_seam_work",
        "no_master_action",
        "no_external_truth_claim",
    ):
        assert required_boundary in payload["non_claim_boundary"]

    for expected_bundle_member in (
        EXPECTED_WITNESS_REL,
        EXPECTED_WITNESS_GATE_REL,
        "formal/output/stat_der02_bounded_discharge_attempt_surface_v0.json",
        EXPECTED_GATE_REL,
    ):
        assert expected_bundle_member in payload["expected_new_artifacts_for_next_commit_bundle"]
        assert expected_bundle_member in payload["cross_surface_pointers"] or expected_bundle_member in (
            "formal/output/stat_der02_bounded_discharge_attempt_surface_v0.json",
        )