from __future__ import annotations

import dataclasses
import hashlib
import json
from pathlib import Path

import pytest

from formal.python.tools import (
    native_gravitational_principle_requirements_and_action_selection_packet_v2 as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    assert packet.artifact_bytes() == packet.artifact_bytes() == REPORT_PATH.read_bytes()


def test_packet_preserves_every_frozen_v1_review_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    packet.build_packet()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == packet.AUTHORITY_AND_SOURCE_HASHES


def test_packet_consumes_v1_block_and_stops_for_v2_review() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["authority"]["v1_review_verdict"] == (
        "BLOCKED_REQUIREMENTS_ACTION_SELECTION_PRODUCTION_SEMANTICS_INCOMPLETE"
    )
    assert report["repair_contract"]["repair_count"] == 5
    assert report["repair_contract"]["final_automatically_authorized_repair_attempt"] is True
    assert report["repair_contract"]["automatic_v3_authorized"] is False


def test_bound_requirement_objects_are_internal_frozen_and_exact() -> None:
    assert tuple(packet.PROJECT_REQUIREMENT_CATALOG) == packet.PROJECT_REQUIREMENT_IDS
    assert len(packet.PROJECT_REQUIREMENT_CATALOG) == 10
    assert len(packet.SUPPLIED_REQUIREMENT_CATALOG) == 3
    row = packet.BOUND_REQUIREMENT_CATALOG["S3_NO_EXTRA_GRAVITATIONAL_MODES"]
    assert dataclasses.is_dataclass(row)
    assert row.statement_class == "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
    assert row.native_elimination_allowed is False
    assert row.native_distinctiveness_allowed is False
    with pytest.raises(dataclasses.FrozenInstanceError):
        row.statement_class = "PROJECT_BOUND_NATIVE_REQUIREMENT"  # type: ignore[misc]
    with pytest.raises(TypeError):
        packet.BOUND_REQUIREMENT_CATALOG["X"] = row  # type: ignore[index]


def test_public_input_rejects_caller_authored_decision_objects() -> None:
    value = packet._outcome_fixture("CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR")
    value["requirements"] = [{"requirement_id": "C_NATIVE"}]
    result = packet.evaluate_analysis(value)
    assert result["diagnostic"] == "CALLER_DECISION_BEARING_OBJECT_REJECTED"
    assert result["matrix_evaluated"] is False


def test_false_caller_statement_class_is_ignored_and_canonical_class_retained() -> None:
    controls = {
        row["control_id"]: row
        for row in packet.run_production_controls()["adversarial_controls"]
    }
    row = controls["ADV_FALSE_CALLER_STATEMENT_CLASS_IGNORED"]
    assert row["passed"] is True
    assert row["observed"] == "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
    assert row["construction_kind"] == "BASELINE_SINGLE_FIELD_MUTATION"
    assert row["changed_paths"] == ["$.caller_requirement_claims"]


def test_every_decision_bearing_cell_requires_exact_bound_evidence() -> None:
    report = _report()["evidence_bound_cell_contract"]
    assert set(report["decision_bearing_statuses_require_evidence"]) == (
        set(packet.MATRIX_CELL_VALUES) - {"NOT_EVALUATED"}
    )
    assert report["expected_outcome_is_evidence"] is False
    assert "expected" not in packet.EvidenceRecord.__dataclass_fields__

    value = packet._outcome_fixture("CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR")
    value["matrix"]["C_NATIVE"]["F_EH"]["evidence_id"] = (
        "CE_C_NATIVE_F_FR_SAT"
    )
    result = packet.evaluate_analysis(value)
    assert result["diagnostic"] == "EVIDENCE_CELL_BINDING_MISMATCH"
    assert result["matrix_evaluated"] is False


def test_satisfies_without_evidence_fails_closed_atomically() -> None:
    controls = {
        row["control_id"]: row
        for row in packet.run_production_controls()["adversarial_controls"]
    }
    row = controls["ADV_SATISFIES_WITHOUT_EVIDENCE"]
    assert row["passed"] is True
    assert row["observed"] == "EVIDENCE_ID_REQUIRED"
    assert row["changed_paths"] == ["$.matrix.C_NATIVE.F_EH.evidence_id"]


def test_equivalence_cell_without_included_validated_proof_fails_closed() -> None:
    controls = {
        row["control_id"]: row
        for row in packet.run_production_controls()["adversarial_controls"]
    }
    row = controls["ADV_EQUIVALENT_WITHOUT_VALIDATED_PROOF"]
    assert row["passed"] is True
    assert row["observed"] == "EQUIVALENCE_CELL_PROOF_MISSING"
    assert row["changed_paths"] == ["$.equivalence_proof_ids"]


def test_invalid_fr_to_eh_parameter_limit_proof_is_rejected() -> None:
    proof = packet.EQUIVALENCE_PROOF_CATALOG[
        "CP_INVALID_FR_EH_PARAMETER_LIMIT"
    ]
    assert proof.family_a == "F_FR"
    assert proof.family_b == "F_EH"
    assert proof.validation_status == "REJECTED"
    assert proof.equivalence_type not in packet.ALLOWED_EQUIVALENCE_TYPES
    assert set(proof.forbidden_changes).intersection(
        packet.FORBIDDEN_EQUIVALENCE_CHANGES
    )
    controls = {
        row["control_id"]: row
        for row in packet.run_production_controls()["adversarial_controls"]
    }
    assert controls["ADV_INVALID_FR_TO_EH_PROOF_REJECTED"]["observed"] == (
        "EQUIVALENCE_PROOF_REJECTED"
    )
    assert controls["ADV_INVALID_FR_TO_EH_PROOF_REJECTED"]["passed"] is True


def test_fr_to_eh_pair_is_rejected_even_with_forged_allowed_type_label() -> None:
    sat = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    value = packet._fixture(
        ["C_NATIVE"],
        ["F_EH", "F_FR"],
        {"C_NATIVE": {"F_EH": sat, "F_FR": sat}},
        equivalence_proof_ids=["CP_FORGED_FR_EH_ALGEBRAIC_IDENTITY"],
    )
    result = packet.evaluate_analysis(value)
    assert result["diagnostic"] == "FORBIDDEN_FAMILY_EQUIVALENCE_PAIR"
    assert result["matrix_evaluated"] is False


def test_local_bulk_proof_does_not_erase_global_property_uncertainty() -> None:
    controls = {
        row["control_id"]: row
        for row in packet.run_production_controls()["adversarial_controls"]
    }
    row = controls["ADV_UNDECIDABLE_CLASS_WITHOUT_PROPERTY_TRANSPORT"]
    assert row["passed"] is True
    assert row["observed"] == "EQUIVALENCE_CLASS_STATUS_UNRESOLVED"

    proof = packet.EQUIVALENCE_PROOF_CATALOG["CP_EH_BOUNDARY_LOCAL_BULK"]
    assert "LOCAL_BULK_EQUATIONS" in proof.preserved_property_keys
    assert "GLOBAL_STABILITY" in proof.nonpreserved_property_keys
    assert "GLOBAL_STABILITY" not in proof.preserved_property_keys


def test_exact_property_transport_can_resolve_only_the_covered_property() -> None:
    sat = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    undec = "NOT_DECIDABLE_FROM_REQUIREMENT"
    value = packet._fixture(
        ["C_LOCAL_BULK"],
        ["F_EH", "F_EH_BOUNDARY"],
        {"C_LOCAL_BULK": {"F_EH": sat, "F_EH_BOUNDARY": undec}},
        equivalence_proof_ids=["CP_EH_BOUNDARY_LOCAL_BULK"],
    )
    result = packet.evaluate_analysis(value)
    row = result["summary"]["class_requirement_statuses"][0]
    assert row["property_key"] == "LOCAL_BULK_EQUATIONS"
    assert row["property_transport_proved"] is True
    assert row["class_status"] == (
        "CLASS_SATISFIES_VIA_EXACT_PROPERTY_TRANSPORT"
    )
    assert result["scientific_outcome"] == (
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
    )


def test_standard_gr_oracle_cannot_supply_native_cell_evidence() -> None:
    controls = {
        row["control_id"]: row
        for row in packet.run_production_controls()["adversarial_controls"]
    }
    row = controls["ADV_STANDARD_GR_ORACLE_AS_NATIVE_EVIDENCE"]
    assert row["passed"] is True
    assert row["observed"] == "STANDARD_GR_ORACLE_NATIVE_EVIDENCE"
    assert row["changed_paths"] == ["$.matrix.C_NATIVE.F_EH.evidence_id"]


def test_all_six_outcomes_are_reachable_exclusive_and_shared_path() -> None:
    execution = packet.run_production_controls()
    outcomes = execution["outcome_controls"]
    assert outcomes["outcome_control_count"] == 6
    assert outcomes["outcome_control_pass_count"] == 6
    assert outcomes["all_six_outcomes_reached"] is True
    assert {row["observed"] for row in outcomes["rows"]} == set(
        packet.SCIENTIFIC_OUTCOMES
    )
    assert all(row["matching_scientific_outcome_count"] == 1 for row in outcomes["rows"])
    assert all(
        row["entry_point_id"] == packet.PRODUCTION_ENTRY_POINT_ID
        for row in outcomes["rows"]
    )


def test_no_go_is_viable_consistent_and_distinct_from_inconsistency() -> None:
    no_go = packet.evaluate_analysis(packet._outcome_fixture(
        "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS"
    ))
    inconsistent = packet.evaluate_analysis(packet._outcome_fixture(
        "REQUIREMENT_SET_INCONSISTENT"
    ))
    assert no_go["scientific_outcome"] == (
        "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS"
    )
    assert no_go["summary"]["affirmative_equivalence_classes"] == ["F_EH"]
    assert inconsistent["scientific_outcome"] == "REQUIREMENT_SET_INCONSISTENT"
    assert inconsistent["summary"]["affirmative_equivalence_classes"] == []
    assert inconsistent["summary"]["unresolved_equivalence_classes"] == []
    no_go_evidence = packet.TERMINAL_EVIDENCE_CATALOG["TE_NO_GO"]
    assert no_go_evidence.requirements_internally_consistent is True
    assert no_go_evidence.ordinary_viable_gravity_exists is True
    assert no_go_evidence.distinctive_native_gravity_in_envelope_exists is False


def test_retained_boundary_adversarial_and_outcome_controls_share_one_path() -> None:
    execution = _report()["control_execution"]
    assert execution["retained_control_count"] == (
        execution["retained_control_pass_count"]
    ) == 8
    assert execution["boundary_probe_count"] == (
        execution["boundary_probe_pass_count"]
    ) == 2
    assert execution["adversarial_control_count"] == (
        execution["adversarial_control_pass_count"]
    ) == 6
    assert execution["outcome_controls"]["outcome_control_count"] == (
        execution["outcome_controls"]["outcome_control_pass_count"]
    ) == 6
    assert execution["all_used_shared_entry_point"] is True
    assert execution["all_declared_single_field_mutations_atomic"] is True


def test_project_profile_requires_exact_frozen_ten_by_seven_identity() -> None:
    result = packet.evaluate_analysis({
        "analysis_profile": packet.PROJECT_PROFILE,
        "mode": "NATIVE_ONLY",
        "requirement_ids": list(packet.PROJECT_REQUIREMENT_IDS[:-1]),
        "family_ids": list(packet.PROJECT_FAMILY_IDS),
        "matrix": {},
        "equivalence_proof_ids": [],
        "terminal_evidence_ids": [],
    })
    assert result["diagnostic"] == "PROJECT_REQUIREMENT_INVENTORY_MISMATCH"
    assert result["matrix_evaluated"] is False


def test_exact_project_profile_requires_separate_custody_validated_provider() -> None:
    result = packet.evaluate_analysis({
        "analysis_profile": packet.PROJECT_PROFILE,
        "mode": "NATIVE_ONLY",
        "requirement_ids": list(packet.PROJECT_REQUIREMENT_IDS),
        "family_ids": list(packet.PROJECT_FAMILY_IDS),
        "matrix": {},
        "equivalence_proof_ids": [],
        "terminal_evidence_ids": [],
    })
    assert result["diagnostic"] == "PROJECT_EVIDENCE_PROVIDER_REQUIRED"
    assert result["matrix_evaluated"] is False


def test_project_provider_manifest_must_bind_catalog_not_just_have_matching_hash() -> None:
    packet_path = REPO_ROOT / packet.PACKET_RELATIVE_PATH
    empty_catalog_hash = packet._catalog_sha256((), (), ())
    provider = packet.AnalysisCatalogProvider(
        provider_id="FORGED_PROJECT_PROVIDER",
        profile_id=packet.PROJECT_PROFILE,
        validation_status="CUSTODY_VALIDATED_PROJECT_PROVIDER",
        custody_manifest_relative_path=packet.PACKET_RELATIVE_PATH,
        custody_manifest_sha256=_sha256(packet_path),
        catalog_sha256=empty_catalog_hash,
        evidence_records=(),
        equivalence_proofs=(),
        terminal_evidence_records=(),
    )
    result = packet.evaluate_analysis({
        "analysis_profile": packet.PROJECT_PROFILE,
        "mode": "NATIVE_ONLY",
        "requirement_ids": list(packet.PROJECT_REQUIREMENT_IDS),
        "family_ids": list(packet.PROJECT_FAMILY_IDS),
        "matrix": {},
        "equivalence_proof_ids": [],
        "terminal_evidence_ids": [],
    }, catalog_provider=provider)
    assert result["diagnostic"] == "PROJECT_PROVIDER_CUSTODY_MANIFEST_INVALID"
    assert result["matrix_evaluated"] is False


def test_real_matrix_family_judgments_and_downstream_physics_remain_absent() -> None:
    report = _report()
    boundary = report["real_analysis_boundary"]
    assert boundary["real_matrix_cell_count"] == 70
    assert boundary["real_matrix_cells_supplied"] == 0
    assert boundary["real_matrix_evidence_records_supplied"] == 0
    assert boundary["real_survivor_set"] == "NOT_COMPUTED"
    assert boundary["real_scientific_outcome"] == "NOT_SELECTED"
    scope = report["scope"]
    assert scope["v2_contract_repair_prepared"] is True
    assert scope["synthetic_controls_executed"] is True
    assert scope["real_matrix_cells_computed"] == 0
    for key, value in scope.items():
        if key not in {
            "v2_contract_repair_prepared",
            "synthetic_controls_executed",
            "real_matrix_cells_computed",
        }:
            assert value is False, key


def test_anti_rabbit_hole_boundary_forbids_automatic_v3() -> None:
    boundary = _report()["anti_rabbit_hole_boundary"]
    assert boundary["v2_is_final_automatically_authorized_repair_attempt"] is True
    assert boundary["automatic_v3_authorized"] is False
    assert boundary["if_v2_foundational_review_failure"] == [
        "CLOSE_AUTOMATED_ACTION_SELECTION_TOOLING_LANE",
        "CONDUCT_SMALLER_MANUALLY_ADJUDICATED_REQUIREMENTS_ANALYSIS",
        "RETURN_TO_FULL_SCIENTIFIC_PRIORITY_MAP",
    ]


def test_human_packet_records_five_repairs_controls_freeze_and_stopping_rule() -> None:
    text = (REPO_ROOT / packet.PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "BoundRequirement",
        "evidence_id",
        "CP_INVALID_FR_EH_PARAMETER_LIMIT",
        "EQUIVALENCE_CLASS_STATUS_UNRESOLVED",
        "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS",
        "8 / 8",
        "6 / 6",
        "0 / 70",
        "automatic V3",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
