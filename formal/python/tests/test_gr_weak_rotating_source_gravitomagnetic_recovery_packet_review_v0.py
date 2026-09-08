from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    gr_weak_rotating_source_gravitomagnetic_recovery_packet_review_v0 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    first = review.artifact_bytes()
    second = review.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_packet_authority_and_source_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_SOURCE_HASHES
    }
    review.build_review()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == review.AUTHORITY_AND_SOURCE_HASHES


def test_review_consumes_packet_and_blocks_at_exact_primary_diagnostic() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT == (
        "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE"
    )
    assert report["primary_diagnostic"] == review.PRIMARY_DIAGNOSTIC == (
        "FIELD_EQUATION_SURFACE_FAILURE"
    )
    assert report["authority"]["consumed_packet_verdict"] == (
        "PREPARED_PENDING_INDEPENDENT_REVIEW"
    )


def test_fail_fast_gate_finds_no_authorized_continuum_tensor_equation() -> None:
    gate = _report()["fail_fast_gate"]
    assert gate["answer"] is False
    assert gate["required_object_present"] is False
    assert gate["fail_fast_applied"] is True
    assert gate["diagnostic"] == "FIELD_EQUATION_SURFACE_FAILURE"
    assert gate["derivation_authorized"] is False


def test_all_three_bound_project_surfaces_reproduce_but_do_not_supply_tensor_equation() -> None:
    rows = _report()["exact_binding_review"]
    assert len(rows) == 3
    assert all(row["binding_reproduced"] for row in rows)
    assert all(not row["continuum_metric_tensor_equation_derived"] for row in rows)
    assert {row["binding_id"] for row in rows} == {
        "GR_PROJECT_ACTION_REP32_SCAFFOLD",
        "GR_PROJECT_BOUNDED_DISCRETE_WEAK_FIELD_POISSON",
        "GR_PROJECT_DISCHARGE_BOUNDARY",
    }


def test_provisional_einstein_scalar_route_is_not_misclassified_as_project_derivation() -> None:
    alternative = _report()["alternative_surface_audit"]
    assert alternative["authorized_project_derived_continuum_tensor_surface_found"] is False
    provisional = alternative["provisional_einstein_scalar_route"]
    assert provisional == {
        "equation_recorded": True,
        "classification": "SUPPLIED_STANDARD_GR_PROVISIONAL_CLASSICAL_SANDBOX",
        "toe_native_gravitational_equation_derived": False,
        "coupled_solution_constructed": False,
        "eligible_to_discharge_gate": False,
    }
    target_map = alternative["full_gr_target_map"]
    assert target_map["status"] == "LOCAL_DONE_PILLAR_TARGET_OPEN"
    assert target_map["retained_blocker"] == (
        "gr01_continuum_limit_source_identification_retained"
    )


def test_stage_one_fails_and_stages_two_through_seven_are_not_evaluated() -> None:
    adjudication = _report()["stage_adjudication"]
    assert adjudication["stage_count"] == len(adjudication["rows"]) == 7
    assert adjudication["failed_count"] == 1
    assert adjudication["not_evaluated_count"] == 6
    first, *downstream = adjudication["rows"]
    assert first["stage"] == 1
    assert first["status"] == "FAILED"
    assert first["diagnostic"] == "FIELD_EQUATION_SURFACE_FAILURE"
    assert all(row["status"] == "NOT_EVALUATED" for row in downstream)
    assert all(row["diagnostic"] == "UPSTREAM_FAIL_FAST" for row in downstream)


def test_packet_conventions_and_oracles_remain_retained_without_execution() -> None:
    retained = _report()["retained_packet_policy_without_execution"]
    assert retained == {
        "coordinate_signature_si_policy_reproduced": True,
        "source_gauge_boundary_contract_reproduced": True,
        "standard_gr_oracles_remain_comparison_only": True,
        "coefficient_fitting_remains_forbidden": True,
        "planned_control_count": 8,
        "controls_executed": 0,
        "controls_adjudicated": False,
        "downstream_sign_coefficient_and_orbital_checks_adjudicated": False,
    }


def test_review_does_not_refute_standard_gr_or_claim_project_recovery() -> None:
    interpretation = _report()["scientific_interpretation"]
    assert interpretation["standard_GR_refuted"] is False
    assert interpretation["standard_Lense_Thirring_result_refuted"] is False
    assert interpretation["project_GR_recovery_established"] is False
    assert "does not provide the continuum tensor" in interpretation["finding"]


def test_two_future_routes_require_fresh_priority_selection_and_are_not_authorized() -> None:
    routes = _report()["future_options_requiring_fresh_priority_selection"]
    assert {row["route_id"] for row in routes} == {
        "PROJECT_GR_TENSOR_SURFACE_ROUTE",
        "STANDARD_GR_COMPARATOR_ROUTE",
    }
    assert all(row["authorized_now"] is False for row in routes)
    assert _report()["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert _report()["selected_next_target_kind"] == (
        "FULL_PRIORITY_RESPONSE_SELECTION_ONLY"
    )


def test_review_executes_no_calculation_control_empirics_or_promotion() -> None:
    scope = _report()["scope"]
    assert scope["independent_packet_review_executed"] is True
    for key, value in scope.items():
        if key != "independent_packet_review_executed":
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "FIELD_EQUATION_SURFACE_FAILURE",
        "No standard-GR refutation",
        "pillar completion",
        "seam closure",
        "master-action promotion",
    ):
        assert token in claim

