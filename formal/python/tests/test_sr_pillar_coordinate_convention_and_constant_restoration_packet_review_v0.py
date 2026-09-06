from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v0 as review_v0,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review_v0.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _review() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    first = review_v0.artifact_bytes()
    second = review_v0.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_v0_input_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path) for path in review_v0.FROZEN_INPUT_HASHES
    }
    review_v0.build_review()
    after = {
        path: _sha256(REPO_ROOT / path) for path in review_v0.FROZEN_INPUT_HASHES
    }
    assert before == after == review_v0.FROZEN_INPUT_HASHES


def test_review_consumes_exact_authority_and_blocks_acceptance() -> None:
    review = _review()
    assert review["target"] == review_v0.CONSUMED_TARGET
    assert review["verdict"] == review_v0.VERDICT
    assert review["first_diagnostic"] == review_v0.FIRST_DIAGNOSTIC
    assert review["selected_next_target"] == review_v0.SELECTED_NEXT_TARGET
    assert review["hard_stop"]["packet_accepted"] is False


def test_base_coordinate_signature_and_si_policy_are_retained() -> None:
    retained = _review()["retained_findings"]
    assert retained["temporal_coordinate"] == "x^0 = c t"
    assert retained["metric_signature"] == "(+,-,-,-)"
    assert retained["restoration_target"] == "SI"
    assert retained["partial_0_equals_c_inverse_partial_t"] is True
    assert retained["p_0_component_policy"] == "p^0 = E/c"
    assert retained["J_0_component_policy"] == "J^0 = c rho"


def test_independent_dimension_audit_reproduces_all_six_checks() -> None:
    audit = _review()["retained_findings"]["dimension_audit"]
    assert audit["method"].startswith("independent M,L,T,Q")
    assert audit["base_vectors_match_independent_expectations"] is True
    assert audit["check_count"] == 6
    assert audit["passed_check_count"] == 6
    assert len(audit["checks"]) == 6
    assert all(row["passed"] for row in audit["checks"])


def test_independent_em_scaling_audit_reproduces_the_declared_algebra() -> None:
    audit = _review()["retained_findings"]["electromagnetic_scaling_audit"]
    assert audit["exact_declared_object_map_reproduced"] is True
    assert audit["sourced_maxwell_mu0_exponent"]["passed"] is True
    assert audit["exchange_product_mu0_exponent"]["passed"] is True
    assert audit["gauge_stress_mu0_exponent"]["passed"] is True


def test_exact_seven_blocking_findings_are_recorded() -> None:
    blocked = _review()["blocking_findings"]
    assert blocked["count"] == 7
    assert blocked["all_confirmed"] is True
    ids = [row["finding_id"] for row in blocked["findings"]]
    assert ids == [
        "F_TENSOR_COMPONENT_AND_LEVI_CIVITA_CONVENTION_UNSPECIFIED",
        "QUANTUM_GAUGE_HBAR_AND_CURRENT_NORMALIZATION_UNSPECIFIED",
        "BIDIRECTIONAL_EQUATION_ROUND_TRIPS_NOT_EXECUTED",
        "NEGATIVE_CONTROLS_DECLARED_NOT_EXECUTED_AND_INCOMPLETE",
        "STRESS_ENERGY_COMPONENT_SEMANTICS_INCOMPLETE",
        "REPRESENTATIVE_EQUATION_SOURCE_BINDINGS_INCOMPLETE",
        "FLAT_CURVED_DERIVATIVE_ADAPTER_UNSPECIFIED",
    ]


def test_quantum_and_tensor_convention_defects_are_first_class_blocks() -> None:
    findings = {
        row["finding_id"]: row for row in _review()["blocking_findings"]["findings"]
    }
    tensor = findings["F_TENSOR_COMPONENT_AND_LEVI_CIVITA_CONVENTION_UNSPECIFIED"]
    assert "F^{0i}/F^{ij}" in tensor["evidence"]
    assert "Levi-Civita" in tensor["evidence"]
    quantum = findings["QUANTUM_GAUGE_HBAR_AND_CURRENT_NORMALIZATION_UNSPECIFIED"]
    assert "dimensionful Dirac equation" in quantum["evidence"]
    assert "J=q psibar gamma psi" in quantum["evidence"]


def test_round_trips_and_negative_controls_are_not_misreported_as_executed() -> None:
    findings = {
        row["finding_id"]: row for row in _review()["blocking_findings"]["findings"]
    }
    assert findings["BIDIRECTIONAL_EQUATION_ROUND_TRIPS_NOT_EXECUTED"][
        "confirmed"
    ] is True
    negative = findings["NEGATIVE_CONTROLS_DECLARED_NOT_EXECUTED_AND_INCOMPLETE"]
    assert negative["required_missing_controls"] == [
        "REJECT_p0_EQUALS_E_INSTEAD_OF_E_OVER_c",
        "REJECT_DIMENSIONFUL_GAUGE_DERIVATIVE_WITHOUT_hbar",
        "REJECT_T0i_WITH_INCORRECT_COMPONENT_DIMENSION_OR_MEANING",
    ]


def test_v1_contract_is_bounded_and_contains_all_required_repairs() -> None:
    review = _review()
    contract = review["v1_contract"]
    assert len(contract) == 9
    joined = "\n".join(contract)
    for token in (
        "F^{0i}",
        "Levi-Civita",
        "hbar",
        "mass-shell",
        "flat partial_mu versus curved nabla_mu",
        "SI-to-natural-to-SI",
        "observed diagnostics",
        "p^0=E",
        "T^{ij}",
        "R13 closure",
    ):
        assert token in joined
    assert review["selected_next_target"].endswith("_packet_v1")


def test_review_authorizes_no_application_migration_or_automation() -> None:
    scope = _review()["scope_and_authorization"]
    assert scope == {
        "packet_v0_accepted": False,
        "six_surface_application_authorized": False,
        "scientific_equation_migration_executed": False,
        "historical_artifacts_modified": False,
        "repository_wide_migration_authorized": False,
        "r13_reopened": False,
        "external_comparator_activated": False,
        "automation_created": False,
        "only_bounded_v1_packet_preparation_authorized": True,
    }


def test_claim_ceiling_does_not_promote_sr_or_any_seam() -> None:
    ceiling = _review()["claim_ceiling"]
    assert "no SR recovery" in ceiling
    assert "pillar completion" in ceiling
    assert "seam closure" in ceiling
    assert "R13 result" in ceiling
