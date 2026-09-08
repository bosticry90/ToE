from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from formal.python.tools import post_quadratic_gravity_comparison_conditional_mode_selection_packet_review_v0 as review


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH
PACKET_PATH = REPO_ROOT / review.PACKET_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _packet() -> dict[str, object]:
    value = json.loads(PACKET_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _selector(value: dict[str, object], selector_id: str) -> dict[str, object]:
    return next(
        row for row in value["selector_register"]["rows"]
        if row["selector_id"] == selector_id
    )


def test_review_regenerates_exactly_and_preserves_packet_custody() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    review.build_review()
    after = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    assert before == after == review.PACKET_HASHES


def test_review_accepts_packet_and_authorizes_one_execution_only() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND
    boundary = report["authorization_boundary"]
    assert boundary["one_bounded_envelope_execution_authorized"] is True
    assert boundary["additional_execution_authorized"] is False
    assert boundary["independent_result_review_required_after_execution"] is True


def test_baseline_packet_passes_independent_semantic_audit() -> None:
    audit = review.audit_packet(_packet())
    assert audit == {
        "selector_count": 10,
        "stratum_count": 9,
        "authority_class_count": 4,
        "positions_unselected": 3,
        "principal_outcome_empty": True,
        "condition_adoption_count": 0,
    }


def test_authority_audit_keeps_R9_R10_nonselecting_and_S3_supplied() -> None:
    audit = _report()["independent_authority_audit"]
    assert audit["R9"] == "PROJECT_BOUND_EVALUATION_ONLY_NO_PARAMETER_RESTRICTION"
    assert audit["R10"] == "PROJECT_BOUND_EVALUATION_ONLY_NO_ACCEPTANCE_THRESHOLD"
    assert audit["S3"] == "SUPPLIED_EXCLUDED_FROM_NATIVE_SELECTION"
    assert audit["hypothetical_postulate"] == "NOT_PROPOSED_NOT_AUTHORIZED_NOT_ADOPTED"
    assert audit["native_branch_selector_found_during_packet_review"] is False


def test_scalar_and_spin2_mass_signs_are_independently_reproduced() -> None:
    algebra = _report()["independent_conditional_algebra"]
    assert algebra["scalar_non_tachyonic_iff_Sigma_negative"] is True
    assert algebra["spin2_non_tachyonic_iff_beta_positive"] is True
    assert all(
        row["non_tachyonic"] == row["Sigma_negative"]
        for row in algebra["scalar_sign_samples"]
    )
    assert all(
        row["non_tachyonic"] == row["beta_positive"]
        for row in algebra["spin2_sign_samples"]
    )


def test_absent_mode_and_scalar_only_algebra_are_reproduced() -> None:
    algebra = _report()["independent_conditional_algebra"]
    assert algebra["beta_zero_and_Sigma_zero_imply_alpha_zero"] is True
    assert algebra["beta_zero_scalar_non_tachyonic_implies_alpha_negative"] is True


def test_coincident_mass_samples_all_agree_without_cancellation_claim() -> None:
    algebra = _report()["independent_conditional_algebra"]
    assert algebra["coincident_masses_equal"] is True
    assert all(row["m0_squared"] == row["m2_squared"] for row in algebra["coincident_samples"])
    coincident = _report()["coincident_mass_review"]
    assert coincident["P2_P0s_orthogonal"] is True
    assert coincident["pole_order"] == 1
    assert coincident["cancellation"] is False
    assert coincident["ghost_repaired"] is False


def test_exact_and_finite_precision_current_claims_are_disjoint() -> None:
    current = _report()["exact_empirical_review"]
    assert current["exact_generic_current_equality"] == "beta=0 within frozen family"
    assert current["finite_precision_agreement"] == (
        "bounds or suppresses correction; beta=0 not inferred"
    )
    assert current["dataset_imported"] is False
    assert current["metric_to_observable_transport_executed"] is False


def test_all_twelve_adversarial_controls_fail_closed_for_intended_reason() -> None:
    controls = _report()["adversarial_controls"]
    assert controls["control_count"] == controls["pass_count"] == 12
    assert controls["failure_count"] == 0
    assert all(row["passed"] for row in controls["rows"])
    assert all(
        row["observed_rejection"] == row["expected_rejection"]
        for row in controls["rows"]
    )


@pytest.mark.parametrize(
    ("selector_id", "field", "mutation", "expected"),
    [
        (
            "SEL_NO_NEGATIVE_RESIDUE_SPIN2",
            "authority_class",
            "PROJECT_BOUND_NATIVE_PRINCIPLE",
            "AUTHORITY_CLASS_MISMATCH",
        ),
        (
            "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY",
            "parameter_restriction",
            "beta=0",
            "R9_STRENGTHENED",
        ),
        (
            "SEL_NATIVE_R10_STABILITY_EVALUATION",
            "parameter_restriction",
            "beta=0",
            "R10_STRENGTHENED",
        ),
        (
            "SEL_FINITE_PRECISION_0I",
            "parameter_restriction",
            "beta=0",
            "EMPIRICAL_EXACT_IDENTITY",
        ),
        (
            "SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE",
            "condition_adopted",
            True,
            "CONDITION_PRESELECTED",
        ),
    ],
)
def test_direct_selector_mutations_are_rejected(
    selector_id: str, field: str, mutation: object, expected: str
) -> None:
    value = copy.deepcopy(_packet())
    _selector(value, selector_id)[field] = mutation
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_packet(value)
    assert captured.value.code == expected


def test_unknown_multiple_class_is_rejected() -> None:
    value = copy.deepcopy(_packet())
    _selector(value, "SEL_NO_TACHYONIC_POLES")["authority_class"] = [
        "PROJECT_BOUND_NATIVE_PRINCIPLE",
        "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    ]
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_packet(value)
    assert captured.value.code == "UNKNOWN_AUTHORITY_CLASS"


def test_coincident_mass_ghost_cancellation_is_rejected() -> None:
    value = copy.deepcopy(_packet())
    row = next(
        row for row in value["parameter_strata"]["rows"]
        if row["stratum_id"] == "COINCIDENT_MASSES"
    )
    row["qualification"] = "scalar cancels and repairs ghost"
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_packet(value)
    assert captured.value.code == "COINCIDENT_MASS_MISCLASSIFIED"


def test_position_preselection_and_scope_expansion_are_rejected() -> None:
    selected = copy.deepcopy(_packet())
    selected["logical_paths"][0]["selected_now"] = True
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_packet(selected)
    assert captured.value.code == "POSITION_PRESELECTED"

    expanded = copy.deepcopy(_packet())
    expanded["scope_firewall"]["outside_family_transport_allowed"] = True
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_packet(expanded)
    assert captured.value.code == "SCOPE_LEAK"


def test_premature_principal_outcome_is_rejected() -> None:
    value = copy.deepcopy(_packet())
    value["outcome_contract"]["principal_outcome_now"] = (
        "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE"
    )
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_packet(value)
    assert captured.value.code == "PREMATURE_OUTCOME"


def test_all_sixteen_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 16
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_review_scope_authorizes_execution_but_nothing_scientific_is_executed() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "independent_packet_review_executed",
        "packet_accepted",
        "one_bounded_envelope_execution_authorized",
    }
    assert all(scope[key] is True for key in allowed_true)
    for key, value in scope.items():
        if key not in allowed_true:
            assert value is False, key


def test_claim_ceiling_forbids_every_promotion_and_downstream_action() -> None:
    claim = _report()["claim_ceiling"]
    for token in (
        "No envelope result",
        "selector adoption",
        "native principle",
        "postulate",
        "coupling",
        "action",
        "external mechanism",
        "dataset",
        "empirical fit",
        "orbital transport",
        "frame-dragging result",
        "V2 cell",
    ):
        assert token in claim


def test_human_review_reports_acceptance_controls_and_exact_stop() -> None:
    text = (REPO_ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "16 / 16 PASSED",
        "12 / 12 PASSED",
        "R9_MOMENTUM_CURRENT",
        "R10_STABILITY_NO_FIT",
        "S3_NO_EXTRA_GRAVITATIONAL_MODES",
        "no double pole, cancellation, merger, or",
        "selector adjudications:         0 / 10",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
