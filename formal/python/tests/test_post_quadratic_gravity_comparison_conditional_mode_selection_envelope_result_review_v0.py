from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from formal.python.tools import (
    post_quadratic_gravity_comparison_conditional_mode_selection_envelope_result_review_v0 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH
EXECUTION_PATH = REPO_ROOT / review.EXECUTION_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _report() -> dict[str, object]:
    return _load(REPORT_PATH)


def _execution() -> dict[str, object]:
    return _load(EXECUTION_PATH)


def _row(value: dict[str, object], selector_id: str) -> dict[str, object]:
    return next(
        row for row in value["selector_adjudication"]["rows"]
        if row["selector_id"] == selector_id
    )


def test_review_regenerates_exactly_and_preserves_execution_custody() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in review.EXECUTION_HASHES}
    review.build_review()
    after = {path: _sha256(REPO_ROOT / path) for path in review.EXECUTION_HASHES}
    assert before == after == review.EXECUTION_HASHES


def test_result_is_accepted_and_rotates_only_to_response_selection() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND


def test_baseline_execution_passes_independent_audit() -> None:
    audit = review.audit_execution(_execution())
    assert audit["selector_count"] == audit["adjudicated_count"] == 10
    assert audit["adopted_count"] == 0
    assert audit["native_branch_selector_count"] == 0
    assert audit["open_position_count"] == 3
    assert audit["class_counts"] == {
        "PROJECT_BOUND_NATIVE_PRINCIPLE": 2,
        "SUPPLIED_STANDARD_PHYSICS_CRITERION": 6,
        "EMPIRICAL_CONSTRAINT": 1,
        "PROPOSED_NEW_POSTULATE": 1,
    }


def test_authority_reproduction_keeps_R9_R10_nonselecting_and_S3_supplied() -> None:
    authority = _report()["independent_authority_classification"]
    assert authority["R9"] == "PROJECT_BOUND_EVALUATION_ONLY_NO_PARAMETER_RESTRICTION"
    assert authority["R10"] == "PROJECT_BOUND_EVALUATION_ONLY_NO_ACCEPTANCE_THRESHOLD"
    assert authority["S3"] == "SUPPLIED_EXCLUDED_FROM_NATIVE_SELECTION"
    assert authority["native_branch_selector_count"] == 0


def test_all_exact_conditional_mappings_are_reproduced() -> None:
    execution = _execution()
    for selector_id, (authority_class, authority_binding, consequence) in review.EXPECTED_SELECTORS.items():
        row = _row(execution, selector_id)
        assert row["canonical_provenance"]["authority_class"] == authority_class
        assert row["canonical_provenance"]["authority_binding"] == authority_binding
        assert row["conditional_parameter_consequence"] == consequence


def test_mass_signs_and_einstein_limit_are_independently_reproduced() -> None:
    algebra = _report()["independent_conditional_algebra"]
    assert algebra["scalar_non_tachyonic_iff_Sigma_negative"] is True
    assert algebra["spin2_non_tachyonic_iff_beta_positive"] is True
    assert algebra["beta_zero_and_Sigma_zero_imply_alpha_zero"] is True
    assert all(row["non_tachyonic"] == row["Sigma_negative"] for row in algebra["scalar_sign_samples"])
    assert all(row["non_tachyonic"] == row["beta_positive"] for row in algebra["spin2_sign_samples"])


def test_exact_approximate_meanings_are_six_way_and_noninterchangeable() -> None:
    meanings = _report()["meaning_separation_review"]
    assert meanings["meaning_count"] == 6
    assert len(set(meanings["statuses"])) == 6
    assert meanings["interchange_allowed"] is False
    assert meanings["exact_generic_current_equality"] == "beta=0 within frozen family"
    assert meanings["finite_precision_agreement"] == "PARAMETER_BOUND_NOT_EXACT_IDENTITY"


def test_coincident_masses_remain_orthogonal_simple_channels() -> None:
    coincident = _report()["coincident_mass_review"]
    assert coincident["m0_squared"] == coincident["m2_squared"] == "1/beta"
    assert coincident["P2_P0s_orthogonal"] is True
    assert coincident["pole_order"] == 1
    assert coincident["cancellation"] is False
    assert coincident["ghost_repaired"] is False
    assert _report()["independent_conditional_algebra"]["coincident_masses_equal"] is True


def test_principal_result_is_exclusive_complete_and_nonadoptive() -> None:
    principal = _report()["principal_result_review"]
    assert principal["accepted_outcome"] == "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE"
    assert principal["outcome_count"] == 1
    assert principal["selector_classification_complete"] is True
    assert principal["conditional_consequences_complete"] is True
    assert principal["condition_adoption_count"] == 0
    assert principal["native_branch_selector_count"] == 0
    assert principal["open_position_count"] == 3
    assert principal["selected_position_count"] == 0


def test_all_fourteen_adversarial_controls_fail_closed() -> None:
    controls = _report()["adversarial_controls"]
    assert controls["control_count"] == controls["pass_count"] == 14
    assert controls["failure_count"] == 0
    assert all(row["passed"] for row in controls["rows"])
    assert all(row["observed_rejection"] == row["expected_rejection"] for row in controls["rows"])


@pytest.mark.parametrize(
    ("selector_id", "field", "mutation", "expected"),
    [
        ("SEL_NATIVE_R9_CURRENT_REPRESENTABILITY", "conditional_parameter_consequence", "beta=0", "R9_STRENGTHENED"),
        ("SEL_NATIVE_R10_STABILITY_EVALUATION", "conditional_parameter_consequence", "beta=0", "R10_STRENGTHENED"),
        ("SEL_FINITE_PRECISION_0I", "conditional_parameter_consequence", "beta=0", "EMPIRICAL_EXACT_IDENTITY"),
        ("SEL_NO_NEGATIVE_RESIDUE_SPIN2", "condition_adopted", True, "HIDDEN_ADOPTION"),
        ("SEL_MINIMAL_SPECTRUM", "native_branch_selection_authority", True, "HIDDEN_NATIVE_SELECTOR"),
    ],
)
def test_direct_selector_mutations_are_rejected(
    selector_id: str, field: str, mutation: object, expected: str
) -> None:
    value = copy.deepcopy(_execution())
    _row(value, selector_id)[field] = mutation
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_execution(value)
    assert captured.value.code == expected


def test_hidden_ranking_position_selection_and_scope_transport_are_rejected() -> None:
    ranked = copy.deepcopy(_execution())
    _row(ranked, "SEL_NO_NEGATIVE_RESIDUE_SPIN2")["preference_score"] = 1
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_execution(ranked)
    assert captured.value.code == "HIDDEN_RANKING"

    selected = copy.deepcopy(_execution())
    selected["position_map"]["rows"][0]["selected"] = True
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_execution(selected)
    assert captured.value.code == "POSITION_SELECTED"

    leaked = copy.deepcopy(_execution())
    leaked["scope_firewall"]["outside_family_transport_allowed"] = True
    with pytest.raises(review.ReviewFailure) as captured:
        review.audit_execution(leaked)
    assert captured.value.code == "SCOPE_LEAK"


def test_all_sixteen_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 16
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_accepts_result_and_authorizes_only_response_selection() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "independent_result_review_executed",
        "conditional_envelope_result_accepted",
        "scientific_response_selection_authorized",
    }
    assert all(scope[key] is True for key in allowed_true)
    for key, value in scope.items():
        if key not in allowed_true:
            assert value is False, key


def test_response_options_are_listed_but_none_is_selected() -> None:
    report = _report()
    assert len(report["response_selection_options"]) == 5
    assert report["scope"]["scientific_response_selection_executed"] is False
    assert report["scope"]["branch_selected"] is False


def test_claim_ceiling_and_human_review_preserve_exact_stop() -> None:
    report = _report()
    claim = report["claim_ceiling"]
    for token in (
        "No condition",
        "branch",
        "native principle",
        "postulate",
        "gravitational action",
        "outside-family mechanism",
        "dataset",
        "orbital transport",
        "frame-dragging result",
        "V2 cell",
    ):
        assert token in claim
    text = (REPO_ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "16 / 16 PASSED",
        "14 / 14 PASSED",
        "conditions adopted:               0",
        "native branch selectors:          0",
        "No hidden adoption or ranking",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
