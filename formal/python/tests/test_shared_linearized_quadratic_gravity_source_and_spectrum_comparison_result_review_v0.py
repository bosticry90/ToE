from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    shared_linearized_quadratic_gravity_source_and_spectrum_comparison_result_review_v0 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_freezes_execution() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {row["relative_path"]: row["sha256"] for row in report["authority"]["frozen_execution_artifacts"]} == review.EXECUTION_HASHES


def test_all_sixteen_scientific_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 16
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_independent_quadratic_variations_reproduce_trace() -> None:
    trace = _report()["independent_reproduction"]["exact_variation_trace"]
    assert trace["R2_algebraic_trace"] == 0
    assert trace["R2_Box_R_coefficient"] == 6
    assert trace["Ricci2_curvature_square_trace"] == 0
    assert trace["Ricci2_Box_R_coefficient"] == 2
    assert trace["combined_trace"] == "-R+2(3 alpha+beta)Box R=kappa T"
    assert trace["passed"] is True


def test_linearized_ricci_squared_identity_and_source_normalization() -> None:
    reproduction = _report()["independent_reproduction"]
    identity = reproduction["linearized_ricci_squared_identity"]
    assert identity["direct"].startswith("Box R^L_mu_nu")
    assert identity["decomposed"].startswith("Box G^L_mu_nu")
    assert identity["passed"] is True
    source = reproduction["source_normalization"]
    assert source["sign"] == "POSITIVE"
    assert source["coefficient"] == "8 pi G/c^4"


def test_background_gate_is_independently_reproduced() -> None:
    background = _report()["independent_reproduction"]["background"]
    assert background["source"] == background["curvature"] == 0
    assert background["Euler_tensor"] == background["linear_tadpole"] == 0
    assert background["passed"] is True


def test_projector_scalar_block_multiplies_to_identity() -> None:
    block = _report()["independent_reproduction"]["projector_scalar_block"]
    assert block["determinant"] == "-(k^4/4)(1+2 Sigma k^2)"
    assert block["product_polynomials"] == {
        "00": ["1", "2"],
        "01": ["0", "0"],
        "10": ["0", "0"],
        "11": ["1", "2"],
    }
    assert block["passed"] is True


def test_physical_eigenvalues_and_partial_fractions_reproduce() -> None:
    reproduction = _report()["independent_reproduction"]
    assert reproduction["physical_eigenvalues"] == {
        "spin_2": "-(k^2/2)(1-beta k^2)",
        "scalar": "k^2(1+2 Sigma k^2)",
        "passed": True,
    }
    assert reproduction["partial_fraction_identities"]["passed"] is True
    assert "-1/(2k^2)" in reproduction["partial_fraction_identities"]["scalar"]


def test_point_source_coefficients_reproduce() -> None:
    reproduction = _report()["independent_reproduction"]
    assert reproduction["point_source_coefficients"] == {
        "massless": "1",
        "scalar": "1/3",
        "massive_spin_2": "-4/3",
    }
    assert reproduction["point_source_passed"] is True


def test_stationary_scalar_current_decoupling_and_sign_reproduce() -> None:
    current = _report()["independent_reproduction"]["stationary_current"]
    assert current["theta_0i"] == 0
    assert current["P0s_0i_contraction"] == 0
    assert current["P2_0i_contraction_on_conserved_source"] == 1
    assert current["position_space_kernel"] == "-2 kappa(K0-Km2)T_0i"
    assert current["passed"] is True


def test_coincident_mass_is_simple_and_projector_resolved() -> None:
    coincident = _report()["independent_reproduction"]["coincident_mass"]
    assert coincident["Sigma"] == "-beta/2"
    assert coincident["m0_squared"] == coincident["m2_squared"] == "1/beta"
    assert coincident["pole_order"] == 1
    assert coincident["P2_P0s_product"] == 0
    assert coincident["higher_order_pole_present"] is False
    assert coincident["channel_diagonalizable"] is True
    assert coincident["passed"] is True


def test_accepted_claim_is_exactly_bounded() -> None:
    claim = _report()["accepted_bounded_claim"]
    assert claim["domain"] == "4D_LOCAL_METRIC_MINKOWSKI_CONSERVED_EXTERNAL_SOURCE"
    assert "m0^2=-1/[2(3 alpha+beta)]" in claim["massive_scalar"]
    assert "m2^2=1/beta" in claim["massive_spin_2"]
    assert claim["stationary_0i"].endswith("SCALAR_ZERO")
    assert claim["arbitrary_background_or_nonlinear_claim"] is False


def test_oracles_are_post_reproduction_only() -> None:
    oracles = _report()["post_reproduction_oracles"]
    assert len(oracles) == 3
    assert all(row["role"].endswith("ORACLE") for row in oracles)


def test_scope_authorizes_only_scientific_response_selection() -> None:
    scope = _report()["scope"]
    assert scope["independent_result_review_executed"] is True
    assert scope["comparison_result_accepted"] is True
    assert scope["scientific_response_selection_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "independent_result_review_executed",
            "comparison_result_accepted",
            "scientific_response_selection_authorized",
        }:
            assert value is False, key


def test_posture_preserves_comparison_only_status() -> None:
    posture = _report()["current_posture"]
    assert posture["comparison_execution"] == "COMPLETED_ONCE"
    assert posture["comparison_result"] == "ACCEPTED_16_OF_16_GATES"
    assert posture["comparison_action"] == "SUPPLIED_COMPARISON_ONLY"
    assert posture["native_gravitational_action"] == "NOT_SELECTED"
    assert posture["native_gravitational_principle"] == "NOT_IDENTIFIED"
    assert posture["frame_dragging"] == "NOT_RESUMED"


def test_human_review_records_reproduction_coincident_audit_and_stop() -> None:
    text = (REPO_ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "16 / 16 PASSED",
        "Independent field-equation reproduction",
        "Ricci-squared contribution",
        "Coincident-mass audit",
        "There is no $(k^2-m^2)^{-2}$ term",
        "scalar-current decoupling",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
