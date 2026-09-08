from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_physical_spin2_principal_block as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_physical_spin2_principal_block_result_review as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_calculation_and_review_artifacts_are_current() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_quadratic_spin2_pencil_has_defective_light_cone_roots() -> None:
    result = calculation.analyze_pencil()
    assert result["determinant"] == (
        "beta**2*(lambda - 1)**4*(lambda + 1)**4"
    )
    assert result["roots"] == [
        {
            "lambda": -1,
            "algebraic_multiplicity": 4,
            "geometric_multiplicity": 2,
            "complete_at_root": False,
        },
        {
            "lambda": 1,
            "algebraic_multiplicity": 4,
            "geometric_multiplicity": 2,
            "complete_at_root": False,
        },
    ]
    assert result["all_characteristic_roots_real"] is True
    assert result["strongly_hyperbolic_physical_block"] is False
    assert result["symmetrically_hyperbolic_physical_block"] is False


def test_unrepeated_wave_control_has_complete_roots() -> None:
    result = calculation.analyze_pencil(repeated_wave_power=1)
    assert result["roots"][0]["algebraic_multiplicity"] == 2
    assert result["roots"][0]["geometric_multiplicity"] == 2
    assert result["complete_eigenbasis"] is True
    assert result["strongly_hyperbolic_physical_block"] is True


def test_beta_zero_removes_the_tested_block() -> None:
    result = calculation.analyze_pencil(beta_nonzero=False)
    assert result == {
        "block_present": False,
        "reason": "beta=0 removes the fourth-order physical spin-2 block",
    }


def test_scalar_and_einstein_connection_controls_are_not_escape_routes() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    controls = artifact["coefficient_controls"]
    assert controls["3alpha_plus_beta_eq_0"]["spin2_obstruction_remains"] is True
    assert controls["c_R_eq_0"][
        "spin2_obstruction_remains_when_beta_nonzero"
    ] is True
    assert controls["alpha_eq_beta_eq_0"][
        "light_cone_algebraic_multiplicity"
    ] == controls["alpha_eq_beta_eq_0"][
        "light_cone_geometric_multiplicity"
    ]


def test_review_accepts_phase_a_without_claiming_adapted_norm_result() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["accepted_results"] == [
        "GENERIC_STRONG_HYPERBOLICITY_REFUTED",
        "PHYSICAL_SPIN2_REPEATED_ROOT_DEFECT_IDENTIFIED",
    ]
    assert "ADAPTED_NORM_LOCAL_WELL_POSEDNESS_ESTABLISHED" in artifact[
        "not_established"
    ]
    assert artifact["authority_rotation"]["phase_b_c_execution_authorized"] is False
    assert artifact["authority_rotation"][
        "preserved_descendant_adoption_authorized"
    ] is False
    assert all(review.build_review()["checks"].values())
