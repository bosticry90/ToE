from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_quadratic_gravity_viability_and_native_relevance_result_review_v0
    as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_freezes_execution() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_execution_artifacts"]
    } == review.EXECUTION_HASHES


def test_all_eighteen_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 18
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_metric_trace_and_mass_are_independently_reproduced() -> None:
    row = _report()["independent_reproduction"]["metric_and_trace"]
    assert row["algebraic_trace"] == "-R"
    assert row["Box_R_coefficient"] == "6*alpha"
    assert row["scalar_mass_squared"] == "-1/(6*alpha)"
    assert row["passed"] is True


def test_scalar_tensor_map_and_potential_mass_reproduce() -> None:
    row = _report()["independent_reproduction"]["scalar_tensor"]
    assert row["auxiliary_equation"] == "2*alpha*(R - chi)"
    assert row["Jordan_U"] == "(Phi - 1)**2/(4*alpha)"
    assert row["equivalence_domain"] == "alpha!=0"
    assert row["conformal_domain"] == "Phi>0"
    assert row["potential_mass_squared_at_minimum"] == "-1/(6*alpha)"
    assert row["passed"] is True


def test_sign_translation_reconciles_mass_and_f_rr() -> None:
    row = _report()["independent_reproduction"][
        "convention_and_matter_stability"
    ]
    assert row["f_RR_literature"] == "-2 alpha_packet"
    assert row["alpha_packet_negative_mass_squared"] == "1/(6*a)"
    assert row["alpha_packet_negative_f_RR_literature"] == "2*a"
    assert row["passed"] is True


def test_pure_vacuum_has_only_zero_constant_curvature() -> None:
    row = _report()["independent_reproduction"]["backgrounds"][
        "pure_vacuum_constant_curvature"
    ]
    assert row["equation"] == "-R0"
    assert row["only_root"] == "R0=0"
    assert row["passed"] is True


def test_supplied_background_passes_complete_tensor_equation() -> None:
    row = _report()["independent_reproduction"]["backgrounds"][
        "supplied_constant_density"
    ]
    assert row["full_tensor_lhs_coefficient"] == "-R0/4"
    assert row["solution"] == "R0=-4 kappa rho"
    assert row["Phi0"] == "-8*alpha*kappa*rho + 1"
    assert row["tensor_equation_residual"] == "0"
    assert row["trace_equation_residual"] == "0"
    assert row["passed"] is True


def test_source_conservation_and_fixed_trace_are_explicit() -> None:
    row = _report()["independent_reproduction"]["backgrounds"][
        "supplied_constant_density"
    ]
    assert row["stress_tensor"] == "T_mu_nu=rho g_mu_nu"
    assert row["trace"] == "T=4 rho"
    assert row["delta_T_for_fixed_rho"] == 0
    assert "metric compatibility" in row["conservation"]


def test_matter_stability_claim_remains_bounded() -> None:
    row = _report()["independent_reproduction"][
        "convention_and_matter_stability"
    ]
    assert "supplied-source curvature-mode" in row["qualification"]
    claim = _report()["accepted_bounded_claim"]
    assert claim["dynamical_matter_stability_claim"] is False


def test_traceless_and_screening_claims_remain_narrow() -> None:
    row = _report()["independent_reproduction"]["trace_and_screening"]
    assert row["exactly_traceless_classical_source"] == (
        "NO_DIRECT_LINEAR_SCALAR_EXCITATION"
    )
    assert row["principal_screening_finding"] == (
        "FINITE_MASS_SUPPRESSION_ONLY"
    )
    assert "anomalies" in row["qualification"]


def test_native_bridge_count_remains_zero() -> None:
    claim = _report()["accepted_bounded_claim"]
    posture = _report()["current_posture"]
    assert claim["native_bridge_count"] == posture["native_scalar_bridges"] == 0
    assert claim["native_relevance"] == "NOT_IDENTIFIED"


def test_scope_authorizes_only_response_selection() -> None:
    scope = _report()["scope"]
    assert scope["independent_result_review_executed"] is True
    assert scope["bounded_comparison_result_accepted"] is True
    assert scope["scientific_response_selection_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "independent_result_review_executed",
            "bounded_comparison_result_accepted",
            "scientific_response_selection_authorized",
        }:
            assert value is False, key


def test_post_reproduction_oracles_do_not_create_the_result() -> None:
    oracles = _report()["post_reproduction_oracles"]
    assert len(oracles) == 4
    assert all(row["role"].endswith("ORACLE") for row in oracles)


def test_human_review_records_full_tensor_bridge_and_stop_gates() -> None:
    text = (REPO_ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    for token in (
        review.VERDICT,
        "18 / 18 PASSED",
        "complete tensor equation",
        "f_RR_literature > 0",
        "FINITE_MASS_SUPPRESSION_ONLY",
        "Complete bridges remain",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
