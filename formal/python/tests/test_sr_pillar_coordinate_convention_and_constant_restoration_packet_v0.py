from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_v0 as packet_v0,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet_v0.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _packet() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    first = packet_v0.artifact_bytes()
    second = packet_v0.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_build_is_read_only_over_all_bound_sources() -> None:
    before = {
        path: _sha256(REPO_ROOT / path) for path in packet_v0.SOURCE_HASHES
    }
    packet_v0.build_packet()
    after = {path: _sha256(REPO_ROOT / path) for path in packet_v0.SOURCE_HASHES}
    assert before == after == packet_v0.SOURCE_HASHES


def test_packet_consumes_exact_post_r13_target_and_stops_at_review() -> None:
    packet = _packet()
    assert packet["target"] == packet_v0.TARGET
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == packet_v0.SELECTED_NEXT_TARGET
    authority = packet["authority"]
    assert isinstance(authority, dict)
    assert authority["selected_pillar_code"] == "SR"
    assert authority["selected_weighted_score"] == 51
    assert authority["selected_route"] == "CONVENTION_AND_CONSTANT_RESTORATION"


def test_single_coordinate_signature_and_restoration_system_are_selected() -> None:
    packet = _packet()
    conventions = packet["selected_conventions"]
    assert isinstance(conventions, dict)
    assert conventions["temporal_coordinate"] == "x^0 = c t"
    assert conventions["metric_signature"] == "(+,-,-,-)"
    assert conventions["flat_metric"] == "eta_mu_nu = diag(+1,-1,-1,-1)"
    assert conventions["coordinate_dimension"] == "L for every component"
    assert conventions["covariant_derivative_components"] == (
        "partial_mu = (c^-1 partial_t, nabla)"
    )
    unit_policy = packet["unit_policy"]
    assert isinstance(unit_policy, dict)
    assert unit_policy["restored_target_system"] == "SI"
    assert packet["scope"]["multiple_metric_conventions_supported"] is False
    assert packet["scope"]["multiple_restoration_unit_systems_supported"] is False


def test_core_dimension_table_is_explicit_in_m_l_t_q_basis() -> None:
    packet = _packet()
    assert packet["unit_policy"]["dimension_vector_basis"] == ["M", "L", "T", "Q"]
    dimensions = packet["dimension_table"]
    assert isinstance(dimensions, dict)
    assert dimensions["coordinate_x_mu"] == [0, 1, 0, 0]
    assert dimensions["coordinate_derivative_partial_mu"] == [0, -1, 0, 0]
    assert dimensions["four_velocity_u_mu"] == [0, 1, -1, 0]
    assert dimensions["four_momentum_p_mu"] == [1, 1, -1, 0]
    assert dimensions["four_current_J_mu"] == [0, -2, -1, 1]
    assert dimensions["stress_energy_T_mu_nu"] == [1, -1, -2, 0]


def test_all_six_dimension_and_restoration_cross_checks_pass() -> None:
    checks = _packet()["reversibility_cross_checks"]
    assert isinstance(checks, dict)
    assert checks["dimension_check_count"] == 6
    assert checks["passed_dimension_check_count"] == 6
    assert checks["algebraic_maps_declared_invertible"] is True
    rows = checks["checks"]
    assert isinstance(rows, list)
    assert len(rows) == 6
    assert all(row["passed"] for row in rows)
    assert len({row["check_id"] for row in rows}) == 6


def test_representative_equation_set_is_exact_and_not_applied() -> None:
    equations = _packet()["representative_equations"]
    assert isinstance(equations, list)
    assert [row["equation_id"] for row in equations] == [
        "SR_INTERVAL",
        "SR_MASS_SHELL",
        "CURRENT_CONSERVATION",
        "SOURCED_MAXWELL",
        "MATTER_STRESS_ENERGY_EXCHANGE",
        "GAUGE_STRESS_ENERGY_NORMALIZATION",
    ]
    assert all(
        row["application_status"] == "FROZEN_FOR_LATER_BOUNDED_APPLICATION"
        for row in equations
    )


def test_component_maps_restore_continuity_and_mass_shell_factors() -> None:
    packet = _packet()
    components = packet["component_definitions"]
    assert components["four_momentum"] == "p^mu = m u^mu = (E/c, p)"
    assert components["four_current"] == "J^mu_SI = (c rho, j)"
    equations = {
        row["equation_id"]: row for row in packet["representative_equations"]
    }
    assert "m^2 c^2" in equations["SR_MASS_SHELL"]["restored_SI_form"]
    assert equations["CURRENT_CONSERVATION"]["map"] == (
        "partial_0=c^-1 partial_t and J_SI^0=c rho"
    )


def test_electromagnetic_normalization_is_explicit_and_invertible() -> None:
    packet = _packet()
    normalization = packet["unit_policy"]["electromagnetic_normalization"]
    assert normalization == {
        "A_N": "A_SI / sqrt(mu_0)",
        "F_N": "F_SI / sqrt(mu_0)",
        "J_N": "sqrt(mu_0) J_SI",
        "inverse_map": (
            "A_SI=sqrt(mu_0)A_N; F_SI=sqrt(mu_0)F_N; "
            "J_SI=J_N/sqrt(mu_0)"
        ),
    }
    equations = {
        row["equation_id"]: row for row in packet["representative_equations"]
    }
    assert equations["SOURCED_MAXWELL"]["restored_SI_form"] == (
        "partial_mu F_SI^{mu nu} = mu_0 J_SI^nu"
    )
    assert "mu_0^-1" in equations["GAUGE_STRESS_ENERGY_NORMALIZATION"][
        "restored_SI_form"
    ]
    assert equations["MATTER_STRESS_ENERGY_EXCHANGE"]["map"] == (
        "F_N J_N = F_SI J_SI under the selected electromagnetic normalization"
    )


def test_negative_controls_block_the_named_scope_expansions() -> None:
    controls = _packet()["negative_controls"]
    assert isinstance(controls, list)
    assert len(controls) == 8
    assert len(set(controls)) == 8
    assert "REJECT_x0_EQUALS_t_WHILE_ALL_COORDINATES_ARE_DECLARED_LENGTH" in controls
    assert "REJECT_HISTORICAL_ARTIFACT_REWRITE_DURING_PACKET_PREPARATION" in controls
    assert "REJECT_SOURCED_MAXWELL_EQUALITY_WITHOUT_mu0_AS_SI" in controls


def test_migration_inventory_lists_but_does_not_rewrite_surfaces() -> None:
    packet = _packet()
    migration = packet["migration_inventory"]
    assert isinstance(migration, list)
    assert len(migration) == 6
    surfaces = {row["surface"] for row in migration}
    assert "SR covariance science increment" in surfaces
    assert "cosmology background surfaces" in surfaces
    assert "fixed-background scalar numerical sandboxes" in surfaces
    scope = packet["scope"]
    assert scope["historical_artifacts_modified"] is False
    assert scope["repository_wide_rewrite_authorized"] is False


def test_packet_preserves_nonclaims_and_requires_independent_review() -> None:
    packet = _packet()
    scope = packet["scope"]
    assert scope["representative_equation_application_executed"] is False
    assert scope["r13_reopened"] is False
    assert scope["external_comparator_activated"] is False
    hard_stop = packet["hard_stop"]
    assert hard_stop["independent_packet_review_required"] is True
    assert hard_stop["representative_equation_application_authorized_now"] is False
    assert hard_stop["migration_authorized_now"] is False
    assert hard_stop["repository_wide_rewrite_authorized"] is False
    assert len(packet["independent_review_requirements"]) == 12

