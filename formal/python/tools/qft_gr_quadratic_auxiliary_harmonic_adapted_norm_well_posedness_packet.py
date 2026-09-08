from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


PHASE_A_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_PHYSICAL_SPIN2_PRINCIPAL_BLOCK_"
    "RESULT_REVIEW_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_ADAPTED_NORM_"
    "WELL_POSEDNESS_PACKET_20260728_v0.json"
)
CURRENT_TARGET = (
    "prepare_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_"
    "well_posedness_packet_v0"
)
REVIEW_TARGET = (
    "review_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_"
    "well_posedness_packet_v0_result"
)
EXECUTION_TARGET = (
    "derive_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0"
)


def build_packet() -> dict:
    phase_a = read_json(PHASE_A_REVIEW_PATH)
    if phase_a["accepted"] is not True:
        raise QuadraticHyperbolicityError("Phase A result was not accepted")
    if phase_a["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError("adapted-norm packet authority mismatch")
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_ADAPTED_NORM_"
            "WELL_POSEDNESS_PACKET_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "preparation_target": CURRENT_TARGET,
        "consumed_phase_a_review": {
            "path": PHASE_A_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(PHASE_A_REVIEW_PATH),
            "accepted_results": phase_a["accepted_results"],
        },
        "frozen_scope": {
            "theory": (
                "sqrt(-g) [c_R R + c_Lambda + alpha R^2 "
                "+ beta R_mn R^mn]"
            ),
            "domain": ["beta != 0", "3 alpha + beta != 0"],
            "source": "VACUUM",
            "dimension": 4,
            "metric_signature": "(-,+,+,+)",
            "gauge": "GENERALIZED_HARMONIC",
            "gauge_source_boundary": (
                "H_mu(x,g) is prescribed and contains no metric derivatives "
                "that change the second-order principal wave operator."
            ),
        },
        "auxiliary_variables": [
            {
                "symbol": "R",
                "definition": "scalar curvature of g",
                "sector": "massive scalar",
            },
            {
                "symbol": "S_mn",
                "definition": "R_mn - (1/4) g_mn R",
                "sector": "trace-free massive spin-2 auxiliary tensor",
            },
            {
                "symbol": "g_mn",
                "definition": "spacetime metric",
                "sector": "metric and massless spin-2",
            },
        ],
        "candidate_reduced_system": {
            "scalar_trace_equation": (
                "2(3 alpha + beta) Box_g R - c_R R "
                "- 2 c_Lambda = 0"
            ),
            "trace_free_ricci_principal_equation": (
                "beta Box_g S_mn "
                "- (2 alpha + beta)(nabla_m nabla_n R)^TF "
                "= lower(g,dg,R,dR,S,dS)"
            ),
            "generalized_harmonic_metric_principal_equation": (
                "Box_g g_mn = -2 S_mn - (1/2)g_mn R "
                "+ lower(g,dg,H,dH)"
            ),
            "triangular_principal_order": [
                "R wave equation",
                "S_mn wave equation forced by the trace-free Hessian of R",
                "g_mn generalized-harmonic wave equation forced by R and S_mn",
            ],
            "mass_parameters_for_flat_control": {
                "m0_squared": "c_R / [2(3 alpha + beta)]",
                "m2_squared": "-c_R / beta",
                "interpretation_requires": "c_R != 0",
                "principal_result_depends_on_mass_signs": False,
            },
            "status": "CANDIDATE_REQUIRING_TERM_BY_TERM_DERIVATION",
        },
        "constraints": [
            {
                "id": "C_H_mu",
                "definition": "H_mu - g_mn g^ab Gamma^n_ab",
                "required_propagation": "homogeneous wave system",
            },
            {
                "id": "C_R",
                "definition": "R - scalar_curvature[g]",
                "required_propagation": "closed homogeneous definition-constraint system",
            },
            {
                "id": "C_S_mn",
                "definition": (
                    "S_mn - (R_mn[g] - (1/4)g_mn scalar_curvature[g])"
                ),
                "required_propagation": "closed homogeneous definition-constraint system",
            },
            {
                "id": "C_trace",
                "definition": "g^mn S_mn",
                "required_propagation": "zero if initially zero",
            },
            {
                "id": "C_div_n",
                "definition": "nabla^m S_mn - (1/4)nabla_n R",
                "required_propagation": "contracted-Bianchi compatibility",
            },
            {
                "id": "C_Hamiltonian_and_momentum",
                "definition": "normal projections of the metric equations",
                "required_propagation": "generalized-Bianchi compatibility",
            },
        ],
        "initial_data": {
            "metric_data": ["g_ij", "K_ij"],
            "auxiliary_data": [
                "R",
                "normal derivative of R",
                "S_mn",
                "normal derivative of S_mn",
            ],
            "compatibility": [
                "generalized-harmonic gauge constraint",
                "Hamiltonian and momentum constraints",
                "C_R = 0",
                "C_S_mn = 0",
                "C_trace = 0",
                "C_div_n = 0",
            ],
            "free_vs_derived_components_must_be_enumerated": True,
        },
        "standard_metric_norm_test": {
            "energy_family": (
                "E_metric,s = ||g||^2_H^(s+3) "
                "+ ||dt g||^2_H^(s+2) "
                "+ ||dt^2 g||^2_H^(s+1) "
                "+ ||dt^3 g||^2_H^s"
            ),
            "same_order_estimate_available_generically": False,
            "reason": (
                "Accepted Phase A physical block has algebraic multiplicity "
                "4 and geometric multiplicity 2 at each light-cone root."
            ),
            "claim_boundary": (
                "This rules out the uniform same-order estimate for arbitrary "
                "lower terms; it does not by itself rule out a special "
                "triangular adapted norm."
            ),
        },
        "adapted_norm_candidate": {
            "wave_energy_definition": (
                "W_q[u] = ||u||^2_H^(q+1) + ||dt u||^2_H^q"
            ),
            "candidate": (
                "E_ad,s = W_(s+1)[g] + W_s[S] + W_(s+1)[R]"
            ),
            "component_regularities": {
                "g": "H^(s+2) with dt g in H^(s+1)",
                "S": "H^(s+1) with dt S in H^s",
                "R": "H^(s+2) with dt R in H^(s+1)",
            },
            "linear_triangular_motivation": [
                "Hessian(R) lies in H^s when R lies in H^(s+2).",
                "R and S lie in H^(s+1), sufficient as metric-wave forcing at the displayed grading.",
                "Translation back to pure metric initial data may require one extra derivative beyond E_metric,s.",
            ],
            "candidate_pure_metric_derivative_loss": 1,
            "minimum_loss_established": False,
            "nonlinear_closure_established": False,
            "continuous_dependence_established": False,
            "safe_starting_integer_index": "s >= 3",
            "minimum_regularity_established": False,
        },
        "required_execution_checks": [
            "Derive every lower-order term and verify no hidden principal derivative appears.",
            "Verify trace and trace-free projections with the frozen curvature convention.",
            "Construct the generalized-harmonic reduced equations without changing the physical action.",
            "Derive a homogeneous propagation system for every listed constraint.",
            "Prove or refute the candidate linear variable-coefficient energy estimate.",
            "Determine whether the one-derivative-loss candidate is minimal.",
            "Determine whether the loss is fixed or accumulates under nonlinear iteration.",
            "Attempt Picard closure; if it loses derivatives, state whether Nash-Moser or a different scale is required.",
            "State existence time, uniqueness class, and continuous-dependence topology separately.",
            "Reconstruct a solution of the unreduced metric equations from constraint-satisfying reduced data.",
        ],
        "decision_tree": {
            "same_order_metric_estimate": "REFUTED_BY_ACCEPTED_PHASE_A",
            "auxiliary_adapted_estimate": "OPEN",
            "if_picard_closes_with_fixed_loss": (
                "ADAPTED_NORM_LOCAL_WELL_POSEDNESS_ESTABLISHED"
            ),
            "if_only_smooth_iteration_closes": (
                "SMOOTH_EXISTENCE_WITHOUT_HADAMARD_WELL_POSEDNESS"
            ),
            "if_no_usable_iteration_closes": (
                "GENERIC_LOCAL_WELL_POSEDNESS_BLOCKED"
            ),
        },
        "prohibitions": [
            "No order reduction presented as the original theory.",
            "No regulator or fiducial mode added to close the estimate.",
            "No numerical stability substituted for an energy estimate.",
            "No smooth existence theorem relabeled strong hyperbolicity.",
            "No source extension during the vacuum reduced-system derivation.",
            "No preserved descendant adopted as the result.",
            "No Yukawa work.",
        ],
        "authorized_execution_after_review": {
            "target": EXECUTION_TARGET,
            "scope": (
                "Derive and verify the exact vacuum generalized-harmonic "
                "auxiliary reduced system and its constraint propagation. "
                "Energy-estimate execution remains a successor decision."
            ),
        },
        "not_yet_authorized": [
            "Nonlinear adapted-norm theorem claim.",
            "Prescribed-source extension.",
            "Dynamical matter extension.",
            "Semiclassical source extension.",
            "Maxwell-Dirac secondary calculation.",
        ],
        "selected_next_target": REVIEW_TARGET,
        "verdict": (
            "AUXILIARY_HARMONIC_AND_TWO_NORM_EXECUTION_OBLIGATIONS_"
            "PREPARED_FOR_REVIEW"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_packet,
        description=(
            "quadratic auxiliary-harmonic adapted-norm well-posedness packet"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
