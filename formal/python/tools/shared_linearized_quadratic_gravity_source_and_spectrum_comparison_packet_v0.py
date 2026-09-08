from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_"
    "COMPARISON_PACKET_20260718_v0.json"
)
HUMAN_PACKET_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_"
    "COMPARISON_PACKET_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_packet_v0.py"
)
RESULT_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_"
    "RESULT_REVIEW_20260718_v0.json"
)
TARGET = (
    "prepare_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_packet_v0"
)
VERDICT = "PREPARED_PENDING_INDEPENDENT_REVIEW"
SELECTED_NEXT_TARGET = (
    "review_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_COMPARISON_PACKET_REVIEW_ONLY"

RESULT_REVIEW_HASHES = {
    "formal/docs/lanes/EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_RESULT_REVIEW_20260718_v0.md":
        "55dcef7184fdcde3b379b1f1abfb53b6ca0cbd137ec83750e7ab53d4694396d4",
    RESULT_REVIEW_RELATIVE_PATH:
        "905d162d104fa3763199a88758476c9c9231a07a35b62c8711cb922b633c0d4b",
    "formal/python/tools/exploratory_native_gravitational_requirements_family_survey_result_review_v0.py":
        "2ed3f9b6d0d3ba75282f9683a0c42411e364dc5c1389c99784ee2aee7412a29f",
    "formal/python/tests/test_exploratory_native_gravitational_requirements_family_survey_result_review_v0.py":
        "a14826867e084f2d303ff93fb834fd9ea317e3ee297bbb670c41435b4f29dc42",
    "formal/toe_formal/ToeFormal/Derivation/ExploratoryNativeGravitationalRequirementsFamilySurveyResultReviewV0.lean":
        "85631030f6401903e963c2de2f3038d40c6223538e2026edf23db1ffa190d6a4",
}

COMPARISON_STATUS_LABELS = (
    "COMPARISON ACTION FAMILY",
    "NOT A TOE CANDIDATE",
    "NOT A SUCCESSOR MASTER ACTION",
    "NOT A NATIVE POSTULATE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in RESULT_REVIEW_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"comparison-packet authority drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    result_review = _load_json(RESULT_REVIEW_RELATIVE_PATH)
    expected_verdict = (
        "ACCEPTED_AUTHORIZE_SHARED_LINEARIZED_QUADRATIC_GRAVITY_"
        "COMPARISON_PACKET_PREPARATION_ONLY"
    )
    if result_review.get("verdict") != expected_verdict:
        raise ValueError("survey result review did not accept packet preparation")
    if result_review.get("selected_next_target") != TARGET:
        raise ValueError("survey result review did not authorize this target")
    boundary = result_review["authorization_boundary"]
    if boundary.get("comparison_packet_preparation_authorized") is not True:
        raise ValueError("comparison packet preparation not authorized")
    if boundary.get("comparison_packet_execution_authorized") is not False:
        raise ValueError("comparison execution boundary was not closed")
    return custody, result_review


def _derivation_plan() -> list[dict[str, Any]]:
    steps = [
        ("D1_GAUSS_BONNET_REDUCTION", "Begin with all three quadratic invariants and prove only the frozen four-dimensional compact-support local-bulk reduction."),
        ("D2_EXACT_METRIC_VARIATION", "Vary the reduced metric action with respect to g^mu_nu while retaining boundary terms until the compact-support rule applies."),
        ("D3_EXACT_EULER_TENSOR_AND_IDENTITY", "Record E_mu_nu[g;alpha,beta] and verify its covariant divergence identity."),
        ("D4_MINKOWSKI_BACKGROUND", "Verify zero-source Minkowski is a background when Lambda=0."),
        ("D5_LINEARIZE_FROM_ACTION", "Set g=eta+h and derive E_mu_nu^lin through O(h) without importing the final equation."),
        ("D6_EXTERNAL_SOURCE_NORMALIZATION", "Add the frozen first variation of the external source and derive the kappa normalization."),
        ("D7_QUADRATIC_ACTION_CROSSCHECK", "Expand S_g^cmp+S_gf through O(h^2) and verify its Euler equation agrees with D5."),
        ("D8_PROJECTOR_INVERSION", "Decompose and invert the complete gauge-fixed quadratic operator in the Barnes-Rivers basis."),
        ("D9_CONSERVED_SOURCE_SATURATION", "Derive physical poles, residues, degeneracies, and source couplings after saturation with conserved sources."),
        ("D10_STATIC_CHANNEL_INVERSION", "Fourier-invert the same response for stationary 00 and 0i source channels."),
    ]
    return [
        {
            "order": index,
            "step_id": step_id,
            "obligation": obligation,
            "status": "NOT_EXECUTED",
            "derived_output": None,
        }
        for index, (step_id, obligation) in enumerate(steps, start=1)
    ]


def _mode_register() -> list[dict[str, Any]]:
    return [
        {
            "sector_id": sector_id,
            "expected_question_only": expected_question,
            "presence": "TO_BE_DERIVED",
            "pole": "TO_BE_DERIVED",
            "mass_squared": "TO_BE_DERIVED",
            "residue_sign": "TO_BE_DERIVED",
            "tachyon_condition": "TO_BE_DERIVED",
            "coupled_source_component": "TO_BE_DERIVED",
            "scientific_judgment_made": False,
        }
        for sector_id, expected_question in (
            ("MASSLESS_SPIN_2", "Einstein baseline sector to be reproduced as a control"),
            ("MASSIVE_SCALAR_CANDIDATE", "Candidate scalar channel; existence and locus not preassigned"),
            ("MASSIVE_SPIN_2_CANDIDATE", "Candidate beta-dependent channel; existence and residue not preassigned"),
        )
    ]


def _control_rows() -> list[dict[str, Any]]:
    controls = [
        ("C1_EH_BASELINE", "alpha=0; beta=0", "Derived normalization and 00/0i responses match the supplied linearized Einstein comparator."),
        ("C2_SCALAR_REPRESENTATIVE", "beta=0", "No generic massive spin-2 pole or correction; any scalar sector is derived rather than presumed."),
        ("C3_CURRENT_ZERO", "T_0i=0 for a conserved stationary source", "The current-sourced stationary h_0i contribution vanishes."),
        ("C4_CURRENT_SIGN", "T_0i -> -T_0i", "The linear stationary response obeys h_0i -> -h_0i."),
        ("C5_SOURCE_CONSERVATION", "deliberately violate partial_mu T^mu_nu=0", "Fail closed before interpreting a gauge-invariant saturated response."),
        ("C6_HEAVY_MODE_LIMIT", "take each derived pole mass to infinity along a stated nonsingular path", "The corresponding Yukawa term decouples while formal mode status remains explicit."),
        ("C7_DERIVED_SCALAR_DEGENERACY", "use a scalar degeneracy only after deriving its parameter locus", "Operator and Green-function routes agree on scalar-pole behavior."),
        ("C8_GAUGE_SECTOR", "retain longitudinal projectors before conserved-source saturation", "Physical conserved-source poles and residues are independent of gauge-sector terms."),
        ("C9_DIMENSIONS_NORMALIZATION", "audit every action term and the EH limit", "All terms have action units and the derived RHS coefficient is kappa=8 pi G/c^4."),
        ("C10_GAUSS_BONNET_LOCAL_BULK", "compare unreduced and reduced bases under compact-support variation", "Local bulk equations agree and no boundary or global claim is emitted."),
    ]
    return [
        {
            "control_id": control_id,
            "mutation": mutation,
            "required_behavior": required_behavior,
            "uses_shared_derivation_path": True,
            "status": "NOT_EXECUTED",
            "result": None,
        }
        for control_id, mutation, required_behavior in controls
    ]


def _preparation_controls(packet_value: dict[str, Any]) -> dict[str, Any]:
    action = packet_value["comparison_action_contract"]
    source = packet_value["external_source_contract"]
    basis = packet_value["quadratic_basis_contract"]
    geometry = packet_value["geometry_and_order_contract"]
    analytic = packet_value["fourier_gauge_and_green_contract"]
    modes = packet_value["mode_pole_residue_register"]
    outputs = packet_value["prepared_output_register"]
    controls = packet_value["shared_path_control_contract"]["rows"]
    scope = packet_value["scope"]
    rows = [
        {"control_id": "PREP_AUTHORITY_EXACT", "passed": packet_value["authority"]["consumed_result_review_verdict"].startswith("ACCEPTED_AUTHORIZE")},
        {"control_id": "PREP_COMPARISON_ONLY_LABELS", "passed": tuple(packet_value["classification"]["binding_labels"]) == COMPARISON_STATUS_LABELS},
        {"control_id": "PREP_COMMON_ACTION_NORMALIZATION", "passed": action["A_EH"] == "c^3/(16 pi G)" and action["alpha_dimension_SI"] == action["beta_dimension_SI"] == "m^2"},
        {"control_id": "PREP_EXTERNAL_SOURCE_ONLY", "passed": source["source_status"] == "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE" and source["ToE_matter_action_selected"] is False and source["conservation"] == "partial_mu T^mu_nu = 0"},
        {"control_id": "PREP_GAUSS_BONNET_SCOPE", "passed": basis["dimension"] == 4 and basis["local_bulk_reduction_only"] is True and basis["boundary_global_transport_allowed"] is False},
        {"control_id": "PREP_BACKGROUND_AND_ORDER", "passed": geometry["metric_signature"] == "(+,-,-,-)" and geometry["coordinate_time"] == "x^0=c t" and geometry["linearization_variable"] == "h_mu_nu" and geometry["alpha_beta_perturbative"] is False},
        {"control_id": "PREP_FOURIER_CONVENTION", "passed": analytic["fourier_kernel"] == "exp[-i k_mu x^mu] = exp[i(k_vec.x_vec-omega t)]" and analytic["Box_symbol"] == "-k^2"},
        {"control_id": "PREP_GAUGE_AND_BOUNDARY_PRESCRIPTIONS", "passed": analytic["gauge"] == "de Donder F_nu=0 with xi=1" and analytic["classical_dynamic_prescription"] == "RETARDED" and analytic["stationary_spatial_prescription"] == "DECAY_AT_INFINITY"},
        {"control_id": "PREP_DERIVATION_NOT_EXECUTED", "passed": all(row["status"] == "NOT_EXECUTED" and row["derived_output"] is None for row in packet_value["derivation_plan"]["rows"])},
        {"control_id": "PREP_MODE_REGISTER_BLANK", "passed": len(modes["rows"]) == 3 and all(row["presence"] == "TO_BE_DERIVED" and row["scientific_judgment_made"] is False for row in modes["rows"])},
        {"control_id": "PREP_00_0I_OUTPUTS_BLANK", "passed": all(row["status"] == "NOT_COMPUTED" and row["value"] is None for row in outputs["rows"])},
        {"control_id": "PREP_TEN_SHARED_PATH_CONTROLS_UNEXECUTED", "passed": len(controls) == 10 and all(row["uses_shared_derivation_path"] is True and row["status"] == "NOT_EXECUTED" and row["result"] is None for row in controls)},
        {"control_id": "PREP_NO_COEFFICIENT_FITTING", "passed": action["coefficient_fitting_authorized"] is False},
        {"control_id": "PREP_HARD_STOP", "passed": scope["packet_preparation_executed"] is True and all(value is False for key, value in scope.items() if key != "packet_preparation_executed")},
        {"control_id": "PREP_ROTATE_TO_INDEPENDENT_PACKET_REVIEW", "passed": packet_value["selected_next_target"] == SELECTED_NEXT_TARGET},
    ]
    return {
        "control_count": len(rows),
        "pass_count": sum(row["passed"] for row in rows),
        "failure_count": sum(not row["passed"] for row in rows),
        "rows": rows,
    }


def build_packet() -> dict[str, Any]:
    custody, result_review = _validate_authority()
    human = REPO_ROOT / HUMAN_PACKET_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("comparison packet human record or focused test missing")

    value: dict[str, Any] = {
        "schema_id": "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_PACKET_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_result_review_verdict": result_review["verdict"],
            "frozen_result_review_artifacts": custody,
            "human_packet": {"relative_path": HUMAN_PACKET_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "classification": {
            "status": "SUPPLIED_COMPARISON_FAMILY",
            "binding_labels": list(COMPARISON_STATUS_LABELS),
            "ToE_adoption": "NONE",
            "native_principle": "NONE",
            "candidate_action_authority": "NONE",
            "successful_calculation_promotes_action": False,
        },
        "comparison_action_contract": {
            "coordinate_measure": "d^4x with x^0=c t",
            "A_EH": "c^3/(16 pi G)",
            "kappa": "8 pi G/c^4",
            "action": "S_g^cmp=A_EH integral d^4x sqrt(-g)[R+alpha R^2+beta R_mu_nu R^mu_nu]",
            "cosmological_constant": 0,
            "cosmological_constant_scope": "Minkowski comparison-background choice only",
            "c_dimension_SI": "m s^-1",
            "G_dimension_SI": "m^3 kg^-1 s^-2",
            "A_EH_dimension_SI": "kg s^-1",
            "curvature_dimension_SI": "m^-2",
            "alpha_dimension_SI": "m^2",
            "beta_dimension_SI": "m^2",
            "metric_dimension_SI": "dimensionless",
            "action_dimension_SI": "J s",
            "alpha_beta_domain": "symbolic real parameters",
            "alpha_beta_are_project_parameters": False,
            "alpha_beta_perturbative": False,
            "coefficient_fitting_authorized": False,
            "term_provenance": [
                {"term": "R", "role": "SUPPLIED_EINSTEIN_HILBERT_COMPARATOR"},
                {"term": "R^2", "role": "SUPPLIED_SCALAR_CURVATURE_QUADRATIC_COMPARATOR"},
                {"term": "R_mu_nu R^mu_nu", "role": "SUPPLIED_GENERIC_LOCAL_METRIC_QUADRATIC_COMPARATOR"},
            ],
        },
        "external_source_contract": {
            "source_status": "EXTERNALLY_SUPPLIED_CONSERVED_COMPARISON_SOURCE",
            "symmetry": "T_mu_nu=T_nu_mu",
            "conservation": "partial_mu T^mu_nu = 0",
            "dimension_SI": "J m^-3",
            "first_variation": "delta S_ext|eta=-(1/(2c)) integral d^4x T_mu_nu delta g^mu_nu",
            "linear_coupling": "S_ext^(1)=+(1/(2c)) integral d^4x h_mu_nu T^mu_nu",
            "required_derived_equation_normalization": "E_mu_nu^lin=kappa T_mu_nu",
            "mass_density_probe_definition": "rho=T_00/c^2",
            "current_probe_component": "covariant T_0i under frozen index conventions",
            "nondynamical": True,
            "ToE_matter_action_selected": False,
            "variation_derived_ToE_stress_energy": False,
            "matter_field_content_selected": False,
        },
        "quadratic_basis_contract": {
            "dimension": 4,
            "unreduced_basis": ["R^2", "R_mu_nu R^mu_nu", "R_mu_nu_rho_sigma R^mu_nu_rho_sigma"],
            "Euler_density": "E_4=Riemann^2-4 Ricci^2+R^2",
            "reduction_identity": "gamma Riemann^2=gamma E_4+4 gamma Ricci^2-gamma R^2",
            "coefficient_map": {"alpha_reduced": "alpha_unreduced-gamma", "beta_reduced": "beta_unreduced+4 gamma"},
            "variation_domain": "smooth compactly supported metric variations in Omega compactly contained in M at fixed topology",
            "local_bulk_reduction_only": True,
            "boundary_global_transport_allowed": False,
            "nonclaims": ["boundary charges", "boundary actions", "global topology", "arbitrary boundary conditions", "D!=4", "nonlocal theories"],
        },
        "geometry_and_order_contract": {
            "coordinate_time": "x^0=c t",
            "metric_signature": "(+,-,-,-)",
            "background_metric": "eta_mu_nu=diag(+1,-1,-1,-1)",
            "perturbation": "g_mu_nu=eta_mu_nu+h_mu_nu",
            "linearization_variable": "h_mu_nu",
            "index_metric_at_linear_order": "eta_mu_nu",
            "Riemann_convention": "R^rho_sigma_mu_nu=partial_mu Gamma^rho_nu_sigma-partial_nu Gamma^rho_mu_sigma+Gamma^rho_mu_lambda Gamma^lambda_nu_sigma-Gamma^rho_nu_lambda Gamma^lambda_mu_sigma",
            "Ricci_convention": "R_sigma_nu=R^rho_sigma_rho_nu",
            "Box": "eta^mu_nu partial_mu partial_nu=c^-2 partial_t^2-spatial_laplacian",
            "gravitational_action_expansion": "through O(h^2)",
            "source_expansion": "through O(h)",
            "field_equation_order": "through O(h)",
            "discarded_equation_order": "O(h^2) and higher",
            "alpha_beta_perturbative": False,
            "Minkowski_background_must_be_verified": True,
        },
        "fourier_gauge_and_green_contract": {
            "fourier_forward": "f_tilde(k)=integral d^4x exp[+i k_mu x^mu] f(x)",
            "fourier_inverse": "f(x)=integral d^4k/(2 pi)^4 exp[-i k_mu x^mu] f_tilde(k)",
            "fourier_kernel": "exp[-i k_mu x^mu] = exp[i(k_vec.x_vec-omega t)]",
            "k0": "omega/c",
            "k_squared": "(omega/c)^2-|k_vec|^2",
            "partial_symbol": "-i k_mu",
            "Box_symbol": "-k^2",
            "stationary_inverse": "integral d^3q/(2 pi)^3 exp[i q.x] f_tilde(q)",
            "gauge": "de Donder F_nu=0 with xi=1",
            "trace_reverse": "hbar_mu_nu=h_mu_nu-(1/2)eta_mu_nu h",
            "gauge_function": "F_nu=partial^mu hbar_mu_nu",
            "gauge_fixing_action": "S_gf=-(A_EH/(2 xi)) integral d^4x F_nu F^nu",
            "classical_dynamic_prescription": "RETARDED",
            "retarded_momentum_label": "+i0 k_0 continuation under frozen Fourier sign",
            "residue_reporting_label": "FEYNMAN +i0 FOR POLE ORIENTATION ONLY",
            "stationary_spatial_prescription": "DECAY_AT_INFINITY",
            "growing_Yukawa_branch_allowed": False,
            "prescriptions_may_be_conflated": False,
        },
        "projector_contract": {
            "theta": "theta_mu_nu=eta_mu_nu-k_mu k_nu/k^2",
            "P2": "P2=(1/2)(theta_mu_rho theta_nu_sigma+theta_mu_sigma theta_nu_rho)-(1/3)theta_mu_nu theta_rho_sigma",
            "P0s": "P0s=(1/3)theta_mu_nu theta_rho_sigma",
            "complete_longitudinal_projectors_required_for_inversion": True,
            "conserved_source_saturation_required": True,
            "massless_pole_interpretation": "conserved-source saturated limit",
            "standalone_singular_theta_is_observable": False,
            "gauge_independence_check_required": True,
        },
        "derivation_plan": {"step_count": 10, "executed_step_count": 0, "rows": _derivation_plan(), "literature_oracle_allowed_only_after_derivation": True},
        "mode_pole_residue_register": {
            "sector_count": 3,
            "scientific_judgment_count": 0,
            "rows": _mode_register(),
            "required_distinctions": {
                "GHOST": "wrong-sign kinetic term or negative physical residue",
                "TACHYON": "negative derived mass-squared",
                "CLASSICAL_INSTABILITY": "separately established background or evolution growth",
                "MATTER_INSTABILITY": "instability requiring specified matter environment or coupling",
                "HEAVY_DECOUPLED_MODE": "formally present mode with suppressed tested response",
            },
        },
        "prepared_output_register": {
            "output_count": 11,
            "computed_output_count": 0,
            "rows": [
                {"output_id": output_id, "status": "NOT_COMPUTED", "value": None}
                for output_id in (
                    "NORMALIZED_ACTION_AND_SOURCE_RECORD",
                    "GAUSS_BONNET_LOCAL_BULK_REDUCTION_PROOF",
                    "EXACT_METRIC_EULER_TENSOR",
                    "LINEARIZED_FIELD_EQUATION",
                    "GAUGE_FIXED_QUADRATIC_OPERATOR",
                    "CONSERVED_SOURCE_SATURATED_PROPAGATOR",
                    "POLE_MASS_RESIDUE_TACHYON_DEGENERACY_TABLE",
                    "STATIONARY_00_GREEN_FUNCTION",
                    "STATIONARY_0I_GREEN_FUNCTION",
                    "TEN_SHARED_PATH_CONTROL_RESULTS",
                    "POST_DERIVATION_LITERATURE_COMPARISON_AND_STOP_RECORD",
                )
            ],
            "stationary_00_requirements": ["massless 1/r kernel", "derived scalar Yukawa kernels", "derived massive-spin-2 Yukawa kernels", "source coefficients", "alpha beta dependence", "exact EH limit"],
            "stationary_0i_requirements": ["scalar coupling determination", "massive-spin-2 coupling determination", "long-range kernel", "Yukawa kernels", "exact T_0i index and sign", "no orbital observable"],
        },
        "shared_path_control_contract": {"control_count": 10, "executed_control_count": 0, "rows": _control_rows(), "coefficient_fitting_prohibited": True},
        "fail_closed_conditions": [
            "curvature Fourier gauge source or index sign ambiguity",
            "Einstein-Hilbert or source normalization ambiguity",
            "Gauss-Bonnet domain ambiguity",
            "unresolved degenerate pole or noninvertible operator",
            "source nonconservation",
            "boundary or Green-function prescription ambiguity",
            "ghost tachyon and instability meanings conflated",
            "Einstein control not reproduced without coefficient fitting",
        ],
        "scope": {
            "packet_preparation_executed": True,
            "independent_packet_review_executed": False,
            "comparison_execution_authorized": False,
            "metric_or_tetrad_variation_executed": False,
            "linearized_field_equation_derived": False,
            "propagator_or_mode_calculation_executed": False,
            "pole_or_residue_judgment_made": False,
            "Green_function_computed": False,
            "coefficient_fitting_executed": False,
            "modified_gravity_constraint_computed": False,
            "matter_sector_selected": False,
            "orbital_precession_computed": False,
            "frame_dragging_reopened": False,
            "LARES2_analysis_executed": False,
            "comparison_action_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "master_action_mutation_authorized": False,
            "authoritative_V2_population_authorized": False,
            "automated_action_selection_lane_reopening_authorized": False,
        },
        "current_posture": {
            "exploratory_survey": "ACCEPTED_12_OF_12_GATES",
            "comparison_packet": VERDICT,
            "comparison_execution": "NOT_AUTHORIZED",
            "real_mode_judgments": "NONE",
            "real_Green_functions": "NONE",
            "authoritative_matrix": "0_OF_70",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "metric_variation": "NOT_EXECUTED",
            "frame_dragging": "NOT_RESUMED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }
    preparation_controls = _preparation_controls(value)
    if preparation_controls["control_count"] != preparation_controls["pass_count"]:
        failed = [row["control_id"] for row in preparation_controls["rows"] if not row["passed"]]
        raise ValueError(f"quadratic comparison packet preparation failure: {failed}")
    value["preparation_controls"] = preparation_controls
    return value


def artifact_bytes() -> bytes:
    return (json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate or check the shared linearized quadratic-gravity comparison packet.")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("shared quadratic-gravity comparison packet artifact drift")
        print(json.dumps({
            "status": "VERIFIED",
            "verdict": VERDICT,
            "preparation_controls": "15_OF_15_PASSED",
            "derivation_steps_executed": 0,
            "mode_judgments": 0,
            "Green_functions_computed": 0,
            "comparison_execution_authorized": False,
            "selected_next_target": SELECTED_NEXT_TARGET,
        }, sort_keys=True))
        return 0
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
