from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0.py"
)
CONTRACT_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0.md"
)
TARGET = "prepare_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0"
SELECTED_NEXT_TARGET = (
    "review_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0_result"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/POST_SR_TOOLING_FULL_TOE_SCIENTIFIC_PRIORITY_SELECTION_20260717_v0.json":
        "ca9d4f032f7d9bd0ce2fef104e6c7d6d1718582ad5f2266ea4a8c3fbd4220179",
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v3.json":
        "0dbe441d78de6eba0fe006f7b6b280b655a3feae3e1f9d66775eefae9e49a3b1",
    "formal/docs/lanes/SR_COORDINATE_CONVENTION_AND_RESTORATION_TOOLING_CLOSEOUT_20260717_v0.md":
        "aae7a1e0e7029a778dbc9ab3b88952cc3c619624c2bd2255f151c4040d0548ab",
    "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json":
        "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
    "formal/docs/release/EXTERNAL_RELATED_WORK_AND_METHODS_INTAKE_20260717_v0.json":
        "351fe687ab20a8f83b01ebe8dc807274703acf0cc388805ad5f8481cdbf84ca3",
    "formal/docs/lanes/EXTERNAL_RELATED_WORK_AND_BENCHMARK_INTAKE_20260717_v0.md":
        "a5608b1bbda442e78d177e5668254852dabc2740eb55525eb107f9ecb44a3cb9",
    "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md":
        "1d9fbe0b49d45aad3781b4217dc108a6f2c16361cd59fa662c8283de10f6ac67",
    "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean":
        "da375e85850deb5d32da8a60c24d2fd7021c95143f8da036973d9575bd398458",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean":
        "162cdd0d9596566457ae40c340329b15064e4d0ed17d20deadc48fc2fc431384",
    CONTRACT_RELATIVE_PATH:
        "0e206867019c2c8b66431a6bc3ca161ab6f0b8fae1fa9cdd08f83830cc38c92e",
}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        path = REPO_ROOT / relative_path
        observed = _sha256(path.read_bytes())
        if observed != expected_hash:
            raise ValueError(f"GR packet authority/source hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    selection = json.loads(
        (REPO_ROOT / "formal/docs/release/POST_SR_TOOLING_FULL_TOE_SCIENTIFIC_PRIORITY_SELECTION_20260717_v0.json").read_text(
            encoding="utf-8"
        )
    )
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("GR packet does not consume the selected scientific target")
    if selection.get("verdict") != "SELECTED_DIRECT_GR_KNOWN_LIMIT_RECOVERY_PREPARATION":
        raise ValueError("GR selection verdict mismatch")
    if selection["ranking"]["selected_candidate_id"] != (
        "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY"
    ):
        raise ValueError("GR selected candidate mismatch")

    action_text = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean"
    ).read_text(encoding="utf-8")
    for token in (
        "def actionRep32 : ActionRep32Scaffold",
        "Leaves analytic derivation of `firstVariationRep32` from an action functional open",
    ):
        if token not in action_text:
            raise ValueError(f"project action source token missing: {token}")

    weak_text = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean"
    ).read_text(encoding="utf-8")
    for token in (
        "def WeakFieldPoissonLimitStatement3D",
        "h_kappa_relation : κ = 4 * Real.pi * G_N",
        "No analytic discharge is claimed in this module",
    ):
        if token not in weak_text:
            raise ValueError(f"project weak-field source token missing: {token}")

    gr_doc = (
        REPO_ROOT / "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"
    ).read_text(encoding="utf-8")
    for token in (
        "Bounded/discrete weak-field v0 only",
        "No continuum-limit, uniqueness, or infinite-domain inversion claims",
        "Core Rep32 operator remains scaffold-level",
    ):
        if token not in gr_doc:
            raise ValueError(f"project GR boundary token missing: {token}")

    contract = (REPO_ROOT / CONTRACT_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "INDEPENDENT_RECOVERY_ORACLE_NOT_DERIVATION_INPUT",
        "FIELD_EQUATION_SURFACE_FAILURE",
        "review_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0_result",
        "No numerical orbit integration is authorized",
    ):
        if token not in contract:
            raise ValueError(f"GR contract token missing: {token}")
    return rows


PROJECT_SOURCE_BINDINGS = [
    {
        "binding_id": "GR_PROJECT_ACTION_REP32_SCAFFOLD",
        "relative_path": "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean",
        "exact_object": "actionRep32 : ActionRep32Scaffold",
        "claim_class": "STRUCTURAL_ACTION_SCAFFOLD",
        "limitation": (
            "analytic first variation from the action functional remains open; "
            "this is not a continuum tensor Einstein-equation surface"
        ),
    },
    {
        "binding_id": "GR_PROJECT_BOUNDED_DISCRETE_WEAK_FIELD_POISSON",
        "relative_path": "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean",
        "exact_objects": [
            "WeakFieldPoissonLimitStatement3D",
            "UnitsAndCalibration.h_kappa_relation",
            "DiscretePoissonResidual3D",
        ],
        "claim_class": "BOUNDED_DISCRETE_NEWTONIAN_RECOVERY_UNDER_ASSUMPTIONS",
        "limitation": "no continuum tensor, Einstein-equation, uniqueness, or infinite-domain claim",
    },
    {
        "binding_id": "GR_PROJECT_DISCHARGE_BOUNDARY",
        "relative_path": "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md",
        "exact_object": "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0",
        "claim_class": "T_PROVED_BOUNDED_DISCRETE_V0",
        "limitation": "blocker inventory and bounded/discrete nonclaim remain binding",
    },
]


REQUIRED_CONTROLS = [
    {
        "control_id": "ZERO_ANGULAR_MOMENTUM",
        "changed_premise_count": 1,
        "mutation": "J := 0",
        "required_result": "g_0i^rot=0 and dot(Omega)_LT=0",
    },
    {
        "control_id": "ANGULAR_MOMENTUM_SIGN_REVERSAL",
        "changed_premise_count": 1,
        "mutation": "J := -J",
        "required_result": "g_0i^rot and dot(Omega)_LT reverse sign with unchanged magnitude",
    },
    {
        "control_id": "WRONG_SOURCE_COMPONENT",
        "changed_premise_count": 1,
        "mutation": "replace T_0i current source by T_00",
        "required_result": "current-dipole rotational field is not recovered",
    },
    {
        "control_id": "MIXED_METRIC_COMPONENT_REMOVAL",
        "changed_premise_count": 1,
        "mutation": "set g_0i^rot := 0",
        "required_result": "Lense-Thirring disturbing term is absent",
    },
    {
        "control_id": "WRONG_GREEN_NORMALIZATION",
        "changed_premise_count": 1,
        "mutation": "replace the frozen Poisson Green coefficient by a wrong coefficient",
        "required_result": "metric coefficient oracle comparison fails",
    },
    {
        "control_id": "SIGNATURE_MIX",
        "changed_premise_count": 1,
        "mutation": "import one (-,+,+,+) sign rule without complete conversion",
        "required_result": "SIGNATURE_CONVENTION_MISMATCH",
    },
    {
        "control_id": "COEFFICIENT_FIT_ATTEMPT",
        "changed_premise_count": 1,
        "mutation": "use an oracle or observation to set an intermediate coefficient",
        "required_result": "RECOVERY_COEFFICIENT_FITTING_FORBIDDEN",
    },
    {
        "control_id": "NONDECAYING_EXTERIOR_MODE",
        "changed_premise_count": 1,
        "mutation": "retain one growing or nondecaying rotational homogeneous mode",
        "required_result": "ASYMPTOTIC_FLATNESS_BOUNDARY_FAILURE",
    },
]


FAILURE_CLASSES = [
    "FIELD_EQUATION_SURFACE_FAILURE",
    "SOURCE_IDENTIFICATION_FAILURE",
    "FIELD_EQUATION_NORMALIZATION_OR_SIGN_FAILURE",
    "EXTERIOR_CURRENT_DIPOLE_FAILURE",
    "OBSERVABLE_TRANSPORT_FAILURE",
    "SUPPLIED_TARGET_OR_COEFFICIENT_DEPENDENCE",
]


def build_packet() -> dict[str, Any]:
    authority_rows = _validate_authority_and_sources()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("GR packet focused test is missing")

    return {
        "schema_id": "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "INDEPENDENT_PACKET_REVIEW_ONLY",
        "authority": {
            "consumed_selection_verdict": "SELECTED_DIRECT_GR_KNOWN_LIMIT_RECOVERY_PREPARATION",
            "selected_candidate": "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY",
            "frozen_inputs": authority_rows,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "scientific_question": (
            "Under frozen stationary, weak-field, slow-rotation, compact-source, "
            "exterior, gauge, boundary, and orbital assumptions, can the project GR "
            "sector derive the leading gravitomagnetic g_0i component and "
            "Lense-Thirring nodal coefficient without importing or fitting either?"
        ),
        "project_source_bindings": {
            "required_count": 3,
            "rows": PROJECT_SOURCE_BINDINGS,
            "starting_surface_rule": (
                "A future calculation must first derive or validly transport from the "
                "exact project surface to a continuum tensor metric equation; a standard "
                "Einstein equation cannot be substituted and relabeled project-derived."
            ),
            "first_registered_failure": "FIELD_EQUATION_SURFACE_FAILURE",
        },
        "retained_convention": {
            "temporal_coordinate": "x^0=c t",
            "background_metric": "eta_mu_nu=diag(+1,-1,-1,-1)",
            "dimensionful_target": "SI",
            "metric_perturbation": "g_mu_nu=eta_mu_nu+h_mu_nu; |h_mu_nu|<<1",
            "spatial_component_policy": "Euclidean three-vector labels for i,j,k",
            "sr_tooling_reopened": False,
            "equation_specific_derivation_required": True,
        },
        "regime_and_ordering": {
            "stationary_source": "partial_0 T_mu_nu=0 at retained order",
            "retained_source_conservation": "partial_mu T^{mu nu}=0 at retained order",
            "isolated_compact_source": True,
            "exterior_domain": "r>R_s",
            "weak_field_order": "linear in h_mu_nu",
            "slow_internal_motion": "epsilon_v=|v|/c<<1",
            "rotation_order": "linear in J",
            "radiation_and_retardation": "neglected at retained stationary order",
            "coordinate_frame": "asymptotically Cartesian mass-centered harmonic",
            "stationary_current_conservation": (
                "nabla dot j_m=0 as the leading slow-source continuity consequence"
            ),
            "retained_multipoles": [
                "mass monopole M as nonrotating orbital background",
                "current dipole J as rotational perturbation",
            ],
            "discarded_terms": [
                "mass dipole in the center-of-mass frame",
                "higher current multipoles",
                "spin-squared terms",
                "higher post-Newtonian terms",
                "source deformation",
                "radiative time derivatives",
            ],
        },
        "source_contract": {
            "mass_current": "j_m=rho_m v",
            "contravariant_mixed_component": "T^{0i}=c j_m^i+higher order",
            "covariant_mixed_component": "T_0i=-c j_m_i+higher order",
            "mass_center_condition": "integral rho_m x d^3x=0",
            "zero_total_momentum_condition": "integral j_m d^3x=0",
            "angular_momentum": "J=integral x cross j_m(x) d^3x",
            "current_moment_identity_to_derive": (
                "integral j_m_i x'_j d^3x'=-(1/2)epsilon_ijk J_k"
            ),
            "stress_policy": (
                "T^{ij} and pressure may not manufacture the leading 0i current-dipole "
                "coefficient; any retained contribution requires explicit power counting"
            ),
            "conservation_policy": (
                "partial_mu T^{mu nu}=0 at retained order is required for harmonic-gauge "
                "compatibility and supplies the leading stationary current continuity law"
            ),
        },
        "gauge_and_boundary_contract": {
            "trace_reversal": "hbar_mu_nu=h_mu_nu-(1/2)eta_mu_nu h",
            "trace": "h=eta^{alpha beta}h_alpha_beta",
            "gauge": "partial^mu hbar_mu_nu=0",
            "residual_gauge_equation": "box xi_mu=0; stationary: nabla^2 xi_mu=0",
            "residual_gauge_boundary": (
                "regular and asymptotically decaying; exclude transformations that alter "
                "the leading current-dipole coefficient in the fixed ACMC harmonic representative"
            ),
            "mixed_component_identity": "hbar_0i=h_0i=g_0i at linear order",
            "green_normalization": "nabla^2(1/|x-x'|)=-4 pi delta^3(x-x')",
            "boundaries": [
                "perturbation vanishes at spatial infinity",
                "no growing or nondecaying exterior rotational homogeneous mode",
                "exterior solution is matched to a localized stationary source",
            ],
        },
        "derivation_inputs": {
            "allowed": [
                "three exact project source bindings",
                "retained coordinate, metric, and SI convention",
                "frozen regime, source, gauge, and boundary premises",
                "point-particle action S_pp=-m c integral ds",
            ],
            "forbidden": [
                "standard-GR field equation as a project-derived premise",
                "metric coefficient oracle",
                "nodal coefficient oracle",
                "observational coefficient",
                "coefficient fitting or calibration",
            ],
        },
        "independent_recovery_oracles": {
            "classification": "INDEPENDENT_RECOVERY_ORACLE_NOT_DERIVATION_INPUT",
            "visibility_rule": "COMPARE_ONLY_AFTER_COMPUTED_RESULT_AND_PROVENANCE_ARE_FROZEN",
            "linearized_field_equation": "box hbar_mu_nu=-(16 pi G/c^4)T_mu_nu",
            "wave_operator": "box=(1/c^2)partial_t^2-nabla^2",
            "stationary_0i_equation": "nabla^2 hbar_0i=+(16 pi G/c^4)T_0i",
            "source_integral": (
                "hbar_0i(x)=-(4G/c^4) integral T_0i(x')/|x-x'| d^3x'"
            ),
            "exterior_rotational_metric": (
                "g_0i^rot=+(2G/c^3)(J cross r)_i/r^3"
            ),
            "orbital_orientation": (
                "J=J z_hat; ascending node is right-handed about +z"
            ),
            "nodal_rate": (
                "dot(Omega)_LT=+(2GJ)/(c^2 a^3 (1-e^2)^(3/2))"
            ),
            "oracle_used_as_input": False,
        },
        "authorized_future_derivation_route": {
            "stage_count": 7,
            "stages": [
                "derive or justify a continuum tensor field equation from the exact project surface",
                "linearize, trace reverse, and extract the stationary 0i equation",
                "derive T^{0i}, T_0i, mass current, angular momentum, and discarded orders",
                "apply the boundary-fixed Green solution and compact-source current multipole expansion",
                "emit and freeze the computed exterior g_0i before oracle access",
                "derive the J-dependent orbit perturbation from S_pp and average it analytically",
                "compare frozen metric and nodal coefficients with the isolated oracles",
            ],
            "orbit_average_identity_to_derive_or_independently_check": (
                "<r^-3>=a^-3(1-e^2)^(-3/2)"
            ),
            "numerical_orbit_integration_authorized": False,
        },
        "required_controls": {
            "required_count": 8,
            "all_atomic_single_premise": all(
                row["changed_premise_count"] == 1 for row in REQUIRED_CONTROLS
            ),
            "rows": REQUIRED_CONTROLS,
        },
        "result_classification": {
            "maximum_success": (
                "BOUNDED_GR_ROTATING_WEAK_FIELD_RECOVERY_CANDIDATE_PENDING_RESULT_REVIEW"
            ),
            "success_requires": [
                "valid transport from the exact project surface to the tensor 0i equation",
                "computed exterior current-dipole coefficient equals the isolated oracle",
                "computed signed nodal coefficient equals the isolated oracle",
                "no fitting, target import, or observational calibration",
                "all eight controls produce their registered outcomes",
            ],
            "failure_classes": FAILURE_CLASSES,
            "failure_is_scientifically_usable": True,
            "success_accepted_without_separate_result_review": False,
        },
        "independent_review_acceptance_criteria": [
            "selected authority and all exact project bindings reproduce",
            "retained x^0=c t, (+,-,-,-), and SI policy is internally closed",
            "project source and standard-GR oracle are strictly separated",
            "stationary weak slow-rotation ordering and multipole truncation are complete",
            "T^{0i}, T_0i, j_m, J, and stress power counting are complete",
            "trace reversal, harmonic and residual gauge, and boundary rules are complete",
            "metric and nodal coefficient oracles are inaccessible as derivation inputs",
            "orbital route and signed node orientation are complete",
            "all eight controls are atomic and required",
            "no derivation, fitting, simulation, empirical analysis, or migration occurred",
        ],
        "benchmark_posture": {
            "benchmark_id": "GR-WEAK-ROTATING-SOURCE-BENCHMARK",
            "status": "REFERENCE_BOUND_FOR_SELECTED_GR_PREPARATION_ONLY",
            "LARES_2_data_analysis_authorized": False,
            "empirical_fit_authorized": False,
            "modified_gravity_constraint_claim_authorized": False,
        },
        "scope": {
            "packet_preparation_only": True,
            "derivation_executed": False,
            "coefficient_fitting_executed": False,
            "simulation_executed": False,
            "empirical_comparison_executed": False,
            "authoritative_equations_modified": False,
            "repository_migration_executed": False,
            "general_symbolic_tensor_tool_created": False,
            "Kerr_or_strong_field_claimed": False,
            "complete_post_Newtonian_framework_claimed": False,
            "gravitational_radiation_claimed": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "master_action_promoted": False,
            "R13_reopened": False,
            "SR_restoration_tooling_reopened": False,
            "external_comparator_activated": False,
            "automation_created": False,
        },
        "hard_stop": {
            "stopping_rule": (
                "Freeze one source-to-field-to-orbit derivation contract, two independent "
                "coefficient oracles, eight controls, exact failure classes, and stop for "
                "independent packet review."
            ),
            "bounded_derivation_authorized_now": False,
            "only_independent_packet_review_next": True,
            "accepted_review_may_authorize": (
                "one bounded analytic derivation on the six frozen transport stages plus comparison"
            ),
            "accepted_review_may_not_authorize": [
                "empirical analysis",
                "satellite data processing",
                "repository migration",
                "Kerr or full post-Newtonian expansion",
                "general symbolic infrastructure",
                "GR-pillar completion",
            ],
        },
        "claim_ceiling": (
            "Prepared derivation contract only. No gravitomagnetic or Lense-Thirring "
            "derivation, accepted recovery, empirical validation, GR-pillar completion, "
            "seam closure, or master-action promotion is created."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("GR weak rotating-source packet is stale or missing")
        packet = json.loads(raw)
        print(json.dumps({
            "controls": packet["required_controls"]["required_count"],
            "project_bindings": packet["project_source_bindings"]["required_count"],
            "status": "CHECKED",
            "target": packet["target"],
            "verdict": packet["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
