from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0.py"
)
CONTRACT_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0.md"
)
TARGET = "prepare_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0"
SELECTED_NEXT_TARGET = (
    "review_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0_result"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/GR_FIELD_EQUATION_SURFACE_FAILURE_RESPONSE_SELECTION_20260717_v0.json":
        "314f50857a2f6378b97d60449d518591e504193690100a9b9f543af3e26f3efa",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean":
        "da375e85850deb5d32da8a60c24d2fd7021c95143f8da036973d9575bd398458",
    "formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean":
        "8c7a6a3f3aa74f240945e3d2ac23a05c6e5fa6fa310977ba9c03db89f456d920",
    "formal/toe_formal/ToeFormal/QFT/DocumentMasterActionMapping.lean":
        "56ad40bfe0443a27b1c35142c52ae2430958dace2b8e62eef8e4e14e31e54ddf",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json":
        "fdadf7cb74401fd1d994841c9dbbbce5f6333e86d967d0aa349ed8987c183e8f",
    "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json":
        "7232643ab971c1f647421c81bb52ef37f0a636262bc172d3fffc73ed1c6a4d54",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json":
        "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v1.json":
        "2c6ea6800243635b05da4e89847f177987de6b9ccaeb6bbbe8c8e769a2a1a183",
    "formal/output/reports/gr_master_action_transport_attack_retry_packet_20260412_v0.json":
        "9e9e9d3436526346186873a3dd4bbfab2114db7914349c3a81cf36eb3a197267",
    CONTRACT_RELATIVE_PATH:
        "35b0de6f6f9b41ffdbf9e6544a65392ff2a2964589eb3d4dc3401f4ade7767c2",
}

ALLOWED_OUTCOMES = [
    "NATIVE_CONTINUUM_METRIC_VARIATION_CONTRACT_READY",
    "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
    "NO_NATIVE_CONTINUUM_METRIC_ACTION_SURFACE",
    "SUPPLIED_STANDARD_GR_VARIATIONAL_COMPARATOR_ONLY",
    "BLOCKED_SPINOR_METRIC_VARIATION_SURFACE",
]

FAIL_FAST_DIAGNOSTICS = [
    "ACTION_SOURCE_IDENTITY_FAILURE",
    "ACTION_SOURCE_BLENDING_FAILURE",
    "CK_FIREWALL_ACTION_SOURCE_CONFLICT",
    "ACTION_DIMENSION_AND_CONSTANT_CLOSURE_FAILURE",
    "CONTINUUM_DOMAIN_AND_FIELD_BUNDLE_FAILURE",
    "BLOCKED_SPINOR_METRIC_VARIATION_SURFACE",
    "HIDDEN_METRIC_DEPENDENCE_FAILURE",
    "BOUNDARY_VARIATION_CONTRACT_FAILURE",
    "STRESS_ENERGY_VARIATIONAL_DEFINITION_FAILURE",
    "REP32_CONTINUUM_RELATIONSHIP_FAILURE",
    "EINSTEIN_EQUATION_IMPORT_OR_ORACLE_LEAKAGE",
]

EXCLUDED_SURFACES = [
    {
        "surface_id": "ACTION_REP32",
        "relative_path": "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean",
        "classification": "STRUCTURAL_SCAFFOLD",
        "forbidden_inference": "continuum metric-action authority",
    },
    {
        "surface_id": "FIRST_VARIATION_REP32",
        "relative_path": "formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean",
        "classification": "DECLARED_COMPARISON_PAIRING",
        "forbidden_inference": "analytic first variation derived from actionRep32",
    },
    {
        "surface_id": "DOCUMENT_MASTER_ACTION_MAPPING",
        "relative_path": "formal/toe_formal/ToeFormal/QFT/DocumentMasterActionMapping.lean",
        "classification": "BOUNDED_FREE_SCALAR_TRANSLATION",
        "forbidden_inference": "global candidate metric variation",
    },
    {
        "surface_id": "PROVISIONAL_EINSTEIN_SCALAR_ROUTE",
        "relative_path": "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json",
        "classification": "PROVISIONAL_STANDARD_GR_SANDBOX",
        "forbidden_inference": "ToE-native Einstein equation",
    },
    {
        "surface_id": "STANDALONE_EINSTEIN_HILBERT_SECTOR",
        "classification": "STANDARD_GR_SUPPLIED_SECTOR",
        "forbidden_inference": "full-candidate or emergent ToE gravity",
    },
]

METRIC_DEPENDENCY_LEDGER = [
    {
        "sector": "geometry",
        "required_dependencies": [
            "e=sqrt(-g)",
            "R[e,omega(e)]",
            "Lambda",
            "curvature regularity",
        ],
        "preparation_finding": (
            "Einstein-Hilbert-shaped term is present; continuum domain, regularity, "
            "boundary, and common-unit contracts remain review obligations."
        ),
    },
    {
        "sector": "Dirac",
        "required_dependencies": [
            "e",
            "gamma^mu(e)",
            "omega_mu^ab(e)",
            "spinor adjoint",
            "gauge-plus-spin covariant derivative",
            "real Hermitian action density",
        ],
        "preparation_finding": (
            "The source shorthand does not select a spin structure, tetrad/spin "
            "connection contract, or exact Hermitian density."
        ),
    },
    {
        "sector": "gauge",
        "required_dependencies": [
            "e",
            "inverse metric contractions in F_mu_nu F^mu_nu",
            "gauge bundle and field domain",
            "SI or natural-unit normalization",
        ],
        "preparation_finding": (
            "The contraction is named; bundle, domain, and common action-unit "
            "normalization are not fixed by the source."
        ),
    },
    {
        "sector": "scalar",
        "required_dependencies": [
            "e",
            "inverse metric",
            "scalar derivative",
            "field inventory",
            "potential and regularity",
        ],
        "preparation_finding": (
            "The kinetic and potential shapes are named; field inventory, potential, "
            "regularity, and common units remain incomplete."
        ),
    },
    {
        "sector": "statistical",
        "required_dependencies": [
            "e",
            "rho scalar-versus-density type",
            "dimensionless logarithm argument",
            "reference measure or density scale",
        ],
        "preparation_finding": "The term is explicitly speculative and underdefined.",
    },
    {
        "sector": "C_k",
        "required_dependencies": ["none permitted under current admissibility-only policy"],
        "preparation_finding": (
            "The selected source displays multiplier action embedding, while later "
            "accepted policy forbids C_k action embedding and variation."
        ),
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"native GR packet authority hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    selection = json.loads(
        (REPO_ROOT / "formal/docs/release/GR_FIELD_EQUATION_SURFACE_FAILURE_RESPONSE_SELECTION_20260717_v0.json").read_text(encoding="utf-8")
    )
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("native GR packet did not consume the selected target")
    if selection.get("verdict") != (
        "SELECTED_GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE_PREPARATION"
    ):
        raise ValueError("native GR response-selection verdict mismatch")

    action_text = (
        REPO_ROOT / "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
    ).read_text(encoding="utf-8")
    for token in (
        "working-form artifact only",
        "explicitly non-canonical",
        "S_ToE[g, psi, A, phi, rho]",
        "sum_k lambda_k * C_k",
        "intended as Einstein-Hilbert-type bounded surface",
    ):
        if token not in action_text:
            raise ValueError(f"candidate-action source token missing: {token}")

    ck = json.loads(
        (REPO_ROOT / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json").read_text(encoding="utf-8")
    )
    if ck.get("all_C_k_families_admissibility_only") is not True:
        raise ValueError("C_k admissibility-only policy mismatch")
    if ck.get("C_k_action_embedding_selected") is not False:
        raise ValueError("C_k embedding unexpectedly selected")
    if ck.get("C_k_action_variation_authorized") is not False:
        raise ValueError("C_k variation unexpectedly authorized")

    rep32_text = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean"
    ).read_text(encoding="utf-8")
    for token in (
        "Rep32 action scaffold (structural-only)",
        "Leaves analytic derivation of `firstVariationRep32` from an action functional open",
    ):
        if token not in rep32_text:
            raise ValueError(f"Rep32 boundary token missing: {token}")

    stress = json.loads(
        (REPO_ROOT / "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json").read_text(encoding="utf-8")
    )
    for key in (
        "stress_energy_metric_variation_derived",
        "stress_energy_tetrad_variation_derived",
    ):
        if stress.get(key) is not False:
            raise ValueError(f"stress-energy nonderivation boundary mismatch: {key}")

    matter = json.loads(
        (REPO_ROOT / "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json").read_text(encoding="utf-8")
    )
    if matter.get("field_content_lagrangian_result") != (
        "FIELD_CONTENT_AND_LAGRANGIAN_BLOCKED_BY_MISSING_TOE_MATTER_MODEL"
    ):
        raise ValueError("QFT-GR matter action boundary mismatch")

    sandbox = json.loads(
        (REPO_ROOT / "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json").read_text(encoding="utf-8")
    )
    if sandbox.get("provisional_classical_sandbox_route_only") is not True:
        raise ValueError("provisional Einstein-scalar sandbox boundary mismatch")
    if sandbox.get("toe_native_matter_derivation_claimed") is not False:
        raise ValueError("sandbox unexpectedly claims ToE-native matter")

    retry = json.loads(
        (REPO_ROOT / "formal/output/reports/gr_master_action_transport_attack_retry_packet_20260412_v0.json").read_text(encoding="utf-8")
    )
    if retry["summary"].get("terminal_outcome") != (
        "GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
    ):
        raise ValueError("prior GR transport obstruction mismatch")

    contract = (REPO_ROOT / CONTRACT_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "Sole action candidate under review",
        "BLOCKED_SPINOR_METRIC_VARIATION_SURFACE",
        "CK_FIREWALL_ACTION_SOURCE_CONFLICT",
        "SEPARATE_STRUCTURAL_MODEL / CONTINUUM_RELATION_UNESTABLISHED",
        "This packet authorizes independent review only",
    ):
        if token not in contract:
            raise ValueError(f"human contract token missing: {token}")
    return rows


def build_packet() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native GR packet focused test missing")

    return {
        "schema_id": "GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "INDEPENDENT_PACKET_REVIEW_ONLY",
        "authority": {
            "consumed_selection_verdict": (
                "SELECTED_GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE_PREPARATION"
            ),
            "frozen_inputs": authority,
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
            "Does the project possess one sufficiently defined, project-authorized "
            "continuum gravitational action whose genuine gravitational-variable "
            "variation can produce a tensor field equation without importing the "
            "Einstein equation as an assumption?"
        ),
        "sole_action_candidate": {
            "source_id": "TOE_CANDIDATE_MASTER_ACTION_v0",
            "relative_path": "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md",
            "source_classification": "TOE_NATIVE_CANDIDATE",
            "current_authority": "WORKING_FORM_NONCANONICAL_UNPROMOTED",
            "variational_readiness": "UNADJUDICATED_PENDING_INDEPENDENT_REVIEW",
            "byte_exact_source_required": True,
            "term_insertion_removal_or_reclassification_allowed": False,
            "source_blending_allowed": False,
        },
        "excluded_or_comparator_surfaces": {
            "required_count": len(EXCLUDED_SURFACES),
            "rows": EXCLUDED_SURFACES,
        },
        "gravitational_variable_contract": {
            "full_candidate_variable": "covariant tetrad e^a_mu",
            "metric_relation": "g_mu_nu=eta_ab e^a_mu e^b_nu",
            "formulation": "SECOND_ORDER_TORSION_FREE_TETRAD",
            "spin_connection": "omega_mu^ab(e), metric compatible and not independently varied",
            "required_structures": [
                "invertible oriented tetrad",
                "spin structure and spinor bundle",
                "fixed flat gamma matrices gamma^a",
                "curved gamma matrices gamma^mu=e_a^mu gamma^a",
                "local Lorentz covariance",
                "exact fields held fixed under tetrad variation",
                "real Hermitian Dirac action density",
            ],
            "metric_symbol_only_full_candidate_variation_allowed": False,
            "metric_only_bosonic_subaction_may_equal_full_candidate": False,
            "missing_contract_diagnostic": "BLOCKED_SPINOR_METRIC_VARIATION_SURFACE",
            "route_authorized_as_complete_before_review": False,
        },
        "continuum_domain_and_units_gate": {
            "required_domain": "oriented four-dimensional Lorentzian manifold M",
            "retained_signature": "(+,-,-,-)",
            "retained_temporal_coordinate": "x^0=c t",
            "required_field_data": [
                "tetrad and metric differentiability/nondegeneracy class",
                "field bundles and admissible configurations",
                "one common action-unit convention",
                "dimensionally homogeneous retained integrand terms",
            ],
            "source_unit_posture": "NATURAL_UNIT_LIKE_SHORTHAND_NOT_EXPLICITLY_CLOSED",
            "dimensionful_target": "SI",
            "constant_insertion_or_field_rescaling_during_review_allowed": False,
            "missing_closure_outcome": "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
        },
        "metric_dependency_ledger": {
            "required_count": len(METRIC_DEPENDENCY_LEDGER),
            "rows": METRIC_DEPENDENCY_LEDGER,
            "hidden_dependency_allowed": False,
            "stress_tensor_substitution_for_missing_dependency_allowed": False,
        },
        "boundary_contract": {
            "selected_route": "LOCAL_BULK_COMPACT_SUPPORT",
            "variation": "delta e^a_mu in C_c^infinity(interior(M))",
            "purpose": "make total-divergence terms vanish in the local bulk field-equation test",
            "GHY_term_added": False,
            "finite_boundary_variational_principle_claimed": False,
            "silent_boundary_term_discard_allowed": False,
            "future_finite_boundary_route_requires_separate_authority": True,
        },
        "matter_source_contract": {
            "metric_subroute_definition": (
                "T_mu_nu=-(2/sqrt(-g)) delta S_m/delta g^mu_nu"
            ),
            "selected_tetrad_definition": (
                "tau_a^mu=(1/e) delta S_m/delta e^a_mu"
            ),
            "consistency_target": "tau_a^mu=T^mu_nu e_a_nu",
            "local_Lorentz_and_symmetry_obligations_required": True,
            "retained_T_A_T_psi_T_total_classification": "COMPARISON_POLICIES_NOT_VARIATION_DERIVED",
            "previous_stress_tensor_may_replace_variation": False,
        },
        "C_k_firewall": {
            "retained_policy": "ADMISSIBILITY_AUDIT_ONLY",
            "action_embedding_authorized": False,
            "variation_authorized": False,
            "source_contribution_authorized": False,
            "multiplier_or_penalty_dynamics_authorized": False,
            "selected_source_contains_displayed_C_k_multiplier_term": True,
            "preparation_finding": "REGISTERED_SOURCE_POLICY_CONFLICT",
            "packet_rewrites_action": False,
            "required_review_diagnostic_if_unresolved": "CK_FIREWALL_ACTION_SOURCE_CONFLICT",
        },
        "Rep32_relationship": {
            "classification": "SEPARATE_STRUCTURAL_MODEL_CONTINUUM_RELATION_UNESTABLISHED",
            "discretization_theorem_available": False,
            "reduction_theorem_available": False,
            "convergence_theorem_available": False,
            "analytic_first_variation_from_actionRep32_available": False,
            "prior_transport_result": "GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT",
            "shared_action_terminology_grants_continuum_authority": False,
        },
        "independent_review_protocol": {
            "fail_fast": True,
            "diagnostics_in_order": FAIL_FAST_DIAGNOSTICS,
            "passing_later_gate_repairs_earlier_failure": False,
            "allowed_outcomes": ALLOWED_OUTCOMES,
            "exactly_one_terminal_outcome_required": True,
            "acceptance_criteria": [
                "sole action source and exclusions reproduce byte-exactly",
                "no action-source blending occurs",
                "covariant tetrad route is complete and project-authorized",
                "all retained sectors close field, domain, unit, and tetrad dependence",
                "compact-support boundary contract suffices for the claimed local bulk scope",
                "stress energy is generated by the selected variational definition",
                "C_k source-policy conflict is resolved by pre-existing authority, not packet editing",
                "Rep32 remains within structural authority",
                "Einstein equation and provisional sandbox never enter as native inputs",
                "no metric/tetrad variation or downstream GR calculation occurred",
            ],
        },
        "hard_stop": {
            "stopping_rule": (
                "Freeze one exact candidate, one proposed tetrad-route contract, complete "
                "dependency and boundary gates, five outcomes, and stop for independent review."
            ),
            "only_independent_packet_review_next": True,
            "variation_authorized_now": False,
            "accepted_ready_review_may_authorize": (
                "one separate bounded local bulk tetrad-variation attempt"
            ),
            "accepted_ready_review_does_not_establish_tensor_equation": True,
        },
        "scope": {
            "packet_preparation_only": True,
            "metric_variation_executed": False,
            "tetrad_variation_executed": False,
            "stress_energy_calculated": False,
            "Einstein_equation_imported": False,
            "Einstein_equation_derived": False,
            "standard_GR_comparator_activated": False,
            "weak_field_reduction_executed": False,
            "gravitomagnetic_calculation_executed": False,
            "rotating_source_lane_reopened": False,
            "C_k_action_embedding_executed": False,
            "C_k_variation_executed": False,
            "candidate_action_rewritten": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "repository_migration_executed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Prepared existence-and-variation-contract packet only. One exact candidate "
            "action, a proposed tetrad route, complete readiness gates, five terminal "
            "outcomes, and strict nonclaims are frozen for independent review. No continuum "
            "tensor field surface, stress tensor, Einstein equation, GR recovery, seam "
            "closure, master-action promotion, empirical result, or automation is created."
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
            raise SystemExit("native continuum variation packet is stale or missing")
        packet = json.loads(raw)
        print(json.dumps({
            "allowed_outcomes": len(packet["independent_review_protocol"]["allowed_outcomes"]),
            "dependency_rows": packet["metric_dependency_ledger"]["required_count"],
            "diagnostics": len(packet["independent_review_protocol"]["diagnostics_in_order"]),
            "status": "CHECKED",
            "verdict": packet["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
