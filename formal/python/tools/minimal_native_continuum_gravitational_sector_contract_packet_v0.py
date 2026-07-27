from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_"
    "20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_minimal_native_continuum_gravitational_sector_contract_packet_v0.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_"
    "20260717_v0.md"
)
TARGET = "prepare_minimal_native_continuum_gravitational_sector_contract_packet_v0"
SELECTED_NEXT_TARGET = (
    "review_minimal_native_continuum_gravitational_sector_contract_packet_v0_result"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/NATIVE_CONTINUUM_ACTION_ABSENCE_SCIENTIFIC_TARGET_SELECTION_20260717_v0.json":
        "86717db3c1a23c8d9562a398db847668d9422fef0261e682038d25e531d9abab",
    "formal/python/tools/native_continuum_action_absence_scientific_target_selection_v0.py":
        "1c91e2aae12390876810d698030d9ec61a3bfbd2eb1fc813e0b27ff52a05421a",
    "formal/python/tests/test_native_continuum_action_absence_scientific_target_selection_v0.py":
        "ecc8af33edc2d9e944eeb9c1af5fd43fffd4ffe7ae2795ca97869009f1dd2610",
    "formal/toe_formal/ToeFormal/Derivation/NativeContinuumActionAbsenceScientificTargetSelectionV0.lean":
        "95e66c9f1a33ad4c02673af2eaa9355d5afa83aacdb6a7f48847a9b3e967e8a9",
    "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_REVIEW_20260717_v0.json":
        "66ed74e9264c82eaa9715cc0369020f93b7956f9f3aa2f9b8b6abb5141fe2e64",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v3.json":
        "0dbe441d78de6eba0fe006f7b6b280b655a3feae3e1f9d66775eefae9e49a3b1",
    "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean":
        "da375e85850deb5d32da8a60c24d2fd7021c95143f8da036973d9575bd398458",
    "formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean":
        "8c7a6a3f3aa74f240945e3d2ac23a05c6e5fa6fa310977ba9c03db89f456d920",
    "formal/toe_formal/ToeFormal/QFT/DocumentMasterActionMapping.lean":
        "56ad40bfe0443a27b1c35142c52ae2430958dace2b8e62eef8e4e14e31e54ddf",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json":
        "de305a72dc522fe807c037bbe7980d96e3308d0547645ccb9939d1889720d987",
    "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.json":
        "4b894a31d1eb9ea29b06f70934913f42a007db31bbf3ac75f2ab8411674d1939",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json":
        "fdadf7cb74401fd1d994841c9dbbbce5f6333e86d967d0aa349ed8987c183e8f",
    "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json":
        "7232643ab971c1f647421c81bb52ef37f0a636262bc172d3fffc73ed1c6a4d54",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json":
        "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    PACKET_RELATIVE_PATH:
        "5fc170073b11907bb14c05984d577c9b68e0a8d6ebfcf8c7fedf081a4ef292d8",
}

PROVENANCE_CLASSES = [
    "DERIVED_FROM_PROJECT_PRINCIPLE",
    "POSTULATED_NATIVE_CANDIDATE",
    "SUPPLIED_STANDARD_PHYSICS_BASELINE",
]

CANDIDATE_COMPLETENESS_GATES = [
    "one provenance class",
    "one project principle or explicit postulate record",
    "one exact metric field and continuum domain",
    "one complete local gravitational scalar density",
    "all couplings constants and SI dimensions",
    "action-level symmetry contract",
    "compact-support local boundary and variation contract",
    "one selected matter functional or authorized bounded matter class",
    "variational stress-energy definition",
    "external C_k firewall",
    "explicit nontransport from v0 Rep32 and supplied comparators",
    "recovery and discriminator obligations",
]

RECOVERY_LADDER = [
    "well-defined continuum action functional",
    "valid local metric variation",
    "symmetric tensor field equation",
    "covariant source conservation",
    "stationary weak-field 00 equation",
    "recovery of bounded Newton-Poisson surface",
    "stationary weak-field 0i equation",
    "exterior gravitomagnetic field",
    "Lense-Thirring coefficient",
    "later radiation and stronger-field tests",
]

ALLOWED_OUTCOMES = [
    "MINIMAL_NATIVE_GRAVITATIONAL_ACTION_CONTRACT_READY",
    "SUPPLIED_EINSTEIN_HILBERT_SECTOR_ONLY",
    "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
    "BLOCKED_MATTER_COUPLING_UNDEFINED",
    "BLOCKED_DIMENSIONAL_OR_BOUNDARY_CONTRACT",
    "REQUIREMENTS_NO_GO_ROUTE_RECOMMENDED",
]

ATOMIC_CONTROLS = [
    {
        "control_id": "CTRL_RELABELED_EINSTEIN_HILBERT_NATIVE",
        "mutation_count": 1,
        "first_diagnostic": "PROVENANCE_CLASSIFICATION_FAILURE",
    },
    {
        "control_id": "CTRL_UNDEFINED_NATIVE_CORRECTION",
        "mutation_count": 1,
        "first_diagnostic": "CANDIDATE_COMPLETENESS_FAILURE",
    },
    {
        "control_id": "CTRL_CK_EMBEDDED_OR_PENALIZED",
        "mutation_count": 1,
        "first_diagnostic": "CK_FIREWALL_VIOLATION",
    },
    {
        "control_id": "CTRL_RETAINED_STRESS_INSERTED_NOT_DERIVED",
        "mutation_count": 1,
        "first_diagnostic": "MATTER_SOURCE_DERIVATION_FAILURE",
    },
    {
        "control_id": "CTRL_REP32_NAME_IMPLIES_CONTINUUM_AUTHORITY",
        "mutation_count": 1,
        "first_diagnostic": "REP32_CONTINUUM_TRANSPORT_FAILURE",
    },
    {
        "control_id": "CTRL_ONE_SI_DIMENSION_OMITTED",
        "mutation_count": 1,
        "first_diagnostic": "DIMENSIONAL_CONTRACT_FAILURE",
    },
    {
        "control_id": "CTRL_BOUNDARY_PRESCRIPTION_OMITTED",
        "mutation_count": 1,
        "first_diagnostic": "BOUNDARY_VARIATION_CONTRACT_FAILURE",
    },
    {
        "control_id": "CTRL_UNSELECTED_TETRAD_SPINOR_IMPORT",
        "mutation_count": 1,
        "first_diagnostic": "MINIMAL_FIELD_SCOPE_FAILURE",
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"minimal native GR packet hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    selection = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/NATIVE_CONTINUUM_ACTION_ABSENCE_"
            "SCIENTIFIC_TARGET_SELECTION_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("minimal native GR packet did not consume selection target")
    if selection["ranking"].get("selected_candidate_id") != (
        "DEFINE_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR"
    ):
        raise ValueError("minimal native GR selection winner mismatch")
    if selection["scope"].get("native_gravitational_action_defined") is not False:
        raise ValueError("selection unexpectedly defined a gravitational action")

    action_review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_"
            "AUTHORITY_RECONCILIATION_PACKET_REVIEW_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if action_review.get("verdict") != "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY":
        raise ValueError("historical master-action status mismatch")
    if action_review["retained_status"].get(
        "native_executable_continuum_action"
    ) != "NOT_YET_DEFINED":
        raise ValueError("native executable action unexpectedly exists")

    sr = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_"
            "CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v3.json"
        ).read_text(encoding="utf-8")
    )
    if sr["retained_results"].get("physical_convention") != (
        "x^0=c t; (+,-,-,-); SI"
    ):
        raise ValueError("retained SR physical convention mismatch")
    if sr["scope_and_authorization"].get("automatic_v4_authorized") is not False:
        raise ValueError("closed SR restoration tooling unexpectedly reopened")

    ck = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_"
            "AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json"
        ).read_text(encoding="utf-8")
    )
    if ck.get("all_C_k_families_admissibility_only") is not True:
        raise ValueError("C_k firewall status mismatch")
    if ck.get("C_k_action_embedding_selected") is not False:
        raise ValueError("C_k embedding unexpectedly selected")

    stress = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_"
            "DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json"
        ).read_text(encoding="utf-8")
    )
    if stress.get("stress_energy_derived") is not False:
        raise ValueError("retained stress policy unexpectedly variation-derived")
    if stress.get("stress_energy_metric_variation_derived") is not False:
        raise ValueError("metric-derived stress status mismatch")

    matter = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_"
            "CANDIDATE_PACKET_20260616_v0.json"
        ).read_text(encoding="utf-8")
    )
    if matter.get("matter_field_content_selected") is not False:
        raise ValueError("matter field content unexpectedly selected")
    if matter.get("lagrangian_density_selected") is not False:
        raise ValueError("matter Lagrangian unexpectedly selected")

    comparator = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_"
            "ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json"
        ).read_text(encoding="utf-8")
    )
    if comparator.get("provisional_classical_sandbox_route_only") is not True:
        raise ValueError("Einstein-scalar comparator classification mismatch")

    weak_field = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean"
    ).read_text(encoding="utf-8")
    for token in ("Structural-only theorem surface", "No analytic discharge is claimed"):
        if token not in weak_field:
            raise ValueError(f"GR01 structural boundary token missing: {token}")

    packet = (REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "`S_m[g, chi]` is contract notation only",
        "Formula identity does not determine provenance",
        "The first route is limited to local bulk field equations",
        "No proposed minimal gravitational action may contain",
        "exactly one of the six outcomes",
        "No action or field",
    ):
        if token not in packet:
            raise ValueError(f"human minimal native GR packet token missing: {token}")
    return rows


def build_packet() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("minimal native GR packet focused test missing")
    if len(PROVENANCE_CLASSES) != 3:
        raise ValueError("provenance classifier count mismatch")
    if len(CANDIDATE_COMPLETENESS_GATES) != 12:
        raise ValueError("candidate completeness gate count mismatch")
    if len(RECOVERY_LADDER) != 10:
        raise ValueError("recovery ladder count mismatch")
    if len(ALLOWED_OUTCOMES) != 6:
        raise ValueError("packet outcome count mismatch")
    if len(ATOMIC_CONTROLS) != 8 or not all(
        row["mutation_count"] == 1 for row in ATOMIC_CONTROLS
    ):
        raise ValueError("atomic control contract mismatch")

    return {
        "schema_id": (
            "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_"
            "20260717_v0"
        ),
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "INDEPENDENT_MINIMAL_NATIVE_GRAVITATIONAL_CONTRACT_REVIEW_ONLY"
        ),
        "authority": {
            "selection_verdict": (
                "SELECTED_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_PREPARATION"
            ),
            "historical_master_action_status": "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
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
            "Can one complete project-owned continuum gravitational action contract be "
            "specified without rebuilding the ToE or relabeling standard GR as native?"
        ),
        "provenance_contract": {
            "class_count": len(PROVENANCE_CLASSES),
            "classes": PROVENANCE_CLASSES,
            "exactly_one_initial_class_required": True,
            "formula_identity_determines_provenance": False,
            "renamed_Einstein_Hilbert_is_native": False,
            "project_principle_must_predate_derived_formula": True,
            "postulated_candidate_must_be_labeled_postulate": True,
        },
        "minimal_field_contract": {
            "gravitational_field": "g_mu_nu",
            "field_count": 1,
            "spacetime_dimension": 4,
            "manifold": "ORIENTABLE_TIME_ORIENTABLE_LORENTZIAN_M",
            "signature": "(+,-,-,-)",
            "coordinate_policy": "x^0=ct",
            "selected_route": "LOCAL_METRIC_THEORY",
            "nonlocal_route_selected": False,
            "tetrad_selected": False,
            "independent_spin_connection_selected": False,
            "full_Dirac_geometry_selected": False,
            "generic_matter_symbol": "chi_CONTRACT_NOTATION_ONLY",
        },
        "symmetry_contract": {
            "diffeomorphism_covariance_required": True,
            "coordinate_independent_scalar_action_required": True,
            "locality_required_for_bounded_route": True,
            "parity_even_baseline": True,
            "time_reversal_even_baseline": True,
            "off_shell_identity_required": True,
            "notation_alone_proves_symmetry": False,
            "symmetry_breaking_requires_new_selection": True,
        },
        "dimensional_contract": {
            "target_units": "SI",
            "action_dimension": "J s",
            "S_over_hbar_dimensionless": True,
            "x0_policy": "x^0=ct",
            "manual_equation_specific_restoration_required": True,
            "automated_SR_restoration_tool_reopened": False,
            "all_couplings_fields_curvatures_and_new_scales_must_be_typed": True,
        },
        "boundary_variation_contract": {
            "claim_scope": "LOCAL_BULK_FIELD_EQUATIONS_ONLY",
            "region": "OPEN_OMEGA_COMPACTLY_CONTAINED_IN_M",
            "variation_class": "SMOOTH_COMPACTLY_SUPPORTED_METRIC_VARIATIONS",
            "global_variational_principle_claimed": False,
            "finite_boundary_claim_authorized": False,
            "boundary_terms_may_be_silently_discarded_elsewhere": False,
        },
        "matter_source_contract": {
            "S_m_g_chi_is_existing_action": False,
            "S_m_g_chi_status": "CONTRACT_NOTATION_ONLY",
            "matter_field_content_selected_in_current_authority": False,
            "matter_lagrangian_selected_in_current_authority": False,
            "required_definition": (
                "T_mu_nu=-(2/sqrt(-g))*delta S_m/delta g^mu_nu"
            ),
            "retained_stress_policies_are_oracles_only": True,
            "inserting_retained_stress_as_input_allowed": False,
            "T_0i_representability_required": True,
            "covariant_source_conservation_condition_required": True,
        },
        "C_k_firewall": {
            "classification": "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY",
            "action_embedding_allowed": False,
            "variation_allowed": False,
            "multiplier_allowed": False,
            "quadratic_penalty_allowed": False,
            "historical_v0_modified": False,
        },
        "existing_object_boundaries": {
            "historical_master_action_v0": "SCHEMATIC_SECTOR_INVENTORY_ONLY",
            "Rep32": "SEPARATE_STRUCTURAL_MODEL_NO_CONTINUUM_TRANSPORT",
            "DocumentMasterActionMapping": "BOUNDED_MAPPING_NO_GLOBAL_TRANSPORT",
            "Einstein_scalar_sandbox": "SUPPLIED_PROVISIONAL_COMPARATOR_ONLY",
            "GR01": "BOUNDED_DISCRETE_NEWTON_POISSON_OBLIGATION_ONLY",
            "authority_flows_automatically": False,
        },
        "candidate_completeness_contract": {
            "gate_count": len(CANDIDATE_COMPLETENESS_GATES),
            "gates": CANDIDATE_COMPLETENESS_GATES,
            "undefined_correction_fails_before_variation": True,
            "nonstandard_term_required_fields": [
                "tensorial construction and domain",
                "selecting principle or postulated reason",
                "allowed symmetries",
                "coupling dimensions",
                "added degrees of freedom and derivative order",
                "vanishing or decoupling limit",
                "possible observable discriminator",
            ],
        },
        "recovery_contract": {
            "stage_count": len(RECOVERY_LADDER),
            "stages": RECOVERY_LADDER,
            "executed_stage_count": 0,
            "earlier_failure_blocks_later_stages": True,
        },
        "outcome_contract": {
            "outcome_count": len(ALLOWED_OUTCOMES),
            "exactly_one_required": True,
            "allowed_outcomes": ALLOWED_OUTCOMES,
            "selection_base_outcome_count": 4,
            "fail_closed_refinement_count": 2,
        },
        "control_contract": {
            "control_count": len(ATOMIC_CONTROLS),
            "all_single_mutation": True,
            "rows": ATOMIC_CONTROLS,
            "controls_executed_by_preparation": False,
            "independent_review_execution_required": True,
        },
        "scope": {
            "packet_preparation_only": True,
            "gravitational_action_proposed_selected_or_derived": False,
            "successor_master_action_prepared_or_created": False,
            "metric_tetrad_spin_or_matter_variation_executed": False,
            "stress_energy_derived": False,
            "Einstein_equation_imported_or_derived": False,
            "Newton_Poisson_calculation_executed": False,
            "tensor_or_weak_field_calculation_executed": False,
            "gravitomagnetic_calculation_executed": False,
            "C_k_embedded_or_varied": False,
            "Rep32_continuum_transport_claimed": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "repository_migration_executed": False,
            "general_symbolic_tooling_created": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Prepared contract only. Provenance, metric-only field scope, symmetries, "
            "SI dimensions, compact-support local variation, variational matter sourcing, "
            "external C_k policy, existing-object nontransport, twelve completeness gates, "
            "ten recovery stages, six outcomes, and eight atomic review controls are frozen. "
            "No gravitational action, successor master action, variation, stress-energy, "
            "tensor field equation, GR recovery, promotion, empirical result, tooling lane, "
            "or automation is created."
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
            raise SystemExit("minimal native GR contract packet is stale or missing")
        packet = json.loads(raw)
        print(json.dumps({
            "completeness_gates": packet["candidate_completeness_contract"]["gate_count"],
            "controls": packet["control_contract"]["control_count"],
            "outcomes": packet["outcome_contract"]["outcome_count"],
            "recovery_stages": packet["recovery_contract"]["stage_count"],
            "status": "CHECKED",
            "verdict": packet["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
