from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "20260718_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_gravitational_principle_requirements_and_action_selection_packet_v0.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "20260718_v0.md"
)
TARGET = (
    "prepare_native_gravitational_principle_requirements_and_action_selection_packet_v0"
)
SELECTED_NEXT_TARGET = (
    "review_native_gravitational_principle_requirements_and_action_selection_packet_v0_result"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0.json":
        "e2468ea98384383654efe73dd054f5149beb6d4a62db45123109d962999dea66",
    "formal/python/tools/native_gravitational_principle_response_selection_v0.py":
        "7b9788a1e23fe30a5bfc67ac2c0f84175178310ca7893def9533477413d029c1",
    "formal/python/tests/test_native_gravitational_principle_response_selection_v0.py":
        "0a2ce3bb4c19b3fcf0fdacae3d87fac1db72649b29e4e3c3115ce1c130b8637f",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleResponseSelectionV0.lean":
        "517d562ece95da2228c3423697fbcdfb4e3b1d365197b8a4b84c0f7d699e4a2e",
    "formal/docs/lanes/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_REVIEW_20260717_v0.md":
        "554e18d20bb3d6f2076cb4d6ea6c86480ee46d11f39f87c01673f37dfc8ec70c",
    "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_REVIEW_20260717_v0.json":
        "6b902c6c620e15aa68898ae271e2de787186c9ef051e5c16c69edd0ea703ccfd",
    "formal/python/tools/minimal_native_continuum_gravitational_sector_contract_packet_review_v0.py":
        "ef92c485d3543d349af76ea3469027d71c2056e66e02c9cc259101c63955975e",
    "formal/python/tests/test_minimal_native_continuum_gravitational_sector_contract_packet_review_v0.py":
        "5f0a07fc4aa5438a811228e058062952bbdec09b362b5a5320e06307d3c77a80",
    "formal/toe_formal/ToeFormal/Derivation/MinimalNativeContinuumGravitationalSectorContractPacketReviewV0.lean":
        "7e4de22622b0d6c74645777f4899ee5f9ee6c0b04b4ca0fc9018a20a49cd0fec",
    "formal/docs/lanes/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.md":
        "5fc170073b11907bb14c05984d577c9b68e0a8d6ebfcf8c7fedf081a4ef292d8",
    "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json":
        "2031bc50487bdcd07c5a18dcf2fcdddb611337b5150fbbf416b0d6ab0b9d86d4",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json":
        "de305a72dc522fe807c037bbe7980d96e3308d0547645ccb9939d1889720d987",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json":
        "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json":
        "fdadf7cb74401fd1d994841c9dbbbce5f6333e86d967d0aa349ed8987c183e8f",
    "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json":
        "7232643ab971c1f647421c81bb52ef37f0a636262bc172d3fffc73ed1c6a4d54",
    PACKET_RELATIVE_PATH:
        "b74f94c30298d81671157213845bf761631fb9cc39a8d102b93c236e8199056f",
}

STATEMENT_CLASSES = [
    "ACCEPTED_PROJECT_REQUIREMENT",
    "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
    "NEW_PROPOSED_POSTULATE",
]

REQUIREMENT_CLASSES = [
    "ACTION_FORM_CONSTRAINT",
    "FIELD_CONTENT_CONSTRAINT",
    "SYMMETRY_CONSTRAINT",
    "VARIATIONAL_CONSTRAINT",
    "RECOVERY_CONSTRAINT",
    "STABILITY_CONSTRAINT",
    "SOURCE_COUPLING_CONSTRAINT",
    "OBSERVATIONAL_CONSTRAINT",
    "EXTERNAL_ADMISSIBILITY_CONSTRAINT",
]

REQUIREMENTS = [
    {
        "requirement_id": "R1_DIMENSION",
        "statement": "four-dimensional continuum target",
        "authority_status": "FROZEN_EVALUATION_ENVELOPE_ASSUMPTION",
        "constraint_classes": ["FIELD_CONTENT_CONSTRAINT"],
        "mathematical_scope": "dim(M)=4",
        "necessity": "REQUIRED_INSIDE_FROZEN_ENVELOPE",
        "source_bindings": [
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json"
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "may exclude other dimensions but selects no 4D invariant",
    },
    {
        "requirement_id": "R2_METRIC_ONLY",
        "statement": "one metric gravitational variable",
        "authority_status": "FROZEN_MINIMAL_SCOPE_ASSUMPTION",
        "constraint_classes": ["FIELD_CONTENT_CONSTRAINT"],
        "mathematical_scope": "gravitational field g_mu_nu only",
        "necessity": "REQUIRED_INSIDE_FROZEN_ENVELOPE",
        "source_bindings": [
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json"
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "outside-scope classification is not refutation",
    },
    {
        "requirement_id": "R3_LOCALITY",
        "statement": "local action in the bounded route",
        "authority_status": "FROZEN_MINIMAL_SCOPE_ASSUMPTION",
        "constraint_classes": ["ACTION_FORM_CONSTRAINT"],
        "mathematical_scope": "local scalar density on M",
        "necessity": "REQUIRED_INSIDE_FROZEN_ENVELOPE",
        "source_bindings": [
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json"
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "locality is not a derived native principle",
    },
    {
        "requirement_id": "R4_DIFF_COVARIANCE",
        "statement": "diffeomorphism-covariant scalar action",
        "authority_status": "ACCEPTED_EVALUATION_REQUIREMENT",
        "constraint_classes": ["SYMMETRY_CONSTRAINT"],
        "mathematical_scope": "coordinate-independent scalar action",
        "necessity": "REQUIRED_FOR_EVALUATED_CANDIDATE",
        "source_bindings": [
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json"
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "covariance alone does not prove action uniqueness",
    },
    {
        "requirement_id": "R5_CK_FIREWALL",
        "statement": "C_k remains external to gravitational dynamics",
        "authority_status": "ACCEPTED_GLOBAL_PROJECT_POLICY",
        "constraint_classes": ["EXTERNAL_ADMISSIBILITY_CONSTRAINT"],
        "mathematical_scope": "no C_k embedding multiplier penalty or variation",
        "necessity": "REQUIRED",
        "source_bindings": [
            "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json"
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "excludes C_k dynamics but selects no remaining invariant",
    },
    {
        "requirement_id": "R6_LOCAL_VARIATION",
        "statement": "smooth compactly supported local metric variations",
        "authority_status": "ACCEPTED_LOCAL_BULK_REVIEW_CONTRACT",
        "constraint_classes": ["VARIATIONAL_CONSTRAINT"],
        "mathematical_scope": "delta g compactly supported in Omega compactly contained in M",
        "necessity": "REQUIRED_FOR_LOCAL_BULK_COMPARISON",
        "source_bindings": [
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json"
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "does not establish a global boundary theory",
    },
    {
        "requirement_id": "R7_SOURCE_COMPATIBILITY",
        "statement": "generic variational matter source and conservation compatibility",
        "authority_status": "ACCEPTED_CANDIDATE_EVALUATION_REQUIREMENT",
        "constraint_classes": ["SOURCE_COUPLING_CONSTRAINT"],
        "mathematical_scope": "T_mu_nu=-(2/sqrt(-g))*delta S_m/delta g^mu_nu",
        "necessity": "REQUIRED_FOR_SOURCE_COUPLED_CANDIDATE",
        "source_bindings": [
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json",
            "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json",
            "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json",
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "matter action remains undefined and stress policies are oracles only",
    },
    {
        "requirement_id": "R8_NEWTON_POISSON",
        "statement": "recover the bounded Newton-Poisson surface",
        "authority_status": "RETAINED_RECOVERY_OBLIGATION",
        "constraint_classes": ["RECOVERY_CONSTRAINT"],
        "mathematical_scope": "stationary weak-field 00 limit",
        "necessity": "REQUIRED_FOR_FUTURE_RECOVERY",
        "source_bindings": [
            "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean",
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json",
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "shared weak-field limit is not an action uniqueness theorem",
    },
    {
        "requirement_id": "R9_MOMENTUM_CURRENT",
        "statement": "represent conserved T_0i and a weak-field 0i response",
        "authority_status": "RETAINED_DOWNSTREAM_RECOVERY_OBLIGATION",
        "constraint_classes": ["SOURCE_COUPLING_CONSTRAINT", "RECOVERY_CONSTRAINT"],
        "mathematical_scope": "stationary momentum-current source sector",
        "necessity": "REQUIRED_FOR_FUTURE_GRAVITOMAGNETISM",
        "source_bindings": [
            "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json",
            "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json",
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "recovery target not yet derived",
    },
    {
        "requirement_id": "R10_STABILITY_NO_FIT",
        "statement": "stable weak-field behavior and no fitting of recovery coefficients",
        "authority_status": "SELECTED_EVALUATION_OBLIGATION",
        "constraint_classes": ["STABILITY_CONSTRAINT", "OBSERVATIONAL_CONSTRAINT"],
        "mathematical_scope": "candidate weak-field and recovery comparison",
        "necessity": "REQUIRED_AFTER_CANDIDATE_EXISTS",
        "source_bindings": [
            "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0.json"
        ],
        "selection_power_status": "NOT_ANALYZED",
        "initial_boundary": "not a candidate premise before a candidate exists",
    },
]

ACTION_FAMILIES = [
    {
        "family_id": "F_EH",
        "structural_class": "local metric action linear in curvature with optional cosmological term",
        "envelope_status": "PRIMARY_METRIC_LOCAL_ENVELOPE",
        "comparison_only": True,
    },
    {
        "family_id": "F_FR",
        "structural_class": "local metric f(R) excluding the purely linear representative",
        "envelope_status": "PRIMARY_METRIC_LOCAL_ENVELOPE",
        "comparison_only": True,
    },
    {
        "family_id": "F_QUADRATIC",
        "structural_class": "local metric independent quadratic Ricci or Riemann invariants",
        "envelope_status": "PRIMARY_METRIC_LOCAL_ENVELOPE",
        "comparison_only": True,
    },
    {
        "family_id": "F_EXTRA_FIELD",
        "structural_class": "metric plus additional fundamental scalar vector or tensor",
        "envelope_status": "OUTSIDE_FROZEN_METRIC_ONLY_SCOPE",
        "comparison_only": True,
    },
    {
        "family_id": "F_NONLOCAL",
        "structural_class": "explicitly nonlocal metric action",
        "envelope_status": "OUTSIDE_FROZEN_LOCAL_SCOPE",
        "comparison_only": True,
    },
    {
        "family_id": "F_CONNECTION_TORSION",
        "structural_class": "independent connection Palatini or torsion family",
        "envelope_status": "OUTSIDE_FROZEN_METRIC_ONLY_SCOPE",
        "comparison_only": True,
    },
    {
        "family_id": "F_EQUIVALENCE_PROBE",
        "structural_class": "boundary algebraic or four-dimensional topological variants",
        "envelope_status": "EQUIVALENCE_CONTROL_NOT_SEPARATE_CANDIDATE",
        "comparison_only": True,
    },
]

MATRIX_CELL_VALUES = [
    "SURVIVES",
    "ELIMINATED",
    "OUTSIDE_ENVELOPE",
    "EQUIVALENT_REPRESENTATIVE",
    "REQUIRES_SUPPLIED_ASSUMPTION",
    "NOT_EVALUATED",
]

SELECTION_POWER_VALUES = [
    "ELIMINATES_FAMILY",
    "FIXES_COEFFICIENT",
    "RESTRICTS_FIELD_CONTENT",
    "RESTRICTS_DERIVATIVE_ORDER",
    "RESTRICTS_SOLUTIONS_ONLY",
    "RECOVERY_LIMIT_ONLY",
    "REDUNDANT_OR_DEPENDENT",
    "NO_DEMONSTRATED_SELECTION_POWER",
]

DEPENDENCY_VALUES = [
    "INDEPENDENT_FOR_FROZEN_ANALYSIS",
    "LOGICALLY_IMPLIES_UNDER_DECLARED_ASSUMPTIONS",
    "PARTIALLY_OVERLAPS",
    "REDUNDANT_DUPLICATE",
    "DEPENDENCE_UNRESOLVED",
]

DEPENDENCY_PROBES = [
    {
        "probe_id": "D_DIFF_BIANCHI_CONSERVATION",
        "members": ["R4_DIFF_COVARIANCE", "R7_SOURCE_COMPATIBILITY"],
        "required_posture": "DEPENDENCE_MUST_BE_DERIVED_NOT_ASSUMED_IDENTICAL",
    },
    {
        "probe_id": "D_00_VERSUS_0I",
        "members": ["R8_NEWTON_POISSON", "R9_MOMENTUM_CURRENT"],
        "required_posture": "INDEPENDENT_RECOVERY_PROJECTIONS_UNLESS_DERIVED_OTHERWISE",
    },
    {
        "probe_id": "D_VARIATION_SCOPE_NOT_DYNAMICS",
        "members": ["R6_LOCAL_VARIATION"],
        "required_posture": "NO_BULK_SELECTION_WEIGHT_FROM_SCOPE_RULE",
    },
    {
        "probe_id": "D_CK_NOT_FIELD_EQUATION",
        "members": ["R5_CK_FIREWALL"],
        "required_posture": "ARCHITECTURE_FILTER_NOT_GRAVITATIONAL_INVARIANT",
    },
]

EQUIVALENCE_RULES = [
    "algebraic tensor identities",
    "total divergences trivial under frozen compact-support local bulk variation",
    "four-dimensional topological densities with no frozen local bulk metric variation",
    "invertible local field redefinitions preserving domain degrees source observables and boundary scope",
    "normalization changes applied consistently to the full coupled action and source",
]

FORBIDDEN_EQUIVALENCES = [
    "different derivative or operator order",
    "different propagating degrees of freedom",
    "local versus nonlocal dynamics",
    "metric-only versus independent-connection dynamics",
    "changed source coupling",
    "observable-changing coefficients",
    "sign index or boundary-condition changes",
]

DISTINCTIVENESS_TESTS = [
    "eliminates an otherwise viable inequivalent family",
    "fixes a coupling or coefficient",
    "derives a cross-pillar gravitational link",
    "explains an Einstein-Hilbert-type recovery limit",
    "requires a novel invariant",
    "produces a distinctive observable",
    "proves a falsifiable no-go result",
]

OUTCOME_DECISION_ORDER = [
    {
        "order": 1,
        "outcome": "REQUIREMENT_SET_INCONSISTENT",
        "precondition": "empty survivor set with explicit inconsistent subset or proof",
    },
    {
        "order": 2,
        "outcome": "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS",
        "precondition": "consistent families exist but desired distinctiveness is proved impossible in frozen class",
    },
    {
        "order": 3,
        "outcome": "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
        "precondition": "accepted native requirements uniquely select one family or bounded equivalence class without supplied uniqueness premises",
    },
    {
        "order": 4,
        "outcome": "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        "precondition": "unique survivor is Einstein-Hilbert-type with every collapse assumption provenance-separated",
    },
    {
        "order": 5,
        "outcome": "ACTION_FAMILY_UNDERDETERMINED",
        "precondition": "multiple inequivalent survivors and exhaustion of refinements not proved",
    },
    {
        "order": 6,
        "outcome": "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
        "precondition": "all accepted-principle selection power exhausted and countermodels prove no refinement can select",
    },
]

ATOMIC_CONTROLS = [
    {
        "control_id": "CTRL_REMOVE_ONE_REQUIREMENT",
        "mutation_count": 1,
        "first_diagnostic": "REQUIREMENT_REMOVAL_DELTA_MISMATCH",
    },
    {
        "control_id": "CTRL_STANDARD_ASSUMPTION_AS_NATIVE",
        "mutation_count": 1,
        "first_diagnostic": "REQUIREMENT_PROVENANCE_CLASS_LEAKAGE",
    },
    {
        "control_id": "CTRL_EH_ORACLE_INSERTION",
        "mutation_count": 1,
        "first_diagnostic": "STANDARD_GR_ORACLE_LEAKAGE",
    },
    {
        "control_id": "CTRL_DUPLICATE_REQUIREMENT",
        "mutation_count": 1,
        "first_diagnostic": "REQUIREMENT_REDUNDANCY_WEIGHT_INFLATION",
    },
    {
        "control_id": "CTRL_INCONSISTENT_PAIR",
        "mutation_count": 1,
        "first_diagnostic": "INCONSISTENT_REQUIREMENT_PAIR_NOT_DETECTED",
    },
    {
        "control_id": "CTRL_BOUNDARY_EQUIVALENT_SPLIT",
        "mutation_count": 1,
        "first_diagnostic": "ACTION_EQUIVALENCE_CLASS_SPLIT",
    },
    {
        "control_id": "CTRL_SHARED_NEWTONIAN_LIMIT_UNIQUENESS",
        "mutation_count": 1,
        "first_diagnostic": "RECOVERY_LIMIT_UNIQUENESS_OVERCLAIM",
    },
    {
        "control_id": "CTRL_SILENT_SCOPE_RELAXATION",
        "mutation_count": 1,
        "first_diagnostic": "FROZEN_ENVELOPE_SCOPE_LEAKAGE",
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"native-principle packet hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    selection = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_"
            "SELECTION_20260718_v0.json"
        ).read_text(encoding="utf-8")
    )
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("native-principle packet did not consume selected target")
    if selection["ranking"].get("selected_candidate_id") != (
        "DEFINE_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_ENVELOPE"
    ):
        raise ValueError("native-principle response winner mismatch")
    if selection["scope"].get("packet_prepared_now") is not False:
        raise ValueError("selection unexpectedly prepared the packet")
    if selection["scope"].get("native_gravitational_action_proposed_or_selected") is not False:
        raise ValueError("selection unexpectedly proposed an action")

    review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_"
            "SECTOR_CONTRACT_PACKET_REVIEW_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if review.get("verdict") != "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE":
        raise ValueError("terminal native-principle review verdict mismatch")
    if review["contract_design_review"].get("status") != (
        "PASS_COMPLETE_BOUNDED_REVIEW_CONTRACT"
    ):
        raise ValueError("minimal gravitational contract acceptance mismatch")
    if review["native_principle_review"].get(
        "project_principle_bound_that_selects_action"
    ) is not False:
        raise ValueError("a native gravitational principle unexpectedly exists")

    ck = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_"
            "AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json"
        ).read_text(encoding="utf-8")
    )
    if ck.get("all_C_k_families_admissibility_only") is not True:
        raise ValueError("C_k firewall mismatch")
    if ck.get("C_k_action_variation_authorized") is not False:
        raise ValueError("C_k action variation unexpectedly authorized")

    rotating = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_"
            "RECOVERY_PACKET_REVIEW_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if rotating.get("verdict") != "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE":
        raise ValueError("gravitomagnetic recovery boundary mismatch")

    stress = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_"
            "DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json"
        ).read_text(encoding="utf-8")
    )
    if stress.get("stress_energy_metric_variation_derived") is not False:
        raise ValueError("stress-energy unexpectedly metric-variation-derived")

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
        raise ValueError("standard-GR comparator boundary mismatch")

    packet = (REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "No current bound authority in this packet selects an at-most-second-order",
        "The catalog is a comparison device, not a candidate list",
        "Showing that `F_EH` satisfies the requirements is not a uniqueness proof",
        "Exactly one result is permitted",
        "eight atomic controls",
        "does not perform the analysis",
        "create an automation",
    ):
        if token not in packet:
            raise ValueError(f"human native-principle packet token missing: {token}")
    return rows


def _validate_contract() -> None:
    if len(STATEMENT_CLASSES) != 3 or len(set(STATEMENT_CLASSES)) != 3:
        raise ValueError("statement-class contract mismatch")
    if len(REQUIREMENT_CLASSES) != 9 or len(set(REQUIREMENT_CLASSES)) != 9:
        raise ValueError("requirement-class contract mismatch")
    if len(REQUIREMENTS) != 10 or len({row["requirement_id"] for row in REQUIREMENTS}) != 10:
        raise ValueError("requirement inventory mismatch")
    valid_classes = set(REQUIREMENT_CLASSES)
    if any(
        not set(row["constraint_classes"]).issubset(valid_classes)
        for row in REQUIREMENTS
    ):
        raise ValueError("requirement uses unknown constraint class")
    if any(row["selection_power_status"] != "NOT_ANALYZED" for row in REQUIREMENTS):
        raise ValueError("packet preparation prematurely analyzed selection power")
    if len(ACTION_FAMILIES) != 7 or len({row["family_id"] for row in ACTION_FAMILIES}) != 7:
        raise ValueError("comparison-family catalog mismatch")
    if not all(row["comparison_only"] for row in ACTION_FAMILIES):
        raise ValueError("comparison family was promoted to candidate")
    if len(MATRIX_CELL_VALUES) != 6 or len(set(MATRIX_CELL_VALUES)) != 6:
        raise ValueError("matrix cell vocabulary mismatch")
    if len(SELECTION_POWER_VALUES) != 8 or len(set(SELECTION_POWER_VALUES)) != 8:
        raise ValueError("selection-power vocabulary mismatch")
    if len(DEPENDENCY_VALUES) != 5 or len(set(DEPENDENCY_VALUES)) != 5:
        raise ValueError("dependency vocabulary mismatch")
    if len(EQUIVALENCE_RULES) != 5 or len(FORBIDDEN_EQUIVALENCES) != 7:
        raise ValueError("equivalence rule contract mismatch")
    if len(DISTINCTIVENESS_TESTS) != 7:
        raise ValueError("distinctiveness contract mismatch")
    if [row["order"] for row in OUTCOME_DECISION_ORDER] != list(range(1, 7)):
        raise ValueError("outcome decision order mismatch")
    if len({row["outcome"] for row in OUTCOME_DECISION_ORDER}) != 6:
        raise ValueError("outcome vocabulary is not mutually exclusive")
    if len(ATOMIC_CONTROLS) != 8 or not all(
        row["mutation_count"] == 1 for row in ATOMIC_CONTROLS
    ):
        raise ValueError("atomic control contract mismatch")
    if len({row["first_diagnostic"] for row in ATOMIC_CONTROLS}) != 8:
        raise ValueError("atomic control diagnostics are not unique")


def build_packet() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    _validate_contract()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native-principle packet focused test missing")

    return {
        "schema_id": (
            "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_"
            "PACKET_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "INDEPENDENT_REQUIREMENTS_ACTION_SELECTION_AND_NO_GO_PACKET_REVIEW_ONLY"
        ),
        "authority": {
            "selection_verdict": (
                "SELECTED_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_PREPARATION"
            ),
            "terminal_prior_block": "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
            "minimal_gravitational_contract": "PASS_COMPLETE_BOUNDED_REVIEW_CONTRACT",
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
            "Do accepted project commitments genuinely select constrain or rule out "
            "gravitational action families, or is a new gravitational postulate unavoidable?"
        ),
        "statement_provenance_contract": {
            "class_count": len(STATEMENT_CLASSES),
            "classes": STATEMENT_CLASSES,
            "exactly_one_initial_class_required": True,
            "convenience_reclassification_allowed": False,
            "second_order_field_equation_assumption": (
                "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION_ONLY"
            ),
            "Levi_Civita_uniqueness_assumption": (
                "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION_ONLY"
            ),
            "no_extra_gravitational_modes_assumption": (
                "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION_ONLY"
            ),
        },
        "requirement_inventory": {
            "requirement_count": len(REQUIREMENTS),
            "constraint_class_count": len(REQUIREMENT_CLASSES),
            "constraint_classes": REQUIREMENT_CLASSES,
            "rows": REQUIREMENTS,
            "selection_power_values": SELECTION_POWER_VALUES,
            "analysis_executed": False,
            "numerical_requirement_weights_allowed": False,
        },
        "comparison_family_envelope": {
            "family_count": len(ACTION_FAMILIES),
            "rows": ACTION_FAMILIES,
            "finite_catalog": True,
            "catalog_exhaustive_over_all_gravity_theories": False,
            "family_adopted_or_activated_count": 0,
            "outside_scope_is_refutation": False,
            "unrestricted_enumeration_engine_authorized": False,
        },
        "survival_elimination_matrix_contract": {
            "row_count": len(REQUIREMENTS),
            "column_count": len(ACTION_FAMILIES),
            "cell_values": MATRIX_CELL_VALUES,
            "elimination_requires_derivation_or_counterexample": True,
            "survival_means_adoption": False,
            "intermediate_survivor_sets_required": True,
            "matrix_computed_by_preparation": False,
        },
        "independence_redundancy_contract": {
            "dependency_values": DEPENDENCY_VALUES,
            "probe_count": len(DEPENDENCY_PROBES),
            "probes": DEPENDENCY_PROBES,
            "duplicate_wording_adds_selection_power": False,
            "numerical_weighting_allowed": False,
            "dependency_analysis_executed": False,
        },
        "standard_GR_isolation": {
            "Einstein_Hilbert_role": "COMPARISON_ORACLE_ONLY",
            "allowed_direction": (
                "ACCEPTED_REQUIREMENTS_TO_COMPUTED_SURVIVOR_TO_EH_COMPARISON"
            ),
            "forbidden_direction": (
                "EH_INPUT_TO_RECONSTRUCTED_REQUIREMENTS_TO_UNIQUENESS_CLAIM"
            ),
            "satisfaction_implies_uniqueness": False,
            "Einstein_equation_allowed_as_selection_premise": False,
            "comparator_activated": False,
        },
        "equivalence_contract": {
            "allowed_rule_count": len(EQUIVALENCE_RULES),
            "allowed_rules": EQUIVALENCE_RULES,
            "forbidden_rule_count": len(FORBIDDEN_EQUIVALENCES),
            "forbidden_equivalences": FORBIDDEN_EQUIVALENCES,
            "claim_scope": "LOCAL_BULK_ONLY",
            "global_boundary_quantum_equivalence_claimed": False,
            "proof_required_per_equivalence": True,
        },
        "distinctiveness_contract": {
            "test_count": len(DISTINCTIVENESS_TESTS),
            "tests": DISTINCTIVENESS_TESTS,
            "at_least_one_demonstrated_test_required": True,
            "repository_ownership_is_distinctiveness": False,
            "methodological_rigor_alone_is_action_selection": False,
        },
        "outcome_contract": {
            "outcome_count": len(OUTCOME_DECISION_ORDER),
            "exactly_one_required": True,
            "decision_order": OUTCOME_DECISION_ORDER,
            "underdetermined_requires_multiple_inequivalent_survivors": True,
            "postulate_required_requires_exhaustion_proof": True,
            "inconsistency_and_no_go_are_distinct": True,
            "standard_GR_collapse_must_report_supplied_assumptions": True,
        },
        "control_contract": {
            "control_count": len(ATOMIC_CONTROLS),
            "all_single_mutation": True,
            "rows": ATOMIC_CONTROLS,
            "controls_executed_by_preparation": False,
            "independent_review_execution_required": True,
        },
        "retained_boundaries": {
            "minimal_gravitational_contract": "ACCEPTED",
            "native_gravitational_principle": "NOT_CREATED_OR_SELECTED",
            "native_gravitational_action": "NOT_PROPOSED_OR_SELECTED",
            "matter_sector": "NOT_SELECTED",
            "standard_GR_comparator": "NOT_ACTIVATED",
            "metric_variation": "NOT_EXECUTED",
            "recovery_ladder": "NOT_ENTERED",
            "gravitomagnetic_recovery": "BLOCKED_UPSTREAM",
            "C_k": "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY",
        },
        "scope": {
            "packet_preparation_only": True,
            "independent_review_executed": False,
            "requirements_selection_analysis_executed": False,
            "survival_elimination_matrix_computed": False,
            "outcome_selected": False,
            "native_gravitational_principle_created_or_selected": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "action_family_adopted_or_activated": False,
            "standard_GR_comparator_activated": False,
            "matter_fields_or_lagrangian_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "recovery_ladder_entered": False,
            "gravitomagnetic_route_reopened": False,
            "C_k_embedded_or_varied": False,
            "symbolic_restoration_reopened": False,
            "unrestricted_theory_enumeration_created": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Prepared packet only. Ten byte-bound requirements, three statement "
            "provenance classes, nine constraint classes, a seven-family comparison "
            "envelope, closed matrix vocabulary, dependency and equivalence rules, "
            "standard-GR isolation, seven distinctiveness tests, six ordered outcomes, "
            "and eight atomic review controls are frozen. No analysis, principle, "
            "postulate, action, family adoption, matter sector, variation, tensor "
            "equation, GR recovery, tooling lane, or automation is created."
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
            raise SystemExit(
                "native gravitational principle requirements packet is stale or missing"
            )
        report = json.loads(raw)
        print(json.dumps({
            "controls": report["control_contract"]["control_count"],
            "families": report["comparison_family_envelope"]["family_count"],
            "outcomes": report["outcome_contract"]["outcome_count"],
            "requirements": report["requirement_inventory"]["requirement_count"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
