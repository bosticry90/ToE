from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal.python.tools import (  # noqa: E402
    native_gravitational_principle_requirements_and_action_selection_packet_review_v1 as review_v1,
)
from formal.python.tools import (  # noqa: E402
    native_gravitational_principle_requirements_and_action_selection_packet_v1 as v1,
)


REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "20260718_v2.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_gravitational_principle_requirements_and_action_selection_packet_v2.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "20260718_v2.md"
)
TARGET = (
    "prepare_native_gravitational_principle_requirements_and_action_selection_"
    "packet_v2"
)
SELECTED_NEXT_TARGET = (
    "review_native_gravitational_principle_requirements_and_action_selection_"
    "packet_v2_result"
)
PRODUCTION_ENTRY_POINT_ID = "evaluate_analysis_v2"
PROJECT_PROFILE = "PROJECT_FROZEN_REQUIREMENTS_ACTION_ANALYSIS_V2"
CONTROL_PROFILE = "SYNTHETIC_CONTROL_REQUIREMENTS_ACTION_ANALYSIS_V2"

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/lanes/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v1.md":
        "66322dff48e73303dbcdd803cd50519efb9ccf667870721e8d10bfac2cb795aa",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v1.json":
        "e15e561c4f9124f7d234c26b40b071213da03454b8416a7cb5f5c75b3a3bde6d",
    "formal/python/tools/native_gravitational_principle_requirements_and_action_selection_packet_review_v1.py":
        "6cf9f7ab46c75ab56a68106fdb951c952fef958a0d7ca09fdc92ef5e870adf6d",
    "formal/python/tests/test_native_gravitational_principle_requirements_and_action_selection_packet_review_v1.py":
        "da31a981f35d51f4d1db5e5c005adacee2a40e6c8ac2f56c5f95493bbbd7eace",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleRequirementsAndActionSelectionPacketReviewV1.lean":
        "9049816f43b458c97993023668b618ec3bd147b7a5512528df41e6cce2f59034",
    PACKET_RELATIVE_PATH:
        "65b0c97de4da870a2bcf0cc91229f3d738a99b6140f19eb2e96cde61b50f5b1b",
}

STATEMENT_CLASSES = tuple(v1.STATEMENT_CLASSES)
MATRIX_CELL_VALUES = tuple(v1.MATRIX_CELL_VALUES)
SCIENTIFIC_OUTCOMES = tuple(v1.SCIENTIFIC_OUTCOMES)

DECISION_BEARING_CALLER_FIELDS = frozenset({
    "requirements",
    "families",
    "statement_class",
    "native_elimination_allowed",
    "native_distinctiveness_allowed",
    "authority_source",
    "evidence_registry",
    "equivalence_map",
    "equivalence_proofs",
    "terminal_evidence",
    "evidence",
})

ALLOWED_EQUIVALENCE_TYPES = frozenset({
    "ALGEBRAIC_IDENTITY",
    "LOCAL_BULK_BOUNDARY_TERM",
    "TOPOLOGICAL_LOCAL_BULK_NULL_VARIATION",
    "INVERTIBLE_LOCAL_FIELD_REDEFINITION",
    "NONZERO_OVERALL_NORMALIZATION",
})

FORBIDDEN_EQUIVALENCE_CHANGES = frozenset({
    "PROPAGATING_DEGREES_OF_FREEDOM",
    "DIFFERENTIAL_ORDER",
    "SCALAR_CONTENT",
    "SOURCE_COUPLING",
    "STABILITY",
    "LOCAL_BULK_EQUATIONS",
    "PHYSICAL_PREDICTIONS",
    "LOCALITY",
    "INDEPENDENT_CONNECTION",
})

FORBIDDEN_FAMILY_EQUIVALENCE_PAIRS = frozenset({
    frozenset({"F_EH", "F_FR"}),
})

ALLOWED_PROJECT_VALIDATOR_IDS = frozenset({
    "CELL_COMPATIBILITY_VALIDATOR_V2",
    "CELL_INCOMPATIBILITY_VALIDATOR_V2",
    "CELL_LIMITATION_VALIDATOR_V2",
    "SCOPE_CLASSIFICATION_VALIDATOR_V2",
    "CONDITIONALITY_VALIDATOR_V2",
    "EQUIVALENCE_PROOF_VALIDATOR_V2",
    "TERMINAL_EVIDENCE_VALIDATOR_V2",
})

VALIDATOR_BY_EVIDENCE_CLASS = MappingProxyType({
    "COMPATIBILITY_EVIDENCE": "CELL_COMPATIBILITY_VALIDATOR_V2",
    "INCOMPATIBILITY_EVIDENCE": "CELL_INCOMPATIBILITY_VALIDATOR_V2",
    "EXPLICIT_LIMITATION_EVIDENCE": "CELL_LIMITATION_VALIDATOR_V2",
    "SCOPE_CLASSIFICATION_EVIDENCE": "SCOPE_CLASSIFICATION_VALIDATOR_V2",
    "CONDITIONALITY_EVIDENCE": "CONDITIONALITY_VALIDATOR_V2",
    "TYPED_EQUIVALENCE_EVIDENCE": "EQUIVALENCE_PROOF_VALIDATOR_V2",
})

CLAIM_SCOPE_BY_STATUS = MappingProxyType({
    "AFFIRMATIVELY_SATISFIES_REQUIREMENT": "EXACT_REQUIREMENT_FAMILY_COMPATIBILITY",
    "ELIMINATED": "EXACT_REQUIREMENT_FAMILY_INCOMPATIBILITY",
    "NOT_DECIDABLE_FROM_REQUIREMENT": "EXACT_REQUIREMENT_FAMILY_LIMITATION",
    "OUTSIDE_FROZEN_ENVELOPE": "FROZEN_ENVELOPE_SCOPE_CLASSIFICATION",
    "EQUIVALENT_UNDER_LOCAL_BULK_RULE": "EXACT_PROPERTY_LOCAL_BULK_EQUIVALENCE",
    "REQUIRES_SUPPLIED_ASSUMPTION": "CONDITIONAL_STANDARD_PHYSICS_DEPENDENCE",
    "NOT_EVALUATED": "NONE",
})


@dataclass(frozen=True)
class BoundRequirement:
    requirement_id: str
    source_identities: tuple[str, ...]
    statement_class: str
    authority_subtype: str
    scope: str
    native_elimination_allowed: bool
    native_distinctiveness_allowed: bool
    requirement_types: tuple[str, ...]
    dependency_information: tuple[str, ...]
    property_key: str
    catalog_role: str


@dataclass(frozen=True)
class BoundFamily:
    family_id: str
    structural_class: str
    envelope_status: str
    comparison_only: bool
    catalog_role: str


@dataclass(frozen=True)
class EvidenceRecord:
    evidence_id: str
    profile_id: str
    requirement_id: str
    family_id: str
    supported_status: str
    claim_scope: str
    evidence_class: str
    source_role: str
    support_reference: str
    validation_status: str
    proof_id: str | None = None
    support_sha256: str = ""
    validator_id: str = ""


@dataclass(frozen=True)
class EquivalenceProof:
    proof_id: str
    profile_id: str
    family_a: str
    family_b: str
    equivalence_type: str
    domain: str
    preserved_property_keys: tuple[str, ...]
    nonpreserved_property_keys: tuple[str, ...]
    forbidden_changes: tuple[str, ...]
    evidence_source: str
    sufficient_for_local_bulk_reduction: bool
    validation_status: str
    canonical_representative: str
    evidence_source_sha256: str = ""
    validator_id: str = ""


@dataclass(frozen=True)
class TerminalEvidence:
    terminal_evidence_id: str
    profile_id: str
    evidence_type: str
    support_reference: str
    validation_status: str
    requirements_internally_consistent: bool | None = None
    ordinary_viable_gravity_exists: bool | None = None
    distinctive_native_gravity_in_envelope_exists: bool | None = None
    accepted_inventory_exhausted: bool | None = None
    no_refinement_countermodel_bound: bool | None = None
    inconsistent_requirement_ids: tuple[str, ...] = ()
    native_discriminating_requirement_ids: tuple[str, ...] = ()
    support_sha256: str = ""
    validator_id: str = ""


@dataclass(frozen=True)
class AnalysisCatalogProvider:
    provider_id: str
    profile_id: str
    validation_status: str
    custody_manifest_relative_path: str
    custody_manifest_sha256: str
    catalog_sha256: str
    evidence_records: tuple[EvidenceRecord, ...]
    equivalence_proofs: tuple[EquivalenceProof, ...]
    terminal_evidence_records: tuple[TerminalEvidence, ...]


DEPENDENCY_BY_REQUIREMENT = {
    "R4_DIFF_COVARIANCE": ("DEPENDENCE_WITH_R7_MUST_BE_DERIVED",),
    "R7_SOURCE_COMPATIBILITY": ("DEPENDENCE_WITH_R4_MUST_BE_DERIVED",),
    "R8_NEWTON_POISSON": ("INDEPENDENT_FROM_R9_UNLESS_DERIVED",),
    "R9_MOMENTUM_CURRENT": ("INDEPENDENT_FROM_R8_UNLESS_DERIVED",),
    "R6_LOCAL_VARIATION": ("SCOPE_ONLY_NO_BULK_SELECTION_WEIGHT",),
    "R5_CK_FIREWALL": ("ARCHITECTURE_FILTER_NOT_FIELD_EQUATION",),
}

PROPERTY_BY_REQUIREMENT = {
    "R1_DIMENSION": "SPACETIME_DIMENSION",
    "R2_METRIC_ONLY": "GRAVITATIONAL_FIELD_CONTENT",
    "R3_LOCALITY": "ACTION_LOCALITY",
    "R4_DIFF_COVARIANCE": "DIFFEOMORPHISM_COVARIANCE",
    "R5_CK_FIREWALL": "CK_EXTERNALITY",
    "R6_LOCAL_VARIATION": "LOCAL_BULK_VARIATION_DOMAIN",
    "R7_SOURCE_COMPATIBILITY": "SOURCE_COUPLING_AND_CONSERVATION",
    "R8_NEWTON_POISSON": "NEWTON_POISSON_RECOVERY",
    "R9_MOMENTUM_CURRENT": "MOMENTUM_CURRENT_RESPONSE",
    "R10_STABILITY_NO_FIT": "STABILITY_AND_NO_FIT_RECOVERY",
}


def _freeze_project_requirement(row: dict[str, Any]) -> BoundRequirement:
    return BoundRequirement(
        requirement_id=row["requirement_id"],
        source_identities=tuple(row["source_bindings"]),
        statement_class=row["statement_class"],
        authority_subtype=row["authority_subclass"],
        scope=row["mathematical_scope"],
        native_elimination_allowed=bool(row["native_elimination_allowed"]),
        native_distinctiveness_allowed=bool(row["native_distinctiveness_allowed"]),
        requirement_types=tuple(row["constraint_classes"]),
        dependency_information=DEPENDENCY_BY_REQUIREMENT.get(
            row["requirement_id"], ("DEPENDENCE_UNRESOLVED",)
        ),
        property_key=PROPERTY_BY_REQUIREMENT[row["requirement_id"]],
        catalog_role="FROZEN_PROJECT_REQUIREMENT",
    )


PROJECT_REQUIREMENT_CATALOG = MappingProxyType({
    row["requirement_id"]: _freeze_project_requirement(row)
    for row in v1.REPAIRED_REQUIREMENTS
})
PROJECT_REQUIREMENT_IDS = tuple(PROJECT_REQUIREMENT_CATALOG)


def _freeze_supplied_requirement(row: dict[str, Any], property_key: str) -> BoundRequirement:
    return BoundRequirement(
        requirement_id=row["requirement_id"],
        source_identities=("FROZEN_SUPPLIED_STANDARD_PHYSICS_REGISTRY_V1",),
        statement_class=row["statement_class"],
        authority_subtype=row["authority_subclass"],
        scope="CONDITIONAL_COMPARATOR_ONLY",
        native_elimination_allowed=False,
        native_distinctiveness_allowed=False,
        requirement_types=("SUPPLIED_ASSUMPTION",),
        dependency_information=("EXCLUDED_FROM_NATIVE_SELECTION",),
        property_key=property_key,
        catalog_role="FROZEN_SUPPLIED_ASSUMPTION",
    )


SUPPLIED_PROPERTY_KEYS = {
    "S1_SECOND_ORDER_FIELD_EQUATIONS": "DIFFERENTIAL_ORDER",
    "S2_LEVI_CIVITA_UNIQUENESS": "CONNECTION_CHOICE",
    "S3_NO_EXTRA_GRAVITATIONAL_MODES": "PROPAGATING_MODE_CONTENT",
}
SUPPLIED_REQUIREMENT_CATALOG = MappingProxyType({
    row["requirement_id"]: _freeze_supplied_requirement(
        row, SUPPLIED_PROPERTY_KEYS[row["requirement_id"]]
    )
    for row in v1.SUPPLIED_ASSUMPTIONS
})


def _control_requirement(requirement_id: str, property_key: str) -> BoundRequirement:
    return BoundRequirement(
        requirement_id=requirement_id,
        source_identities=("INTERNAL_SYNTHETIC_CONTROL_AUTHORITY_V2",),
        statement_class="PROJECT_BOUND_NATIVE_REQUIREMENT",
        authority_subtype="SYNTHETIC_CONTROL_ONLY",
        scope="SYNTHETIC_CONTROL_ONLY",
        native_elimination_allowed=True,
        native_distinctiveness_allowed=True,
        requirement_types=("SYNTHETIC_CONTROL_REQUIREMENT",),
        dependency_information=("SYNTHETIC_INDEPENDENT",),
        property_key=property_key,
        catalog_role="INTERNAL_SYNTHETIC_CONTROL_REQUIREMENT",
    )


CONTROL_REQUIREMENT_CATALOG = MappingProxyType({
    row.requirement_id: row
    for row in (
        _control_requirement("C_NATIVE", "GENERAL_NATIVE_COMPATIBILITY"),
        _control_requirement("C_NEWTON", "NEWTON_POISSON_RECOVERY"),
        _control_requirement("C_DISC", "NATIVE_DISTINCTIVENESS"),
        _control_requirement("C_LOCAL_BULK", "LOCAL_BULK_EQUATIONS"),
        _control_requirement("C_GLOBAL_PROPERTY", "GLOBAL_STABILITY"),
        _control_requirement("C_INCONSISTENT", "SYNTHETIC_INCONSISTENT_CONJUNCTION"),
    )
})

BOUND_REQUIREMENT_CATALOG = MappingProxyType({
    **dict(PROJECT_REQUIREMENT_CATALOG),
    **dict(SUPPLIED_REQUIREMENT_CATALOG),
    **dict(CONTROL_REQUIREMENT_CATALOG),
})


def _freeze_family(row: dict[str, Any]) -> BoundFamily:
    return BoundFamily(
        family_id=row["family_id"],
        structural_class=row["structural_class"],
        envelope_status=row["envelope_status"],
        comparison_only=bool(row["comparison_only"]),
        catalog_role="FROZEN_SEVEN_FAMILY_ENVELOPE",
    )


PROJECT_FAMILY_CATALOG = MappingProxyType({
    row["family_id"]: _freeze_family(row) for row in v1.ACTION_FAMILIES
})
PROJECT_FAMILY_IDS = tuple(PROJECT_FAMILY_CATALOG)


def _control_family(family_id: str, structural_class: str) -> BoundFamily:
    return BoundFamily(
        family_id=family_id,
        structural_class=structural_class,
        envelope_status="PRIMARY_METRIC_LOCAL_ENVELOPE",
        comparison_only=True,
        catalog_role="INTERNAL_SYNTHETIC_CONTROL_FAMILY",
    )


CONTROL_FAMILY_CATALOG = MappingProxyType({
    row.family_id: row
    for row in (
        _control_family("F_EH_BOUNDARY", "synthetic boundary-term EH representative"),
        _control_family("F_NATIVE", "synthetic native-selected action family"),
        _control_family("F_ALT", "synthetic inequivalent alternative action family"),
    )
})

BOUND_FAMILY_CATALOG = MappingProxyType({
    **dict(PROJECT_FAMILY_CATALOG),
    **dict(CONTROL_FAMILY_CATALOG),
})


EQUIVALENCE_PROOF_CATALOG = MappingProxyType({
    "CP_EH_BOUNDARY_LOCAL_BULK": EquivalenceProof(
        proof_id="CP_EH_BOUNDARY_LOCAL_BULK",
        profile_id=CONTROL_PROFILE,
        family_a="F_EH",
        family_b="F_EH_BOUNDARY",
        equivalence_type="LOCAL_BULK_BOUNDARY_TERM",
        domain="FOUR_DIMENSIONAL_COMPACT_SUPPORT_LOCAL_BULK_VARIATION",
        preserved_property_keys=(
            "LOCAL_BULK_EQUATIONS",
            "DIFFEOMORPHISM_COVARIANCE",
            "NEWTON_POISSON_RECOVERY",
        ),
        nonpreserved_property_keys=(
            "GLOBAL_STABILITY",
            "BOUNDARY_OBSERVABLES",
            "GLOBAL_CHARGES",
        ),
        forbidden_changes=(),
        evidence_source="synthetic://v2/boundary-difference/local-bulk-proof",
        sufficient_for_local_bulk_reduction=True,
        validation_status="ACCEPTED",
        canonical_representative="F_EH",
    ),
    "CP_INVALID_FR_EH_PARAMETER_LIMIT": EquivalenceProof(
        proof_id="CP_INVALID_FR_EH_PARAMETER_LIMIT",
        profile_id=CONTROL_PROFILE,
        family_a="F_FR",
        family_b="F_EH",
        equivalence_type="PARAMETER_LIMIT_OR_SUBFAMILY_INCLUSION",
        domain="UNVALIDATED_GLOBAL_FAMILY_MERGE",
        preserved_property_keys=(),
        nonpreserved_property_keys=(
            "PROPAGATING_MODE_CONTENT",
            "DIFFERENTIAL_ORDER",
            "LOCAL_BULK_EQUATIONS",
        ),
        forbidden_changes=(
            "PROPAGATING_DEGREES_OF_FREEDOM",
            "DIFFERENTIAL_ORDER",
            "SCALAR_CONTENT",
        ),
        evidence_source="synthetic://v2/rejected/fR-is-not-EH-equivalence",
        sufficient_for_local_bulk_reduction=False,
        validation_status="REJECTED",
        canonical_representative="F_EH",
    ),
    "CP_FORGED_FR_EH_ALGEBRAIC_IDENTITY": EquivalenceProof(
        proof_id="CP_FORGED_FR_EH_ALGEBRAIC_IDENTITY",
        profile_id=CONTROL_PROFILE,
        family_a="F_FR",
        family_b="F_EH",
        equivalence_type="ALGEBRAIC_IDENTITY",
        domain="FORGED_SYNTHETIC_CONTROL_DOMAIN",
        preserved_property_keys=("GENERAL_NATIVE_COMPATIBILITY",),
        nonpreserved_property_keys=(),
        forbidden_changes=(),
        evidence_source="synthetic://v2/forged/fR-EH-algebraic-identity",
        sufficient_for_local_bulk_reduction=True,
        validation_status="ACCEPTED",
        canonical_representative="F_EH",
    ),
})


def _evidence_class(status: str) -> str:
    return {
        "AFFIRMATIVELY_SATISFIES_REQUIREMENT": "COMPATIBILITY_EVIDENCE",
        "ELIMINATED": "INCOMPATIBILITY_EVIDENCE",
        "NOT_DECIDABLE_FROM_REQUIREMENT": "EXPLICIT_LIMITATION_EVIDENCE",
        "OUTSIDE_FROZEN_ENVELOPE": "SCOPE_CLASSIFICATION_EVIDENCE",
        "REQUIRES_SUPPLIED_ASSUMPTION": "CONDITIONALITY_EVIDENCE",
        "EQUIVALENT_UNDER_LOCAL_BULK_RULE": "TYPED_EQUIVALENCE_EVIDENCE",
    }[status]


def _evidence_id(requirement_id: str, family_id: str, status: str) -> str:
    short = {
        "AFFIRMATIVELY_SATISFIES_REQUIREMENT": "SAT",
        "ELIMINATED": "ELIM",
        "NOT_DECIDABLE_FROM_REQUIREMENT": "UNDEC",
        "OUTSIDE_FROZEN_ENVELOPE": "OUTSIDE",
        "REQUIRES_SUPPLIED_ASSUMPTION": "SUPPLIED",
    }[status]
    return f"CE_{requirement_id}_{family_id}_{short}"


def _build_control_evidence_catalog() -> dict[str, EvidenceRecord]:
    catalog: dict[str, EvidenceRecord] = {}
    statuses = (
        "AFFIRMATIVELY_SATISFIES_REQUIREMENT",
        "ELIMINATED",
        "NOT_DECIDABLE_FROM_REQUIREMENT",
        "OUTSIDE_FROZEN_ENVELOPE",
        "REQUIRES_SUPPLIED_ASSUMPTION",
    )
    control_requirement_ids = tuple(CONTROL_REQUIREMENT_CATALOG) + tuple(
        SUPPLIED_REQUIREMENT_CATALOG
    )
    control_family_ids = (
        "F_EH",
        "F_FR",
        "F_QUADRATIC",
        "F_EH_BOUNDARY",
        "F_NATIVE",
        "F_ALT",
    )
    for requirement_id in control_requirement_ids:
        for family_id in control_family_ids:
            for status in statuses:
                evidence_id = _evidence_id(requirement_id, family_id, status)
                catalog[evidence_id] = EvidenceRecord(
                    evidence_id=evidence_id,
                    profile_id=CONTROL_PROFILE,
                    requirement_id=requirement_id,
                    family_id=family_id,
                    supported_status=status,
                    claim_scope=CLAIM_SCOPE_BY_STATUS[status],
                    evidence_class=_evidence_class(status),
                    source_role="SYNTHETIC_CONTROL_EVIDENCE",
                    support_reference=(
                        f"synthetic://v2/{requirement_id}/{family_id}/{status.lower()}"
                    ),
                    validation_status="ACCEPTED",
                )

    equivalence_id = "CE_C_LOCAL_BULK_F_EH_BOUNDARY_EQUIV"
    catalog[equivalence_id] = EvidenceRecord(
        evidence_id=equivalence_id,
        profile_id=CONTROL_PROFILE,
        requirement_id="C_LOCAL_BULK",
        family_id="F_EH_BOUNDARY",
        supported_status="EQUIVALENT_UNDER_LOCAL_BULK_RULE",
        claim_scope=CLAIM_SCOPE_BY_STATUS["EQUIVALENT_UNDER_LOCAL_BULK_RULE"],
        evidence_class="TYPED_EQUIVALENCE_EVIDENCE",
        source_role="SYNTHETIC_CONTROL_EVIDENCE",
        support_reference="synthetic://v2/exact-local-bulk-property-transport",
        validation_status="ACCEPTED",
        proof_id="CP_EH_BOUNDARY_LOCAL_BULK",
    )

    oracle_id = "CE_ORACLE_C_NATIVE_F_EH_SAT"
    catalog[oracle_id] = EvidenceRecord(
        evidence_id=oracle_id,
        profile_id=CONTROL_PROFILE,
        requirement_id="C_NATIVE",
        family_id="F_EH",
        supported_status="AFFIRMATIVELY_SATISFIES_REQUIREMENT",
        claim_scope=CLAIM_SCOPE_BY_STATUS["AFFIRMATIVELY_SATISFIES_REQUIREMENT"],
        evidence_class="STANDARD_GR_COMPARATOR_RESULT",
        source_role="STANDARD_GR_ORACLE",
        support_reference="synthetic://v2/forbidden-standard-GR-native-leak",
        validation_status="ACCEPTED_AS_COMPARATOR_ONLY",
    )
    return catalog


EVIDENCE_CATALOG = MappingProxyType(_build_control_evidence_catalog())


TERMINAL_EVIDENCE_CATALOG = MappingProxyType({
    "TE_INCONSISTENT": TerminalEvidence(
        terminal_evidence_id="TE_INCONSISTENT",
        profile_id=CONTROL_PROFILE,
        evidence_type="BOUND_INCONSISTENT_REQUIREMENT_SUBSET_PROOF",
        support_reference="synthetic://v2/terminal/inconsistent-subset-proof",
        validation_status="ACCEPTED",
        requirements_internally_consistent=False,
        ordinary_viable_gravity_exists=False,
        distinctive_native_gravity_in_envelope_exists=False,
        inconsistent_requirement_ids=("C_INCONSISTENT",),
    ),
    "TE_NO_GO": TerminalEvidence(
        terminal_evidence_id="TE_NO_GO",
        profile_id=CONTROL_PROFILE,
        evidence_type="DISTINCTIVENESS_NO_GO_PROOF_IN_FROZEN_ENVELOPE",
        support_reference="synthetic://v2/terminal/viable-gravity-distinctiveness-no-go",
        validation_status="ACCEPTED",
        requirements_internally_consistent=True,
        ordinary_viable_gravity_exists=True,
        distinctive_native_gravity_in_envelope_exists=False,
    ),
    "TE_NATIVE_DISTINCTIVENESS": TerminalEvidence(
        terminal_evidence_id="TE_NATIVE_DISTINCTIVENESS",
        profile_id=CONTROL_PROFILE,
        evidence_type="BOUND_NATIVE_DISTINCTIVENESS_PROOF",
        support_reference="synthetic://v2/terminal/native-distinctiveness",
        validation_status="ACCEPTED",
        requirements_internally_consistent=True,
        ordinary_viable_gravity_exists=True,
        distinctive_native_gravity_in_envelope_exists=True,
        native_discriminating_requirement_ids=("C_DISC",),
    ),
    "TE_INVENTORY_EXHAUSTED": TerminalEvidence(
        terminal_evidence_id="TE_INVENTORY_EXHAUSTED",
        profile_id=CONTROL_PROFILE,
        evidence_type="BOUND_NATIVE_INVENTORY_EXHAUSTION_AND_COUNTERMODEL",
        support_reference="synthetic://v2/terminal/inventory-exhaustion-countermodel",
        validation_status="ACCEPTED",
        requirements_internally_consistent=True,
        ordinary_viable_gravity_exists=True,
        distinctive_native_gravity_in_envelope_exists=False,
        accepted_inventory_exhausted=True,
        no_refinement_countermodel_bound=True,
    ),
})


def _catalog_sha256(
    evidence_records: tuple[EvidenceRecord, ...],
    equivalence_proofs: tuple[EquivalenceProof, ...],
    terminal_records: tuple[TerminalEvidence, ...],
) -> str:
    raw = json.dumps({
        "evidence_records": [asdict(row) for row in evidence_records],
        "equivalence_proofs": [asdict(row) for row in equivalence_proofs],
        "terminal_evidence_records": [asdict(row) for row in terminal_records],
    }, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


_CONTROL_EVIDENCE_RECORDS = tuple(EVIDENCE_CATALOG.values())
_CONTROL_EQUIVALENCE_PROOFS = tuple(EQUIVALENCE_PROOF_CATALOG.values())
_CONTROL_TERMINAL_RECORDS = tuple(TERMINAL_EVIDENCE_CATALOG.values())

CONTROL_CATALOG_PROVIDER = AnalysisCatalogProvider(
    provider_id="INTERNAL_SYNTHETIC_CONTROL_PROVIDER_V2",
    profile_id=CONTROL_PROFILE,
    validation_status="INTERNAL_SYNTHETIC_PROVIDER",
    custody_manifest_relative_path="INTERNAL_SYNTHETIC_CONTROL_CATALOGS",
    custody_manifest_sha256="INTERNAL_SYNTHETIC_CONTROL_CATALOGS",
    catalog_sha256=_catalog_sha256(
        _CONTROL_EVIDENCE_RECORDS,
        _CONTROL_EQUIVALENCE_PROOFS,
        _CONTROL_TERMINAL_RECORDS,
    ),
    evidence_records=_CONTROL_EVIDENCE_RECORDS,
    equivalence_proofs=_CONTROL_EQUIVALENCE_PROOFS,
    terminal_evidence_records=_CONTROL_TERMINAL_RECORDS,
)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _failure(diagnostic: str, stage: str) -> dict[str, Any]:
    return {
        "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
        "status": "PRECHECK_FAILURE",
        "diagnostic": diagnostic,
        "failed_stage": stage,
        "matrix_evaluated": False,
        "scientific_outcome": None,
        "matching_scientific_outcomes": [],
        "matching_scientific_outcome_count": 0,
    }


def _resolved_requirement_row(row: BoundRequirement) -> dict[str, Any]:
    value = asdict(row)
    value["source_identities"] = list(row.source_identities)
    value["requirement_types"] = list(row.requirement_types)
    value["dependency_information"] = list(row.dependency_information)
    return value


def _resolved_family_row(row: BoundFamily) -> dict[str, Any]:
    return asdict(row)


def _validate_input_contract(value: dict[str, Any]) -> dict[str, Any] | None:
    forbidden = sorted(DECISION_BEARING_CALLER_FIELDS.intersection(value))
    if forbidden:
        return _failure("CALLER_DECISION_BEARING_OBJECT_REJECTED", "public_input_preflight")
    if value.get("analysis_profile") not in {PROJECT_PROFILE, CONTROL_PROFILE}:
        return _failure("UNKNOWN_ANALYSIS_PROFILE", "public_input_preflight")
    if value.get("mode") != "NATIVE_ONLY":
        return _failure("NON_NATIVE_MODE_NOT_AUTHORIZED", "public_input_preflight")
    requirement_ids = value.get("requirement_ids")
    family_ids = value.get("family_ids")
    if not isinstance(requirement_ids, list) or not requirement_ids:
        return _failure("REQUIREMENT_ID_INVENTORY_MISSING", "requirement_resolution")
    if not isinstance(family_ids, list) or not family_ids:
        return _failure("FAMILY_ID_ENVELOPE_MISSING", "family_resolution")
    if len(requirement_ids) != len(set(requirement_ids)):
        return _failure("DUPLICATE_REQUIREMENT_ID", "requirement_resolution")
    if len(family_ids) != len(set(family_ids)):
        return _failure("DUPLICATE_FAMILY_ID", "family_resolution")
    if any(requirement_id not in BOUND_REQUIREMENT_CATALOG for requirement_id in requirement_ids):
        return _failure("UNKNOWN_REQUIREMENT_ID", "requirement_resolution")
    if any(family_id not in BOUND_FAMILY_CATALOG for family_id in family_ids):
        return _failure("UNKNOWN_FAMILY_ID", "family_resolution")
    if value["analysis_profile"] == PROJECT_PROFILE:
        if tuple(requirement_ids) != PROJECT_REQUIREMENT_IDS:
            return _failure("PROJECT_REQUIREMENT_INVENTORY_MISMATCH", "requirement_resolution")
        if tuple(family_ids) != PROJECT_FAMILY_IDS:
            return _failure("PROJECT_FAMILY_ENVELOPE_MISMATCH", "family_resolution")
    return None


def _claim_binding_sha256(row: EvidenceRecord | EquivalenceProof | TerminalEvidence) -> str:
    value = asdict(row)
    for key in (
        "support_reference",
        "support_sha256",
        "evidence_source",
        "evidence_source_sha256",
        "validator_id",
        "validation_status",
    ):
        value.pop(key, None)
    raw = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return _sha256(raw)


def _repository_relative_file(
    reference: str,
) -> Path | None:
    reference_path = Path(reference)
    if reference_path.is_absolute() or "://" in reference:
        return None
    resolved = (REPO_ROOT / reference_path).resolve()
    if not resolved.is_relative_to(REPO_ROOT.resolve()) or not resolved.is_file():
        return None
    return resolved


def _validate_project_attestation(
    row: EvidenceRecord | EquivalenceProof | TerminalEvidence,
    *,
    record_kind: str,
    record_id: str,
    reference: str,
    expected_hash: str,
    validator_id: str,
) -> str | None:
    if validator_id not in ALLOWED_PROJECT_VALIDATOR_IDS:
        return "PROJECT_EVIDENCE_VALIDATOR_NOT_ALLOWED"
    attestation_path = _repository_relative_file(reference)
    if attestation_path is None:
        return "PROJECT_EVIDENCE_REFERENCE_NOT_REPOSITORY_RELATIVE_OR_MISSING"
    if _sha256(attestation_path.read_bytes()) != expected_hash:
        return "PROJECT_EVIDENCE_ATTESTATION_HASH_MISMATCH"
    try:
        attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        return "PROJECT_EVIDENCE_ATTESTATION_INVALID"
    expected_keys = {
        "schema_id",
        "validator_id",
        "validation_status",
        "record_kind",
        "record_id",
        "claim_binding_sha256",
        "evidence_source_relative_path",
        "evidence_source_sha256",
    }
    if not isinstance(attestation, dict) or set(attestation) != expected_keys:
        return "PROJECT_EVIDENCE_ATTESTATION_SCHEMA_MISMATCH"
    if (
        attestation["schema_id"]
        != "NATIVE_GRAVITATIONAL_ANALYSIS_EVIDENCE_ATTESTATION_V2"
        or attestation["validator_id"] != validator_id
        or attestation["validation_status"] != "ACCEPTED"
        or attestation["record_kind"] != record_kind
        or attestation["record_id"] != record_id
        or attestation["claim_binding_sha256"] != _claim_binding_sha256(row)
    ):
        return "PROJECT_EVIDENCE_ATTESTATION_BINDING_MISMATCH"
    source_path = _repository_relative_file(attestation["evidence_source_relative_path"])
    if source_path is None:
        return "PROJECT_EVIDENCE_SOURCE_MISSING_OR_OUTSIDE_REPOSITORY"
    if _sha256(source_path.read_bytes()) != attestation["evidence_source_sha256"]:
        return "PROJECT_EVIDENCE_SOURCE_HASH_MISMATCH"
    return None


def _validate_catalog_provider(
    value: dict[str, Any], provider: AnalysisCatalogProvider | None
) -> tuple[
    dict[str, EvidenceRecord],
    dict[str, EquivalenceProof],
    dict[str, TerminalEvidence],
    dict[str, Any] | None,
]:
    if provider is None:
        if value["analysis_profile"] == CONTROL_PROFILE:
            provider = CONTROL_CATALOG_PROVIDER
        else:
            return {}, {}, {}, _failure(
                "PROJECT_EVIDENCE_PROVIDER_REQUIRED", "catalog_provider_preflight"
            )
    if not isinstance(provider, AnalysisCatalogProvider):
        return {}, {}, {}, _failure(
            "CATALOG_PROVIDER_TYPE_INVALID", "catalog_provider_preflight"
        )
    if provider.profile_id != value["analysis_profile"]:
        return {}, {}, {}, _failure(
            "CATALOG_PROVIDER_PROFILE_MISMATCH", "catalog_provider_preflight"
        )
    if provider.profile_id == CONTROL_PROFILE:
        if provider != CONTROL_CATALOG_PROVIDER:
            return {}, {}, {}, _failure(
                "UNREGISTERED_CONTROL_CATALOG_PROVIDER", "catalog_provider_preflight"
            )
    else:
        if provider.validation_status != "CUSTODY_VALIDATED_PROJECT_PROVIDER":
            return {}, {}, {}, _failure(
                "PROJECT_CATALOG_PROVIDER_NOT_CUSTODY_VALIDATED",
                "catalog_provider_preflight",
            )
        manifest_path = REPO_ROOT / provider.custody_manifest_relative_path
        if not manifest_path.is_file():
            return {}, {}, {}, _failure(
                "PROJECT_PROVIDER_CUSTODY_MANIFEST_MISSING",
                "catalog_provider_preflight",
            )
        observed = _sha256(manifest_path.read_bytes())
        if observed != provider.custody_manifest_sha256:
            return {}, {}, {}, _failure(
                "PROJECT_PROVIDER_CUSTODY_HASH_MISMATCH",
                "catalog_provider_preflight",
            )
        observed_catalog_hash = _catalog_sha256(
            provider.evidence_records,
            provider.equivalence_proofs,
            provider.terminal_evidence_records,
        )
        if observed_catalog_hash != provider.catalog_sha256:
            return {}, {}, {}, _failure(
                "PROJECT_PROVIDER_CATALOG_HASH_MISMATCH",
                "catalog_provider_preflight",
            )
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError):
            return {}, {}, {}, _failure(
                "PROJECT_PROVIDER_CUSTODY_MANIFEST_INVALID",
                "catalog_provider_preflight",
            )
        expected_manifest = {
            "schema_id": "NATIVE_GRAVITATIONAL_ANALYSIS_CATALOG_PROVIDER_MANIFEST_V2",
            "manifest_validator_id": "CATALOG_PROVIDER_MANIFEST_VALIDATOR_V2",
            "provider_id": provider.provider_id,
            "profile_id": provider.profile_id,
            "catalog_sha256": provider.catalog_sha256,
            "evidence_record_count": len(provider.evidence_records),
            "equivalence_proof_count": len(provider.equivalence_proofs),
            "terminal_evidence_record_count": len(provider.terminal_evidence_records),
            "independent_validation_status": "ACCEPTED_FOR_BOUNDED_ANALYSIS",
        }
        if manifest != expected_manifest:
            return {}, {}, {}, _failure(
                "PROJECT_PROVIDER_MANIFEST_BINDING_MISMATCH",
                "catalog_provider_preflight",
            )
        for row in provider.evidence_records:
            if row.profile_id != PROJECT_PROFILE or row.validation_status != "ACCEPTED":
                return {}, {}, {}, _failure(
                    "PROJECT_EVIDENCE_RECORD_NOT_VALIDATED",
                    "catalog_provider_preflight",
                )
            expected_validator = VALIDATOR_BY_EVIDENCE_CLASS.get(row.evidence_class)
            if expected_validator is None or row.validator_id != expected_validator:
                return {}, {}, {}, _failure(
                    "PROJECT_EVIDENCE_VALIDATOR_CLASS_MISMATCH",
                    "catalog_provider_preflight",
                )
            diagnostic = _validate_project_attestation(
                row,
                record_kind="CELL_EVIDENCE",
                record_id=row.evidence_id,
                reference=row.support_reference,
                expected_hash=row.support_sha256,
                validator_id=row.validator_id,
            )
            if diagnostic is not None:
                return {}, {}, {}, _failure(diagnostic, "catalog_provider_preflight")
        for row in provider.equivalence_proofs:
            if row.profile_id != PROJECT_PROFILE or row.validation_status != "ACCEPTED":
                return {}, {}, {}, _failure(
                    "PROJECT_EQUIVALENCE_PROOF_NOT_VALIDATED",
                    "catalog_provider_preflight",
                )
            if row.validator_id != "EQUIVALENCE_PROOF_VALIDATOR_V2":
                return {}, {}, {}, _failure(
                    "PROJECT_EQUIVALENCE_VALIDATOR_MISMATCH",
                    "catalog_provider_preflight",
                )
            diagnostic = _validate_project_attestation(
                row,
                record_kind="EQUIVALENCE_PROOF",
                record_id=row.proof_id,
                reference=row.evidence_source,
                expected_hash=row.evidence_source_sha256,
                validator_id=row.validator_id,
            )
            if diagnostic is not None:
                return {}, {}, {}, _failure(diagnostic, "catalog_provider_preflight")
        for row in provider.terminal_evidence_records:
            if row.profile_id != PROJECT_PROFILE or row.validation_status != "ACCEPTED":
                return {}, {}, {}, _failure(
                    "PROJECT_TERMINAL_EVIDENCE_NOT_VALIDATED",
                    "catalog_provider_preflight",
                )
            if row.validator_id != "TERMINAL_EVIDENCE_VALIDATOR_V2":
                return {}, {}, {}, _failure(
                    "PROJECT_TERMINAL_VALIDATOR_MISMATCH",
                    "catalog_provider_preflight",
                )
            diagnostic = _validate_project_attestation(
                row,
                record_kind="TERMINAL_EVIDENCE",
                record_id=row.terminal_evidence_id,
                reference=row.support_reference,
                expected_hash=row.support_sha256,
                validator_id=row.validator_id,
            )
            if diagnostic is not None:
                return {}, {}, {}, _failure(diagnostic, "catalog_provider_preflight")
    evidence = {row.evidence_id: row for row in provider.evidence_records}
    proofs = {row.proof_id: row for row in provider.equivalence_proofs}
    terminal = {
        row.terminal_evidence_id: row for row in provider.terminal_evidence_records
    }
    if len(evidence) != len(provider.evidence_records):
        return {}, {}, {}, _failure(
            "DUPLICATE_PROVIDER_EVIDENCE_ID", "catalog_provider_preflight"
        )
    if len(proofs) != len(provider.equivalence_proofs):
        return {}, {}, {}, _failure(
            "DUPLICATE_PROVIDER_EQUIVALENCE_PROOF_ID", "catalog_provider_preflight"
        )
    if len(terminal) != len(provider.terminal_evidence_records):
        return {}, {}, {}, _failure(
            "DUPLICATE_PROVIDER_TERMINAL_EVIDENCE_ID", "catalog_provider_preflight"
        )
    return evidence, proofs, terminal, None


def _validate_proofs(
    value: dict[str, Any],
    family_ids: list[str],
    proof_catalog: dict[str, EquivalenceProof],
) -> tuple[list[EquivalenceProof], dict[str, Any] | None]:
    proof_ids = value.get("equivalence_proof_ids", [])
    if not isinstance(proof_ids, list):
        return [], _failure("EQUIVALENCE_PROOF_ID_LIST_INVALID", "equivalence_preflight")
    if len(proof_ids) != len(set(proof_ids)):
        return [], _failure("DUPLICATE_EQUIVALENCE_PROOF_ID", "equivalence_preflight")
    proofs: list[EquivalenceProof] = []
    for proof_id in proof_ids:
        proof = proof_catalog.get(proof_id)
        if proof is None:
            return [], _failure("UNKNOWN_EQUIVALENCE_PROOF_ID", "equivalence_preflight")
        if proof.profile_id != value["analysis_profile"]:
            return [], _failure("EQUIVALENCE_PROOF_PROFILE_MISMATCH", "equivalence_preflight")
        if proof.validation_status != "ACCEPTED":
            return [], _failure("EQUIVALENCE_PROOF_REJECTED", "equivalence_preflight")
        if frozenset({proof.family_a, proof.family_b}) in (
            FORBIDDEN_FAMILY_EQUIVALENCE_PAIRS
        ):
            return [], _failure(
                "FORBIDDEN_FAMILY_EQUIVALENCE_PAIR", "equivalence_preflight"
            )
        if proof.equivalence_type not in ALLOWED_EQUIVALENCE_TYPES:
            return [], _failure("EQUIVALENCE_TYPE_NOT_ALLOWED", "equivalence_preflight")
        if set(proof.forbidden_changes).intersection(FORBIDDEN_EQUIVALENCE_CHANGES):
            return [], _failure("FORBIDDEN_PHYSICAL_EQUIVALENCE_CHANGE", "equivalence_preflight")
        if not proof.sufficient_for_local_bulk_reduction:
            return [], _failure("EQUIVALENCE_PROOF_INSUFFICIENT", "equivalence_preflight")
        if proof.family_a not in family_ids or proof.family_b not in family_ids:
            return [], _failure("EQUIVALENCE_PROOF_FAMILY_OUTSIDE_INPUT", "equivalence_preflight")
        proofs.append(proof)
    return proofs, None


def _validate_terminal_evidence(
    value: dict[str, Any],
    requirement_ids: list[str],
    terminal_catalog: dict[str, TerminalEvidence],
) -> tuple[TerminalEvidence | None, dict[str, Any] | None]:
    ids = value.get("terminal_evidence_ids", [])
    if not isinstance(ids, list):
        return None, _failure("TERMINAL_EVIDENCE_ID_LIST_INVALID", "terminal_evidence_preflight")
    if len(ids) > 1:
        return None, _failure("MULTIPLE_TERMINAL_EVIDENCE_RECORDS", "terminal_evidence_preflight")
    if not ids:
        return None, None
    record = terminal_catalog.get(ids[0])
    if record is None:
        return None, _failure("UNKNOWN_TERMINAL_EVIDENCE_ID", "terminal_evidence_preflight")
    if record.profile_id != value["analysis_profile"]:
        return None, _failure("TERMINAL_EVIDENCE_PROFILE_MISMATCH", "terminal_evidence_preflight")
    if record.validation_status != "ACCEPTED":
        return None, _failure("TERMINAL_EVIDENCE_REJECTED", "terminal_evidence_preflight")
    if not set(record.inconsistent_requirement_ids).issubset(requirement_ids):
        return None, _failure("TERMINAL_EVIDENCE_REQUIREMENT_MISMATCH", "terminal_evidence_preflight")
    if not set(record.native_discriminating_requirement_ids).issubset(requirement_ids):
        return None, _failure("TERMINAL_EVIDENCE_REQUIREMENT_MISMATCH", "terminal_evidence_preflight")
    return record, None


def _validate_matrix(
    value: dict[str, Any],
    requirements: list[BoundRequirement],
    families: list[BoundFamily],
    proofs: list[EquivalenceProof],
    evidence_catalog: dict[str, EvidenceRecord],
) -> dict[str, Any] | None:
    matrix = value.get("matrix")
    if not isinstance(matrix, dict):
        return _failure("MATRIX_MISSING", "matrix_preflight")
    requirement_ids = [row.requirement_id for row in requirements]
    family_ids = [row.family_id for row in families]
    if set(matrix) != set(requirement_ids):
        return _failure("MATRIX_REQUIREMENT_SHAPE_MISMATCH", "matrix_preflight")
    proof_ids = {proof.proof_id for proof in proofs}
    proof_by_id = {proof.proof_id: proof for proof in proofs}
    for requirement in requirements:
        cells = matrix[requirement.requirement_id]
        if not isinstance(cells, dict) or set(cells) != set(family_ids):
            return _failure("MATRIX_FAMILY_SHAPE_MISMATCH", "matrix_preflight")
        for family in families:
            cell = cells[family.family_id]
            if not isinstance(cell, dict) or set(cell) != {
                "status", "evidence_id", "claim_scope"
            }:
                return _failure("MATRIX_CELL_SCHEMA_MISMATCH", "matrix_preflight")
            status = cell["status"]
            if status not in MATRIX_CELL_VALUES:
                return _failure("UNKNOWN_MATRIX_CELL_STATE", "matrix_preflight")
            if cell["claim_scope"] != CLAIM_SCOPE_BY_STATUS[status]:
                return _failure("MATRIX_CELL_CLAIM_SCOPE_MISMATCH", "matrix_preflight")
            outside = family.envelope_status.startswith("OUTSIDE_FROZEN_")
            if outside and status != "OUTSIDE_FROZEN_ENVELOPE":
                return _failure("FAMILY_SCOPE_CELL_CONFLICT", "matrix_preflight")
            if not outside and status == "OUTSIDE_FROZEN_ENVELOPE":
                return _failure("PRIMARY_FAMILY_SCOPE_CELL_CONFLICT", "matrix_preflight")
            if status == "NOT_EVALUATED":
                if cell["evidence_id"] is not None:
                    return _failure("NOT_EVALUATED_CELL_HAS_EVIDENCE", "evidence_preflight")
                continue
            evidence_id = cell["evidence_id"]
            if not isinstance(evidence_id, str) or not evidence_id:
                return _failure("EVIDENCE_ID_REQUIRED", "evidence_preflight")
            evidence = evidence_catalog.get(evidence_id)
            if evidence is None:
                return _failure("UNKNOWN_EVIDENCE_ID", "evidence_preflight")
            if evidence.profile_id != value["analysis_profile"]:
                return _failure("EVIDENCE_PROFILE_MISMATCH", "evidence_preflight")
            if evidence.validation_status not in {"ACCEPTED", "ACCEPTED_AS_COMPARATOR_ONLY"}:
                return _failure("EVIDENCE_RECORD_REJECTED", "evidence_preflight")
            if (
                evidence.requirement_id != requirement.requirement_id
                or evidence.family_id != family.family_id
                or evidence.supported_status != status
                or evidence.claim_scope != cell["claim_scope"]
            ):
                return _failure("EVIDENCE_CELL_BINDING_MISMATCH", "evidence_preflight")
            if evidence.source_role == "STANDARD_GR_ORACLE":
                return _failure("STANDARD_GR_ORACLE_NATIVE_EVIDENCE", "evidence_preflight")
            if (
                requirement.statement_class == "PROJECT_BOUND_NATIVE_REQUIREMENT"
                and evidence.source_role == "SUPPLIED_STANDARD_PHYSICS"
            ):
                return _failure("SUPPLIED_ASSUMPTION_NATIVE_EVIDENCE", "evidence_preflight")
            if (
                status == "ELIMINATED"
                and requirement.statement_class == "PROJECT_BOUND_NATIVE_REQUIREMENT"
                and not requirement.native_elimination_allowed
            ):
                return _failure("INELIGIBLE_NATIVE_ELIMINATION", "evidence_preflight")
            if status == "EQUIVALENT_UNDER_LOCAL_BULK_RULE":
                if evidence.proof_id is None or evidence.proof_id not in proof_ids:
                    return _failure("EQUIVALENCE_CELL_PROOF_MISSING", "evidence_preflight")
                proof = proof_by_id[evidence.proof_id]
                if requirement.property_key not in proof.preserved_property_keys:
                    return _failure("EQUIVALENCE_PROPERTY_TRANSPORT_NOT_PROVED", "evidence_preflight")
                if family.family_id not in {proof.family_a, proof.family_b}:
                    return _failure("EQUIVALENCE_CELL_FAMILY_MISMATCH", "evidence_preflight")
    return None


def _components(
    primary_ids: list[str], proofs: list[EquivalenceProof]
) -> tuple[list[list[str]], dict[str, str]]:
    parent = {family_id: family_id for family_id in primary_ids}

    def find(value: str) -> str:
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    def union(a: str, b: str) -> None:
        root_a = find(a)
        root_b = find(b)
        if root_a != root_b:
            parent[root_b] = root_a

    for proof in proofs:
        if proof.family_a in parent and proof.family_b in parent:
            union(proof.family_a, proof.family_b)
    grouped: dict[str, list[str]] = {}
    for family_id in primary_ids:
        grouped.setdefault(find(family_id), []).append(family_id)
    components = [sorted(members) for members in grouped.values()]
    components.sort()
    representatives: dict[str, str] = {}
    for members in components:
        relevant = [
            proof
            for proof in proofs
            if proof.family_a in members and proof.family_b in members
        ]
        candidates = {
            proof.canonical_representative
            for proof in relevant
            if proof.canonical_representative in members
        }
        representative = "F_EH" if "F_EH" in candidates else (
            sorted(candidates)[0] if candidates else members[0]
        )
        for member in members:
            representatives[member] = representative
    return components, representatives


def _property_transport_complete(
    members: list[str], proofs: list[EquivalenceProof], property_key: str
) -> bool:
    if len(members) <= 1:
        return True
    adjacency = {member: set() for member in members}
    for proof in proofs:
        if (
            proof.family_a in adjacency
            and proof.family_b in adjacency
            and property_key in proof.preserved_property_keys
        ):
            adjacency[proof.family_a].add(proof.family_b)
            adjacency[proof.family_b].add(proof.family_a)
    seen = {members[0]}
    stack = [members[0]]
    while stack:
        current = stack.pop()
        for neighbor in adjacency[current] - seen:
            seen.add(neighbor)
            stack.append(neighbor)
    return seen == set(members)


def _class_requirement_status(
    statuses: list[str],
    members: list[str],
    proofs: list[EquivalenceProof],
    property_key: str,
) -> str:
    satisfying = {
        "AFFIRMATIVELY_SATISFIES_REQUIREMENT",
        "EQUIVALENT_UNDER_LOCAL_BULK_RULE",
    }
    unresolved = {
        "NOT_DECIDABLE_FROM_REQUIREMENT",
        "REQUIRES_SUPPLIED_ASSUMPTION",
    }
    if all(status in satisfying for status in statuses):
        return "CLASS_SATISFIES"
    if all(status == "ELIMINATED" for status in statuses):
        return "CLASS_ELIMINATED"
    if (
        any(status in satisfying for status in statuses)
        and any(status in unresolved for status in statuses)
        and not any(status == "ELIMINATED" for status in statuses)
        and _property_transport_complete(members, proofs, property_key)
    ):
        return "CLASS_SATISFIES_VIA_EXACT_PROPERTY_TRANSPORT"
    return "EQUIVALENCE_CLASS_STATUS_UNRESOLVED"


def _matching_outcomes(
    summary: dict[str, Any],
    terminal: TerminalEvidence | None,
) -> list[str]:
    affirmative = summary["affirmative_equivalence_classes"]
    unresolved = summary["unresolved_equivalence_classes"]
    possible = sorted(set(affirmative).union(unresolved))
    unique_complete = len(affirmative) == 1 and not unresolved
    terminal_type = terminal.evidence_type if terminal else None
    native_trace_ids = {
        row["requirement_id"] for row in summary["native_elimination_trace"]
    }

    inconsistent = (
        not possible
        and terminal_type == "BOUND_INCONSISTENT_REQUIREMENT_SUBSET_PROOF"
        and terminal is not None
        and terminal.requirements_internally_consistent is False
        and bool(terminal.inconsistent_requirement_ids)
    )
    no_go = (
        bool(affirmative)
        and terminal_type == "DISTINCTIVENESS_NO_GO_PROOF_IN_FROZEN_ENVELOPE"
        and terminal is not None
        and terminal.requirements_internally_consistent is True
        and terminal.ordinary_viable_gravity_exists is True
        and terminal.distinctive_native_gravity_in_envelope_exists is False
    )
    native_selection = (
        unique_complete
        and terminal_type == "BOUND_NATIVE_DISTINCTIVENESS_PROOF"
        and terminal is not None
        and bool(terminal.native_discriminating_requirement_ids)
        and set(terminal.native_discriminating_requirement_ids).issubset(native_trace_ids)
    )
    collapse = (
        unique_complete
        and affirmative == ["F_EH"]
        and terminal is None
    )
    postulate_required = (
        len(possible) >= 2
        and terminal_type == "BOUND_NATIVE_INVENTORY_EXHAUSTION_AND_COUNTERMODEL"
        and terminal is not None
        and terminal.accepted_inventory_exhausted is True
        and terminal.no_refinement_countermodel_bound is True
    )
    underdetermined = bool(possible) and terminal is None and not collapse

    predicates = {
        "REQUIREMENT_SET_INCONSISTENT": inconsistent,
        "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS": no_go,
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY": native_selection,
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR": collapse,
        "ACTION_FAMILY_UNDERDETERMINED": underdetermined,
        "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED": postulate_required,
    }
    return [outcome for outcome in SCIENTIFIC_OUTCOMES if predicates[outcome]]


def evaluate_analysis(
    value: dict[str, Any],
    *,
    catalog_provider: AnalysisCatalogProvider | None = None,
) -> dict[str, Any]:
    preflight = _validate_input_contract(value)
    if preflight is not None:
        return preflight
    requirement_ids = value["requirement_ids"]
    family_ids = value["family_ids"]
    requirements = [BOUND_REQUIREMENT_CATALOG[item] for item in requirement_ids]
    families = [BOUND_FAMILY_CATALOG[item] for item in family_ids]
    (
        evidence_catalog,
        proof_catalog,
        terminal_catalog,
        provider_failure,
    ) = _validate_catalog_provider(value, catalog_provider)
    if provider_failure is not None:
        return provider_failure
    proofs, proof_failure = _validate_proofs(value, family_ids, proof_catalog)
    if proof_failure is not None:
        return proof_failure
    terminal, terminal_failure = _validate_terminal_evidence(
        value, requirement_ids, terminal_catalog
    )
    if terminal_failure is not None:
        return terminal_failure
    matrix_failure = _validate_matrix(
        value, requirements, families, proofs, evidence_catalog
    )
    if matrix_failure is not None:
        return matrix_failure

    caller_claims = value.get("caller_requirement_claims", [])
    if not isinstance(caller_claims, list):
        return _failure("CALLER_REQUIREMENT_CLAIMS_INVALID", "authority_resolution")
    ignored_claims = copy.deepcopy(caller_claims)
    resolved_requirements = [_resolved_requirement_row(row) for row in requirements]
    resolved_families = [_resolved_family_row(row) for row in families]
    matrix = value["matrix"]
    if any(
        cell["status"] == "NOT_EVALUATED"
        for cells in matrix.values()
        for cell in cells.values()
    ):
        return {
            "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
            "status": "ANALYSIS_INCOMPLETE",
            "diagnostic": "NOT_EVALUATED_CELL_PRESENT",
            "failed_stage": "matrix_completion",
            "matrix_evaluated": False,
            "scientific_outcome": None,
            "matching_scientific_outcomes": [],
            "matching_scientific_outcome_count": 0,
            "resolved_requirements": resolved_requirements,
            "ignored_caller_requirement_claims": ignored_claims,
        }

    primary_ids = [
        row.family_id
        for row in families
        if row.envelope_status == "PRIMARY_METRIC_LOCAL_ENVELOPE"
    ]
    native_requirements = [
        row
        for row in requirements
        if row.statement_class == "PROJECT_BOUND_NATIVE_REQUIREMENT"
    ]
    supplied_requirements = [
        row
        for row in requirements
        if row.statement_class == "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
    ]
    native_elimination_trace: list[dict[str, str]] = []
    supplied_exclusion_trace: list[dict[str, str]] = []
    family_statuses: dict[str, str] = {}
    for family_id in primary_ids:
        statuses = []
        for requirement in native_requirements:
            status = matrix[requirement.requirement_id][family_id]["status"]
            statuses.append(status)
            if status == "ELIMINATED":
                native_elimination_trace.append({
                    "requirement_id": requirement.requirement_id,
                    "family_id": family_id,
                })
        for requirement in supplied_requirements:
            status = matrix[requirement.requirement_id][family_id]["status"]
            if status == "ELIMINATED":
                supplied_exclusion_trace.append({
                    "requirement_id": requirement.requirement_id,
                    "family_id": family_id,
                })
        if "ELIMINATED" in statuses:
            family_statuses[family_id] = "ELIMINATED"
        elif any(status in {
            "NOT_DECIDABLE_FROM_REQUIREMENT", "REQUIRES_SUPPLIED_ASSUMPTION"
        } for status in statuses):
            family_statuses[family_id] = "UNRESOLVED"
        else:
            family_statuses[family_id] = "AFFIRMATIVE"

    components, representatives = _components(primary_ids, proofs)
    class_requirement_rows: list[dict[str, Any]] = []
    class_statuses: dict[str, str] = {}
    for members in components:
        representative = representatives[members[0]]
        requirement_statuses: list[str] = []
        for requirement in native_requirements:
            member_statuses = [
                matrix[requirement.requirement_id][member]["status"]
                for member in members
            ]
            class_status = _class_requirement_status(
                member_statuses, members, proofs, requirement.property_key
            )
            requirement_statuses.append(class_status)
            class_requirement_rows.append({
                "equivalence_class_representative": representative,
                "member_family_ids": members,
                "requirement_id": requirement.requirement_id,
                "property_key": requirement.property_key,
                "member_statuses": dict(zip(members, member_statuses)),
                "class_status": class_status,
                "property_transport_proved": _property_transport_complete(
                    members, proofs, requirement.property_key
                ),
            })
        if "EQUIVALENCE_CLASS_STATUS_UNRESOLVED" in requirement_statuses:
            class_statuses[representative] = "UNRESOLVED"
        elif "CLASS_ELIMINATED" in requirement_statuses:
            class_statuses[representative] = "ELIMINATED"
        else:
            class_statuses[representative] = "AFFIRMATIVE"

    summary = {
        "primary_family_ids": primary_ids,
        "eliminated_family_ids": sorted(
            key for key, status in family_statuses.items() if status == "ELIMINATED"
        ),
        "affirmative_family_ids": sorted(
            key for key, status in family_statuses.items() if status == "AFFIRMATIVE"
        ),
        "unresolved_family_ids": sorted(
            key for key, status in family_statuses.items() if status == "UNRESOLVED"
        ),
        "equivalence_classes": [
            {
                "representative": representatives[members[0]],
                "members": members,
                "class_status": class_statuses[representatives[members[0]]],
            }
            for members in components
        ],
        "class_requirement_statuses": class_requirement_rows,
        "eliminated_equivalence_classes": sorted(
            key for key, status in class_statuses.items() if status == "ELIMINATED"
        ),
        "affirmative_equivalence_classes": sorted(
            key for key, status in class_statuses.items() if status == "AFFIRMATIVE"
        ),
        "unresolved_equivalence_classes": sorted(
            key for key, status in class_statuses.items() if status == "UNRESOLVED"
        ),
        "native_elimination_trace": native_elimination_trace,
        "supplied_assumption_exclusion_trace": supplied_exclusion_trace,
    }
    matching = _matching_outcomes(summary, terminal)
    if not matching:
        status = (
            "EMPTY_SET_CLASSIFICATION_INSUFFICIENT"
            if not summary["affirmative_equivalence_classes"]
            and not summary["unresolved_equivalence_classes"]
            else "TERMINAL_EVIDENCE_CONTEXT_MISMATCH"
        )
        return {
            "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
            "status": status,
            "diagnostic": status,
            "failed_stage": "outcome_selection",
            "matrix_evaluated": True,
            "scientific_outcome": None,
            "matching_scientific_outcomes": [],
            "matching_scientific_outcome_count": 0,
            "resolved_requirements": resolved_requirements,
            "resolved_families": resolved_families,
            "ignored_caller_requirement_claims": ignored_claims,
            "summary": summary,
        }
    if len(matching) != 1:
        return _failure("OUTCOME_PREDICATE_OVERLAP", "outcome_selection")
    return {
        "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
        "status": "SCIENTIFIC_OUTCOME_COMPUTED",
        "diagnostic": None,
        "failed_stage": None,
        "matrix_evaluated": True,
        "scientific_outcome": matching[0],
        "matching_scientific_outcomes": matching,
        "matching_scientific_outcome_count": 1,
        "resolved_requirements": resolved_requirements,
        "resolved_families": resolved_families,
        "ignored_caller_requirement_claims": ignored_claims,
        "terminal_evidence_id": terminal.terminal_evidence_id if terminal else None,
        "summary": summary,
    }


def _cell(
    requirement_id: str,
    family_id: str,
    status: str,
    *,
    evidence_id: str | None = None,
) -> dict[str, Any]:
    if status == "NOT_EVALUATED":
        evidence_id = None
    elif evidence_id is None:
        if status == "EQUIVALENT_UNDER_LOCAL_BULK_RULE":
            evidence_id = "CE_C_LOCAL_BULK_F_EH_BOUNDARY_EQUIV"
        else:
            evidence_id = _evidence_id(requirement_id, family_id, status)
    return {
        "status": status,
        "evidence_id": evidence_id,
        "claim_scope": CLAIM_SCOPE_BY_STATUS[status],
    }


def _fixture(
    requirement_ids: list[str],
    family_ids: list[str],
    statuses: dict[str, dict[str, str]],
    *,
    equivalence_proof_ids: list[str] | None = None,
    terminal_evidence_ids: list[str] | None = None,
    caller_requirement_claims: list[dict[str, Any]] | None = None,
    evidence_overrides: dict[tuple[str, str], str | None] | None = None,
) -> dict[str, Any]:
    evidence_overrides = evidence_overrides or {}
    return {
        "analysis_profile": CONTROL_PROFILE,
        "mode": "NATIVE_ONLY",
        "requirement_ids": requirement_ids,
        "family_ids": family_ids,
        "matrix": {
            requirement_id: {
                family_id: _cell(
                    requirement_id,
                    family_id,
                    statuses[requirement_id][family_id],
                    evidence_id=evidence_overrides.get(
                        (requirement_id, family_id), None
                    ),
                )
                for family_id in family_ids
            }
            for requirement_id in set(requirement_ids)
        },
        "equivalence_proof_ids": equivalence_proof_ids or [],
        "terminal_evidence_ids": terminal_evidence_ids or [],
        "caller_requirement_claims": caller_requirement_claims or [],
    }


def _diff_paths(before: Any, after: Any, prefix: str = "$") -> list[str]:
    if type(before) is not type(after):
        return [prefix]
    if isinstance(before, dict):
        paths: list[str] = []
        for key in sorted(set(before).union(after)):
            child = f"{prefix}.{key}"
            if key not in before or key not in after:
                paths.append(child)
            else:
                paths.extend(_diff_paths(before[key], after[key], child))
        return paths
    if isinstance(before, list):
        return [] if before == after else [prefix]
    return [] if before == after else [prefix]


def _control_row(
    control_id: str,
    expected: Any,
    observed: Any,
    result: dict[str, Any],
    passed: bool,
    *,
    construction_kind: str = "MINIMAL_SYNTHETIC_FIXTURE",
    changed_paths: list[str] | None = None,
) -> dict[str, Any]:
    return {
        "control_id": control_id,
        "construction_kind": construction_kind,
        "changed_paths": changed_paths or [],
        "expected": expected,
        "observed": observed,
        "entry_point_id": result["entry_point_id"],
        "passed": passed,
    }


def _outcome_fixture(outcome: str) -> dict[str, Any]:
    sat = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    elim = "ELIMINATED"
    if outcome == "REQUIREMENT_SET_INCONSISTENT":
        return _fixture(
            ["C_INCONSISTENT"], ["F_ALT"],
            {"C_INCONSISTENT": {"F_ALT": elim}},
            terminal_evidence_ids=["TE_INCONSISTENT"],
        )
    if outcome == "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS":
        return _fixture(
            ["C_NATIVE"], ["F_EH"], {"C_NATIVE": {"F_EH": sat}},
            terminal_evidence_ids=["TE_NO_GO"],
        )
    if outcome == "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY":
        return _fixture(
            ["C_DISC"], ["F_NATIVE", "F_ALT"],
            {"C_DISC": {"F_NATIVE": sat, "F_ALT": elim}},
            terminal_evidence_ids=["TE_NATIVE_DISTINCTIVENESS"],
        )
    if outcome == "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR":
        return _fixture(
            ["C_NATIVE"], ["F_EH"], {"C_NATIVE": {"F_EH": sat}}
        )
    if outcome == "ACTION_FAMILY_UNDERDETERMINED":
        return _fixture(
            ["C_NATIVE"], ["F_EH", "F_FR"],
            {"C_NATIVE": {"F_EH": sat, "F_FR": sat}},
        )
    if outcome == "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED":
        return _fixture(
            ["C_NATIVE"], ["F_EH", "F_FR"],
            {"C_NATIVE": {"F_EH": sat, "F_FR": sat}},
            terminal_evidence_ids=["TE_INVENTORY_EXHAUSTED"],
        )
    raise ValueError(f"unknown outcome: {outcome}")


def run_six_outcome_controls() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for outcome in SCIENTIFIC_OUTCOMES:
        result = evaluate_analysis(_outcome_fixture(outcome))
        rows.append({
            "control_id": f"CTRL_OUTCOME_{outcome}",
            "expected": outcome,
            "observed": result["scientific_outcome"],
            "matching_scientific_outcome_count": result[
                "matching_scientific_outcome_count"
            ],
            "entry_point_id": result["entry_point_id"],
            "passed": (
                result["scientific_outcome"] == outcome
                and result["matching_scientific_outcome_count"] == 1
            ),
        })
    return {
        "outcome_control_count": len(rows),
        "outcome_control_pass_count": sum(row["passed"] for row in rows),
        "all_six_outcomes_reached": {
            row["observed"] for row in rows
        } == set(SCIENTIFIC_OUTCOMES),
        "rows": rows,
    }


def run_production_controls() -> dict[str, Any]:
    sat = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    elim = "ELIMINATED"
    undec = "NOT_DECIDABLE_FROM_REQUIREMENT"
    equiv = "EQUIVALENT_UNDER_LOCAL_BULK_RULE"
    retained: list[dict[str, Any]] = []

    value = _fixture(
        ["C_NATIVE", "S1_SECOND_ORDER_FIELD_EQUATIONS"],
        ["F_EH", "F_FR"],
        {
            "C_NATIVE": {"F_EH": sat, "F_FR": sat},
            "S1_SECOND_ORDER_FIELD_EQUATIONS": {"F_EH": sat, "F_FR": elim},
        },
    )
    result = evaluate_analysis(value)
    retained.append(_control_row(
        "CTRL_SUPPLIED_SECOND_ORDER_NOT_NATIVE",
        "ACTION_FAMILY_UNDERDETERMINED",
        result["scientific_outcome"],
        result,
        result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED"
        and result["summary"]["supplied_assumption_exclusion_trace"] == [{
            "requirement_id": "S1_SECOND_ORDER_FIELD_EQUATIONS",
            "family_id": "F_FR",
        }],
    ))

    value = _fixture(
        ["C_NATIVE"], ["F_EH"], {"C_NATIVE": {"F_EH": sat}}
    )
    result = evaluate_analysis(value)
    retained.append(_control_row(
        "CTRL_MISSING_STATEMENT_CLASS_RESOLVED_INTERNALLY",
        "PROJECT_BOUND_NATIVE_REQUIREMENT",
        result["resolved_requirements"][0]["statement_class"],
        result,
        result["resolved_requirements"][0]["statement_class"]
        == "PROJECT_BOUND_NATIVE_REQUIREMENT",
    ))

    value = _fixture(
        ["C_NATIVE", "C_NATIVE"], ["F_EH"],
        {"C_NATIVE": {"F_EH": sat}},
    )
    result = evaluate_analysis(value)
    retained.append(_control_row(
        "CTRL_DUPLICATE_REQUIREMENT",
        "DUPLICATE_REQUIREMENT_ID",
        result["diagnostic"], result,
        result["diagnostic"] == "DUPLICATE_REQUIREMENT_ID",
    ))

    result = evaluate_analysis(_fixture(
        ["C_NEWTON"], ["F_EH", "F_FR"],
        {"C_NEWTON": {"F_EH": sat, "F_FR": sat}},
    ))
    retained.append(_control_row(
        "CTRL_SHARED_NEWTONIAN_LIMIT",
        "ACTION_FAMILY_UNDERDETERMINED",
        result["scientific_outcome"], result,
        result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED",
    ))

    result = evaluate_analysis(_fixture(
        ["C_NATIVE"], ["F_EH", "F_FR"],
        {"C_NATIVE": {"F_EH": sat, "F_FR": undec}},
    ))
    retained.append(_control_row(
        "CTRL_UNDECIDABLE_CELL",
        {"affirmative": ["F_EH"], "unresolved": ["F_FR"]},
        {
            "affirmative": result["summary"]["affirmative_family_ids"],
            "unresolved": result["summary"]["unresolved_family_ids"],
        },
        result,
        result["summary"]["affirmative_family_ids"] == ["F_EH"]
        and result["summary"]["unresolved_family_ids"] == ["F_FR"],
    ))

    result = evaluate_analysis(_fixture(
        ["C_LOCAL_BULK"], ["F_EH", "F_EH_BOUNDARY"],
        {"C_LOCAL_BULK": {"F_EH": sat, "F_EH_BOUNDARY": sat}},
        equivalence_proof_ids=["CP_EH_BOUNDARY_LOCAL_BULK"],
    ))
    retained.append(_control_row(
        "CTRL_BOUNDARY_EQUIVALENCE",
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        result["scientific_outcome"], result,
        result["scientific_outcome"] == "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
        and result["summary"]["affirmative_equivalence_classes"] == ["F_EH"],
    ))

    result = evaluate_analysis(_fixture(
        ["C_DISC"], ["F_EH", "F_FR"],
        {"C_DISC": {"F_EH": sat, "F_FR": elim}},
    ))
    retained.append(_control_row(
        "CTRL_UNIQUE_NONDISTINCTIVE_EH",
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        result["scientific_outcome"], result,
        result["scientific_outcome"] == "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
    ))

    result = evaluate_analysis(_outcome_fixture(
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY"
    ))
    retained.append(_control_row(
        "CTRL_UNIQUE_NATIVE_DISTINCTIVE",
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
        result["scientific_outcome"], result,
        result["scientific_outcome"] == "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
    ))

    boundary_base = _outcome_fixture("ACTION_FAMILY_UNDERDETERMINED")
    boundary_exhausted = copy.deepcopy(boundary_base)
    boundary_exhausted["terminal_evidence_ids"] = ["TE_INVENTORY_EXHAUSTED"]
    boundary_changed = _diff_paths(boundary_base, boundary_exhausted)
    base_result = evaluate_analysis(boundary_base)
    exhausted_result = evaluate_analysis(boundary_exhausted)
    boundary_probes = [
        _control_row(
            "PROBE_UNDERDETERMINED_WITHOUT_EXHAUSTION",
            "ACTION_FAMILY_UNDERDETERMINED",
            base_result["scientific_outcome"], base_result,
            base_result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED",
        ),
        _control_row(
            "PROBE_POSTULATE_REQUIRED_AFTER_EXHAUSTION",
            "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
            exhausted_result["scientific_outcome"], exhausted_result,
            exhausted_result["scientific_outcome"]
            == "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED"
            and boundary_changed == ["$.terminal_evidence_ids"],
            construction_kind="BASELINE_SINGLE_FIELD_MUTATION",
            changed_paths=boundary_changed,
        ),
    ]

    adversarial: list[dict[str, Any]] = []
    class_base = _fixture(
        ["C_NATIVE", "S3_NO_EXTRA_GRAVITATIONAL_MODES"],
        ["F_EH", "F_FR"],
        {
            "C_NATIVE": {"F_EH": sat, "F_FR": sat},
            "S3_NO_EXTRA_GRAVITATIONAL_MODES": {"F_EH": sat, "F_FR": elim},
        },
    )
    class_mutated = copy.deepcopy(class_base)
    class_mutated["caller_requirement_claims"] = [{
        "requirement_id": "S3_NO_EXTRA_GRAVITATIONAL_MODES",
        "statement_class": "PROJECT_BOUND_NATIVE_REQUIREMENT",
        "native_elimination_allowed": True,
    }]
    class_changed = _diff_paths(class_base, class_mutated)
    result = evaluate_analysis(class_mutated)
    resolved_s3 = next(
        row for row in result["resolved_requirements"]
        if row["requirement_id"] == "S3_NO_EXTRA_GRAVITATIONAL_MODES"
    )
    adversarial.append(_control_row(
        "ADV_FALSE_CALLER_STATEMENT_CLASS_IGNORED",
        "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        resolved_s3["statement_class"], result,
        resolved_s3["statement_class"] == "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
        and resolved_s3["native_elimination_allowed"] is False
        and result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED"
        and class_changed == ["$.caller_requirement_claims"],
        construction_kind="BASELINE_SINGLE_FIELD_MUTATION",
        changed_paths=class_changed,
    ))

    evidence_base = _fixture(
        ["C_NATIVE"], ["F_EH"], {"C_NATIVE": {"F_EH": sat}}
    )
    evidence_mutated = copy.deepcopy(evidence_base)
    evidence_mutated["matrix"]["C_NATIVE"]["F_EH"]["evidence_id"] = None
    evidence_changed = _diff_paths(evidence_base, evidence_mutated)
    result = evaluate_analysis(evidence_mutated)
    adversarial.append(_control_row(
        "ADV_SATISFIES_WITHOUT_EVIDENCE",
        "EVIDENCE_ID_REQUIRED", result["diagnostic"], result,
        result["diagnostic"] == "EVIDENCE_ID_REQUIRED"
        and evidence_changed == ["$.matrix.C_NATIVE.F_EH.evidence_id"],
        construction_kind="BASELINE_SINGLE_FIELD_MUTATION",
        changed_paths=evidence_changed,
    ))

    equivalence_base = _fixture(
        ["C_LOCAL_BULK"], ["F_EH", "F_EH_BOUNDARY"],
        {"C_LOCAL_BULK": {"F_EH": sat, "F_EH_BOUNDARY": equiv}},
        equivalence_proof_ids=["CP_EH_BOUNDARY_LOCAL_BULK"],
    )
    equivalence_mutated = copy.deepcopy(equivalence_base)
    equivalence_mutated["equivalence_proof_ids"] = []
    equivalence_changed = _diff_paths(equivalence_base, equivalence_mutated)
    result = evaluate_analysis(equivalence_mutated)
    adversarial.append(_control_row(
        "ADV_EQUIVALENT_WITHOUT_VALIDATED_PROOF",
        "EQUIVALENCE_CELL_PROOF_MISSING", result["diagnostic"], result,
        result["diagnostic"] == "EQUIVALENCE_CELL_PROOF_MISSING"
        and equivalence_changed == ["$.equivalence_proof_ids"],
        construction_kind="BASELINE_SINGLE_FIELD_MUTATION",
        changed_paths=equivalence_changed,
    ))

    result = evaluate_analysis(_fixture(
        ["C_NATIVE"], ["F_EH", "F_FR"],
        {"C_NATIVE": {"F_EH": sat, "F_FR": sat}},
        equivalence_proof_ids=["CP_INVALID_FR_EH_PARAMETER_LIMIT"],
    ))
    adversarial.append(_control_row(
        "ADV_INVALID_FR_TO_EH_PROOF_REJECTED",
        "EQUIVALENCE_PROOF_REJECTED", result["diagnostic"], result,
        result["diagnostic"] == "EQUIVALENCE_PROOF_REJECTED",
    ))

    result = evaluate_analysis(_fixture(
        ["C_GLOBAL_PROPERTY"], ["F_EH", "F_EH_BOUNDARY"],
        {"C_GLOBAL_PROPERTY": {"F_EH": sat, "F_EH_BOUNDARY": undec}},
        equivalence_proof_ids=["CP_EH_BOUNDARY_LOCAL_BULK"],
    ))
    class_row = result["summary"]["class_requirement_statuses"][0]
    adversarial.append(_control_row(
        "ADV_UNDECIDABLE_CLASS_WITHOUT_PROPERTY_TRANSPORT",
        "EQUIVALENCE_CLASS_STATUS_UNRESOLVED",
        class_row["class_status"], result,
        class_row["class_status"] == "EQUIVALENCE_CLASS_STATUS_UNRESOLVED"
        and class_row["property_transport_proved"] is False
        and result["summary"]["unresolved_equivalence_classes"] == ["F_EH"],
    ))

    oracle_base = _fixture(
        ["C_NATIVE"], ["F_EH"], {"C_NATIVE": {"F_EH": sat}}
    )
    oracle_mutated = copy.deepcopy(oracle_base)
    oracle_mutated["matrix"]["C_NATIVE"]["F_EH"]["evidence_id"] = (
        "CE_ORACLE_C_NATIVE_F_EH_SAT"
    )
    oracle_changed = _diff_paths(oracle_base, oracle_mutated)
    result = evaluate_analysis(oracle_mutated)
    adversarial.append(_control_row(
        "ADV_STANDARD_GR_ORACLE_AS_NATIVE_EVIDENCE",
        "STANDARD_GR_ORACLE_NATIVE_EVIDENCE", result["diagnostic"], result,
        result["diagnostic"] == "STANDARD_GR_ORACLE_NATIVE_EVIDENCE"
        and oracle_changed == ["$.matrix.C_NATIVE.F_EH.evidence_id"],
        construction_kind="BASELINE_SINGLE_FIELD_MUTATION",
        changed_paths=oracle_changed,
    ))

    outcome_controls = run_six_outcome_controls()
    all_rows: Iterable[dict[str, Any]] = (
        retained + boundary_probes + adversarial + outcome_controls["rows"]
    )
    all_shared = all(
        row["entry_point_id"] == PRODUCTION_ENTRY_POINT_ID for row in all_rows
    )
    return {
        "production_entry_point_id": PRODUCTION_ENTRY_POINT_ID,
        "retained_control_count": len(retained),
        "retained_control_pass_count": sum(row["passed"] for row in retained),
        "retained_controls": retained,
        "boundary_probe_count": len(boundary_probes),
        "boundary_probe_pass_count": sum(row["passed"] for row in boundary_probes),
        "boundary_probes": boundary_probes,
        "adversarial_control_count": len(adversarial),
        "adversarial_control_pass_count": sum(row["passed"] for row in adversarial),
        "adversarial_controls": adversarial,
        "outcome_controls": outcome_controls,
        "all_used_shared_entry_point": all_shared,
        "single_field_mutation_controls": sum(
            row["construction_kind"] == "BASELINE_SINGLE_FIELD_MUTATION"
            for row in retained + boundary_probes + adversarial
        ),
        "all_declared_single_field_mutations_atomic": all(
            len(row["changed_paths"]) == 1
            for row in retained + boundary_probes + adversarial
            if row["construction_kind"] == "BASELINE_SINGLE_FIELD_MUTATION"
        ),
    }


def _validate_authority_and_contract() -> dict[str, Any]:
    frozen: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"native-principle v2 authority hash mismatch: {relative_path}")
        frozen.append({"relative_path": relative_path, "sha256": observed})
    review = json.loads(
        (REPO_ROOT / review_v1.REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if review.get("verdict") != review_v1.VERDICT:
        raise ValueError("v1 review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("v1 review did not authorize v2 preparation")
    if review["scope"].get("real_matrix_cells_computed") != 0:
        raise ValueError("v1 review real matrix boundary mismatch")
    controls = run_production_controls()
    if not (
        controls["retained_control_pass_count"]
        == controls["retained_control_count"]
        == 8
    ):
        raise ValueError("retained v2 controls failed")
    if not (
        controls["boundary_probe_pass_count"]
        == controls["boundary_probe_count"]
        == 2
    ):
        raise ValueError("v2 boundary probes failed")
    if not (
        controls["adversarial_control_pass_count"]
        == controls["adversarial_control_count"]
        == 6
    ):
        raise ValueError("v2 adversarial controls failed")
    outcomes = controls["outcome_controls"]
    if not (
        outcomes["outcome_control_pass_count"]
        == outcomes["outcome_control_count"]
        == 6
    ):
        raise ValueError("v2 six-outcome controls failed")
    if not outcomes["all_six_outcomes_reached"]:
        raise ValueError("v2 outcome reachability incomplete")
    if not controls["all_used_shared_entry_point"]:
        raise ValueError("v2 control bypassed production entry point")
    if not controls["all_declared_single_field_mutations_atomic"]:
        raise ValueError("v2 atomic mutation control mismatch")
    return {"frozen_inputs": frozen, "controls": controls}


def build_packet() -> dict[str, Any]:
    validated = _validate_authority_and_contract()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native-principle v2 focused test missing")
    return {
        "schema_id": (
            "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_"
            "PACKET_20260718_v2"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "INDEPENDENT_REQUIREMENTS_ACTION_SELECTION_PACKET_V2_REVIEW_ONLY"
        ),
        "authority": {
            "v1_review_verdict": review_v1.VERDICT,
            "frozen_inputs": validated["frozen_inputs"],
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "repair_contract": {
            "repair_count": 5,
            "repairs": [
                "authority-derived immutable requirement objects",
                "evidence-bound decision-bearing matrix cells",
                "typed validated proof-derived equivalence classes",
                "property-scoped conservative uncertainty preservation",
                "reachable exclusive six-way scientific classifier",
            ],
            "final_automatically_authorized_repair_attempt": True,
            "automatic_v3_authorized": False,
        },
        "authority_derived_requirement_contract": {
            "public_decision_input": ["analysis_profile", "requirement_ids", "family_ids"],
            "caller_authored_requirement_objects_allowed": False,
            "caller_decision_bearing_fields_rejected": sorted(
                DECISION_BEARING_CALLER_FIELDS
            ),
            "caller_requirement_claims_authoritative": False,
            "project_requirement_count": len(PROJECT_REQUIREMENT_CATALOG),
            "project_requirement_ids": list(PROJECT_REQUIREMENT_IDS),
            "project_rows": [
                _resolved_requirement_row(PROJECT_REQUIREMENT_CATALOG[item])
                for item in PROJECT_REQUIREMENT_IDS
            ],
            "supplied_assumption_count": len(SUPPLIED_REQUIREMENT_CATALOG),
            "supplied_assumption_rows": [
                _resolved_requirement_row(row)
                for row in SUPPLIED_REQUIREMENT_CATALOG.values()
            ],
            "immutable_internal_type": "frozen dataclass plus read-only mapping proxy",
        },
        "family_envelope_contract": {
            "project_family_count": len(PROJECT_FAMILY_CATALOG),
            "project_family_ids": list(PROJECT_FAMILY_IDS),
            "rows": [_resolved_family_row(row) for row in PROJECT_FAMILY_CATALOG.values()],
            "unchanged_from_v1": True,
            "expanded_for_real_analysis": False,
        },
        "evidence_bound_cell_contract": {
            "cell_schema": [
                "requirement_id", "family_id", "status", "evidence_id", "claim_scope"
            ],
            "decision_bearing_statuses_require_evidence": [
                status for status in MATRIX_CELL_VALUES if status != "NOT_EVALUATED"
            ],
            "not_evaluated_requires_evidence": False,
            "evidence_exact_binding_fields": [
                "profile_id", "requirement_id", "family_id", "supported_status",
                "claim_scope", "evidence_class", "source_role", "support_reference",
                "support_sha256", "validator_id",
            ],
            "expected_outcome_is_evidence": False,
            "real_project_evidence_record_count": 0,
            "synthetic_evidence_records_are_profile_isolated": True,
        },
        "typed_equivalence_contract": {
            "caller_declared_edges_allowed": False,
            "input_is_proof_ids_only": True,
            "allowed_equivalence_types": sorted(ALLOWED_EQUIVALENCE_TYPES),
            "forbidden_physical_changes": sorted(FORBIDDEN_EQUIVALENCE_CHANGES),
            "forbidden_family_pairs": [["F_EH", "F_FR"]],
            "validated_proof_fields": list(EquivalenceProof.__dataclass_fields__),
            "class_labels_derived_from_validated_proof_graph": True,
            "fR_to_EH_parameter_limit_is_equivalence": False,
            "property_transport_must_be_exact": True,
        },
        "uncertainty_preservation_contract": {
            "member_level_statuses_retained": True,
            "class_level_unresolved_state": "EQUIVALENCE_CLASS_STATUS_UNRESOLVED",
            "mixed_satisfied_undecidable_default": (
                "EQUIVALENCE_CLASS_STATUS_UNRESOLVED"
            ),
            "affirmative_transport_requires_connected_exact_property_proof": True,
            "local_bulk_proof_does_not_transport_global_stability": True,
        },
        "six_way_classifier_contract": {
            "scientific_outcome_count": len(SCIENTIFIC_OUTCOMES),
            "scientific_outcomes": list(SCIENTIFIC_OUTCOMES),
            "every_outcome_has_full_path_synthetic_fixture": True,
            "viable_gravity_no_go_reachable": True,
            "inconsistency_and_no_go_distinct": True,
            "exactly_one_outcome_per_valid_fixture": True,
            "raw_terminal_booleans_allowed": False,
            "terminal_evidence_ids_only": True,
        },
        "production_evaluator_contract": {
            "entry_point": "evaluate_analysis",
            "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
            "project_profile": PROJECT_PROFILE,
            "control_profile": CONTROL_PROFILE,
            "control_and_future_real_analysis_share_entry_point": True,
            "real_project_profile_requires_exact_10_by_7_shape": True,
            "catalog_provider_type": "AnalysisCatalogProvider",
            "project_provider_requires_custody_manifest_and_sha256": True,
            "project_manifest_binds_provider_profile_catalog_hash_and_record_counts": True,
            "project_attestation_schema": (
                "NATIVE_GRAVITATIONAL_ANALYSIS_EVIDENCE_ATTESTATION_V2"
            ),
            "project_attestation_binds_record_claim_and_underlying_source": True,
            "project_evidence_sources_are_repository_relative_and_hash_exact": True,
            "project_validator_ids_are_closed": True,
            "project_provider_supplied_by_preparation": False,
            "caller_catalog_objects_inside_analysis_input_allowed": False,
        },
        "control_execution": validated["controls"],
        "standard_GR_isolation": {
            "Einstein_Hilbert_role": "COMPARISON_ORACLE_ONLY",
            "oracle_evidence_rejected_in_native_matrix": True,
            "supplied_assumptions_excluded_from_native_reduction": True,
            "comparison_occurs_after_native_matrix_reduction": True,
            "comparator_activated": False,
        },
        "real_analysis_boundary": {
            "real_matrix_row_count": 10,
            "real_matrix_column_count": 7,
            "real_matrix_cell_count": 70,
            "real_matrix_cells_supplied": 0,
            "real_matrix_evidence_records_supplied": 0,
            "real_survivor_set": "NOT_COMPUTED",
            "real_scientific_outcome": "NOT_SELECTED",
        },
        "anti_rabbit_hole_boundary": {
            "v2_is_final_automatically_authorized_repair_attempt": True,
            "automatic_v3_authorized": False,
            "if_v2_foundational_review_failure": [
                "CLOSE_AUTOMATED_ACTION_SELECTION_TOOLING_LANE",
                "CONDUCT_SMALLER_MANUALLY_ADJUDICATED_REQUIREMENTS_ANALYSIS",
                "RETURN_TO_FULL_SCIENTIFIC_PRIORITY_MAP",
            ],
        },
        "scope": {
            "v2_contract_repair_prepared": True,
            "synthetic_controls_executed": True,
            "independent_v2_review_executed": False,
            "real_requirements_family_analysis_executed": False,
            "real_matrix_cells_computed": 0,
            "real_family_judgment_made": False,
            "real_survivor_matrix_computed": False,
            "real_scientific_outcome_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "standard_GR_comparator_activated": False,
            "matter_sector_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "gravitomagnetic_route_reopened": False,
            "family_envelope_expanded": False,
            "automatic_v3_authorized": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Final automatically authorized contract-repair preparation only. V2 derives "
            "requirements from immutable internal authority, binds every decision-bearing "
            "synthetic cell to profile-isolated evidence, derives equivalence classes only "
            "from typed validated proof IDs, preserves uncertainty unless exact property "
            "transport is proved, and reaches each frozen scientific outcome once through "
            "the shared evaluator. The real matrix remains 0/70. No real family judgment, "
            "principle, postulate, action, matter choice, variation, GR result, V3, or "
            "automation is authorized or created."
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
            raise SystemExit("native-principle v2 packet is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "adversarial_controls": report["control_execution"]["adversarial_control_pass_count"],
            "outcomes_reached": report["control_execution"]["outcome_controls"]["outcome_control_pass_count"],
            "real_matrix_cells": report["real_analysis_boundary"]["real_matrix_cells_supplied"],
            "retained_controls": report["control_execution"]["retained_control_pass_count"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
