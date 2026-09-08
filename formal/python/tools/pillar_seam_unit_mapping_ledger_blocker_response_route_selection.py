from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qft_route_evidence_identity


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/"
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection.py"
)
HISTORICAL_SCRIPT_SHA256 = (
    "27ad363691f34279e5a9e0d0ffc916096af0f21ca189c284ff7ad005927c730c"
)
LEDGER_RELATIVE_PATH = "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json"
LEDGER_MANIFEST_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-MANIFEST-v0.json"
)
EXECUTION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_"
    "EXECUTION_20260710_v0.json"
)
ACCEPTED_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_"
    "RESULT_REVIEW_20260712_v0.json"
)
PACKET_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-PACKET-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-MANIFEST-v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260712_v0.json"
)

LEDGER_PATH = REPO_ROOT / LEDGER_RELATIVE_PATH
LEDGER_MANIFEST_PATH = REPO_ROOT / LEDGER_MANIFEST_RELATIVE_PATH
EXECUTION_REPORT_PATH = REPO_ROOT / EXECUTION_REPORT_RELATIVE_PATH
ACCEPTED_REVIEW_PATH = REPO_ROOT / ACCEPTED_REVIEW_RELATIVE_PATH
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

LEDGER_SHA256 = "a441b4764c9a27ba66df1eb9b94789b135db35d29aed5151b7bd4bc29c2de9b0"
LEDGER_MANIFEST_SHA256 = (
    "7804844617dea99df2c875d144966b0b196b08bbc884c8aa28a4c441bc7836b1"
)
EXECUTION_REPORT_SHA256 = (
    "9c32106d3220945094a32525ee7f626b32b71146c518a353955974bd386285ec"
)
ACCEPTED_REVIEW_SHA256 = (
    "268525f4646c60bab7077faa559907c581d08d08d1b2ae001c316581fd9b55f6"
)
IMPORTED_SCALAR_ACTION_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_"
    "ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json"
)
IMPORTED_SCALAR_ACTION_REVIEW_SHA256 = (
    "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509"
)
IMPORTED_SCALAR_ACTION_REVIEW_PATH = (
    REPO_ROOT / IMPORTED_SCALAR_ACTION_REVIEW_RELATIVE_PATH
)

CAPTURED_AT_UTC = "2026-07-12T00:00:00Z"
TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_"
    "blocker_response_route_selection_packet"
)
FAILURE_TARGET = (
    "diagnose_pillar_seam_unit_mapping_ledger_"
    "blocker_response_route_selection_packet_mismatch"
)
SUCCESSOR_TARGET = (
    "review_pillar_seam_unit_mapping_ledger_"
    "blocker_response_route_selection_packet_result"
)
SUCCESSOR_TARGET_KIND = (
    "pillar_seam_unit_mapping_ledger_"
    "blocker_response_route_selection_packet_result_review"
)
PACKET_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_v0"
)
MANIFEST_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_MANIFEST_v0"
)
REPORT_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260712_v0"
)
STATUS = "prepared_twelve_row_route_selection_only_resolution_not_performed"
PACKET_RESULT = (
    "TWELVE_UNIT_BLOCKERS_ROUTED_ONCE_WITHOUT_UNIT_ASSIGNMENT_"
    "OR_DIMENSIONAL_RESOLUTION_PENDING_INDEPENDENT_REVIEW"
)
STRICT_PACKET_RESULT = (
    "ROUTE_SELECTION_ONLY_NO_DIMENSIONAL_CLOSURE_NO_PILLAR_COMPLETION_"
    "NO_SEAM_ADMISSIBILITY_NO_LEVEL4_OR5_NO_PHYSICAL_CALIBRATION_"
    "NO_CROSS_SECTOR_COUPLING_VALIDATION_NO_CK_ACTION_EMBEDDING_"
    "NO_CCFT_NO_MASTER_ACTION_PROMOTION"
)

ROUTES = (
    "ACTION_DIMENSION_DERIVATION",
    "EQUATION_BALANCE_DERIVATION",
    "CONVENTION_AND_CONSTANT_RESTORATION",
    "SEAM_CONVERSION_MAP",
    "EMPIRICAL_SCALE_CALIBRATION",
    "OBJECT_SEMANTICS_REFINEMENT",
    "RESEARCH_BLOCKED",
    "DIMENSIONAL_INCOMPATIBILITY_REJECTION",
)

ROUTE_TAXONOMY = [
    {
        "route": "ACTION_DIMENSION_DERIVATION",
        "selection_condition": (
            "Use when an accepted action route identifies this work class; the "
            "successor must bind its measure and normalization before deriving "
            "dimensions in a later tranche."
        ),
    },
    {
        "route": "EQUATION_BALANCE_DERIVATION",
        "selection_condition": (
            "Use only when an authoritative governing equation can support a "
            "later non-circular term-balance derivation."
        ),
    },
    {
        "route": "CONVENTION_AND_CONSTANT_RESTORATION",
        "selection_condition": (
            "Use for hidden natural constants, normalized coordinates, or an "
            "unselected unit convention; no constant value is supplied here."
        ),
    },
    {
        "route": "SEAM_CONVERSION_MAP",
        "selection_condition": (
            "Use only after both participating pillars have independently "
            "reviewed internal unit systems."
        ),
    },
    {
        "route": "EMPIRICAL_SCALE_CALIBRATION",
        "selection_condition": (
            "Use only when a source-backed physical scale must be measured and "
            "cannot be obtained from a convention or derivation."
        ),
    },
    {
        "route": "OBJECT_SEMANTICS_REFINEMENT",
        "selection_condition": (
            "Use when the physical object must be defined more precisely before "
            "a unit question is meaningful."
        ),
    },
    {
        "route": "RESEARCH_BLOCKED",
        "selection_condition": (
            "Use when present evidence cannot authorize a derivation, calibration, "
            "conversion map, or rejection."
        ),
    },
    {
        "route": "DIMENSIONAL_INCOMPATIBILITY_REJECTION",
        "selection_condition": (
            "Use only after reviewed dimensional evidence proves that the bridge "
            "is incompatible in its present form."
        ),
    },
]

ORDERED_SELECTION_CRITERIA = [
    "Is the physical object unambiguously defined?",
    "Is the governing equation or action authoritative?",
    "Is the unit system explicit?",
    "Are coordinates physical, normalized, or dimensionless?",
    "Are natural constants suppressed?",
    "Can dimensions be derived without circularly assuming the desired bridge?",
    "Does the row require an experimental scale?",
    (
        "Does the source pillar map to the target pillar without changing "
        "physical meaning?"
    ),
    "Would the proposed resolution alter the candidate master action?",
    "Should the row remain blocked?",
]

NONCLAIMS = [
    "dimensional_closure",
    "pillar_completion",
    "seam_admissibility",
    "level_4_or_level_5",
    "physical_calibration_claims",
    "cross_sector_coupling_validation",
    "C_k_action_embedding",
    "CCFT_resumption",
    "master_action_promotion",
]

BOUNDARY = {
    "C_k_action_embedding_authorized": False,
    "ccft_resumed": False,
    "cross_sector_coupling_validation_claimed": False,
    "dimensional_closure_claimed": False,
    "level_4_or_level_5_authorized": False,
    "master_action_promoted": False,
    "physical_calibration_claimed": False,
    "pillar_completion_claimed": False,
    "route_selection_is_resolution": False,
    "seam_admissibility_claimed": False,
    "unit_assignments_emitted": 0,
    "dimension_vectors_emitted": 0,
    "conversion_constants_emitted": 0,
    "seam_mappings_emitted": 0,
}

ROUTE_EVIDENCE_ARTIFACTS = [
    {
        "artifact_id": "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0",
        "path": "formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md",
        "sha256": "3ae26471ac6b7fb0f422fc9310eab8641554f16bdcff4979e096998f87286ddc",
    },
    {
        "artifact_id": "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0",
        "path": "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md",
        "sha256": "1d9fbe0b49d45aad3781b4217dc108a6f2c16361cd59fa662c8283de10f6ac67",
    },
    {
        "artifact_id": "DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0",
        "path": "formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md",
        "sha256": "5ad933d40d8151bcef17332cd39d4e0d2dbfc3a9310da1a95f1d68f70a6b4bcc",
    },
    {
        "artifact_id": "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0",
        "path": "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
        "sha256": "524b1471880b3bef74e213fb65ee8a2f5b8033ffe3b8adee151cef08631b9f77",
    },
    {
        "artifact_id": "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0",
        "path": "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md",
        "sha256": "7b1c0bdd683e5d5891a77cf27772df239967ca210b3a7c9fd88ba75f7a1e85e9",
    },
    {
        "artifact_id": "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0",
        "path": "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "sha256": "c57729dfbf52040538bab1e1b73ce55ce5dee2c554fc8bffb050259c43fc3206",
    },
    {
        "artifact_id": "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0",
        "path": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "sha256": "edce7363ad0bbe98b8c29193762d9782d7e931cd65cfc059d609a023feafeb00",
    },
    {
        "artifact_id": "FULL_PILLAR_TARGET_MAP_REBASE_v0",
        "path": "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md",
        "sha256": "2550ca7b24e03f59535133b3856ed2d7d5094a7fd3ab5a96a5a90faaeb8eda25",
    },
    {
        "artifact_id": "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0",
        "path": IMPORTED_SCALAR_ACTION_REVIEW_RELATIVE_PATH,
        "sha256": IMPORTED_SCALAR_ACTION_REVIEW_SHA256,
    },
]
ROUTE_EVIDENCE_SHA_BY_PATH = {
    artifact["path"]: artifact["sha256"] for artifact in ROUTE_EVIDENCE_ARTIFACTS
}

ROUTE_SELECTIONS: dict[str, dict[str, Any]] = {
    "PILLAR-QFT-units_and_dimensions-v0": {
        "available_evidence": [
            "The bound QFT source identifies action, canonical-momentum, Hamiltonian, and normalization obligations.",
            (
                "The accepted QFT_GR classical coupling review authorizes an imported "
                "real-scalar action route in a provisional classical sandbox only."
            ),
        ],
        "missing_evidence": [
            "A source-backed row-wide inventory that distinguishes the exact QFT objects whose units are to be audited; the imported scalar sandbox is narrower than the pillar row."
        ],
        "selected_response_route": "OBJECT_SEMANTICS_REFINEMENT",
        "selection_reason": (
            "The accepted ledger contains no QFT quantity rows, and the imported "
            "real-scalar sandbox does not define the row-wide QFT object inventory. "
            "The physical objects must be narrowed before a later scalar-only "
            "subrow could qualify for action-dimension derivation."
        ),
        "required_source_class": "canonical_qft_unit_bearing_object_inventory_with_explicit_scope",
        "required_derivation_class": "semantic_definition_before_dimensional_analysis",
        "circularity_risk": (
            "high: the candidate master action and desired cross-pillar bridge may not "
            "be used to supply their own missing dimensions"
        ),
        "claim_impact": "planning_only_blocker_retained_no_unit_assignment",
        "successor_target": "prepare_qft_pillar_unit_object_semantics_refinement_packet",
        "forbidden_shortcut": "do_not_infer_units_from_symbol_names_or_the_candidate_master_action",
    },
    "PILLAR-GR-units_and_dimensions-v0": {
        "available_evidence": [
            "The bound GR source contains a bounded weak-field Poisson equation surface and an action-native route under explicit assumptions."
        ],
        "missing_evidence": [
            "A reviewed quantity dictionary, coordinate convention, and explicit constants for term-by-term balance."
        ],
        "selected_response_route": "EQUATION_BALANCE_DERIVATION",
        "selection_reason": (
            "The existing governing-equation surface can organize a later balance "
            "derivation without presupposing the full master action."
        ),
        "required_source_class": "accepted_governing_equation_and_quantity_semantics",
        "required_derivation_class": "term_by_term_governing_equation_dimension_balance",
        "circularity_risk": "medium: full-action claims must not be imported into the bounded weak-field surface",
        "claim_impact": "planning_only_blocker_retained_no_unit_assignment",
        "successor_target": "prepare_pillar_gr_equation_balance_dimension_derivation_guardrail_packet",
        "forbidden_shortcut": "do_not_promote_weak_field_balance_to_full_gr_dimensional_closure",
    },
    "PILLAR-QM-units_and_dimensions-v0": {
        "available_evidence": [
            "The bound QM source identifies Schrodinger-form, state, Hamiltonian, and unitarity surfaces under explicit assumptions."
        ],
        "missing_evidence": [
            "A source-backed definition of the precise state, observable, generator, and coordinate objects whose units are to be audited."
        ],
        "selected_response_route": "OBJECT_SEMANTICS_REFINEMENT",
        "selection_reason": (
            "The accepted ledger has no quantity rows, so the unit-bearing QM objects "
            "must be identified before choosing equation balance or convention restoration."
        ),
        "required_source_class": "canonical_qm_physical_object_definitions",
        "required_derivation_class": "semantic_definition_before_dimensional_analysis",
        "circularity_risk": "high: normalization and unitarity tokens are not dimensional evidence by themselves",
        "claim_impact": "planning_only_blocker_retained_no_unit_assignment",
        "successor_target": "prepare_qm_pillar_unit_object_semantics_refinement_packet",
        "forbidden_shortcut": "do_not_infer_a_state_or_observable_unit_from_schrodinger_notation_or_set_hbar_to_one",
    },
    "PILLAR-STAT-units_and_dimensions-v0": {
        "available_evidence": [
            "The bound STAT source identifies entropy-balance, probability, transport, and regime-validity obligations."
        ],
        "missing_evidence": [
            "A source-backed definition distinguishing entropy, entropy density, probability, and coarse-grained observables."
        ],
        "selected_response_route": "OBJECT_SEMANTICS_REFINEMENT",
        "selection_reason": (
            "The physical carrier is not specific enough for a meaningful unit "
            "assignment; semantics must be fixed before dimensional analysis."
        ),
        "required_source_class": "canonical_physical_object_definition",
        "required_derivation_class": "semantic_definition_before_dimensional_analysis",
        "circularity_risk": "high: target entropy semantics may not be inferred from the desired QM_STAT seam",
        "claim_impact": "planning_only_blocker_retained_no_unit_assignment",
        "successor_target": "prepare_stat_pillar_unit_object_semantics_refinement_packet",
        "forbidden_shortcut": "do_not_treat_probability_entropy_and_entropy_density_as_one_unit_bearing_object",
    },
    "PILLAR-EM-units_and_dimensions-v0": {
        "available_evidence": [
            "The bound EM source defines gauge-potential and field-strength objects but explicitly records UNITS_NOT_SELECTED."
        ],
        "missing_evidence": [
            "A selected electromagnetic unit convention and explicit constant-restoration policy."
        ],
        "selected_response_route": "CONVENTION_AND_CONSTANT_RESTORATION",
        "selection_reason": (
            "The objects are typed while the unit convention is explicitly open, so "
            "convention selection must precede any assignment or seam conversion."
        ),
        "required_source_class": "canonical_em_unit_convention_and_constant_policy",
        "required_derivation_class": "convention_audit_and_suppressed_constant_restoration",
        "circularity_risk": "medium: the EM_QFT seam may not choose the EM convention retroactively",
        "claim_impact": "planning_only_blocker_retained_no_unit_assignment",
        "successor_target": "prepare_em_pillar_unit_convention_and_constant_restoration_packet",
        "forbidden_shortcut": "do_not_mix_em_unit_systems_or_omit_required_constants",
    },
    "PILLAR-SR-units_and_dimensions-v0": {
        "available_evidence": [
            "The bound SR source records dimensional-structure checks for transforms and interval quantities."
        ],
        "missing_evidence": [
            "A reviewed declaration of physical versus normalized coordinates and the treatment of c."
        ],
        "selected_response_route": "CONVENTION_AND_CONSTANT_RESTORATION",
        "selection_reason": (
            "The unresolved issue is the coordinate and constant convention, not an "
            "authorization to declare physical distance dimensionless."
        ),
        "required_source_class": "canonical_coordinate_convention_and_constant_policy",
        "required_derivation_class": "coordinate_convention_audit_and_constant_restoration",
        "circularity_risk": "low: retain the distinction between coordinate normalization and physical dimensions",
        "claim_impact": "planning_only_blocker_retained_no_unit_assignment",
        "successor_target": "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet",
        "forbidden_shortcut": "do_not_identify_dimensionless_coordinates_with_dimensionless_physical_distance",
    },
    "PILLAR-COSMO-units_and_dimensions-v0": {
        "available_evidence": [
            "The bound COSMO source is a planning surface for background objects, source coupling, and expansion observables."
        ],
        "missing_evidence": [
            "Source-backed definitions distinguishing background coordinates, scale factor, observables, densities, and source objects."
        ],
        "selected_response_route": "OBJECT_SEMANTICS_REFINEMENT",
        "selection_reason": (
            "The planning scaffold names several different physical carriers but does "
            "not yet specify which unit-bearing object each ledger quantity would denote."
        ),
        "required_source_class": "canonical_cosmology_background_and_observable_definitions",
        "required_derivation_class": "semantic_definition_before_dimensional_analysis",
        "circularity_risk": "high: a desired local_to_global bridge may not supply the missing cosmology dimensions",
        "claim_impact": "planning_only_blocker_retained_no_unit_assignment",
        "successor_target": "prepare_cosmo_pillar_unit_object_semantics_refinement_packet",
        "forbidden_shortcut": "do_not_treat_a_normalization_scale_as_empirical_calibration_or_a_resolved_unit",
    },
}


def _seam_blocked(
    row_id: str,
    pair: str,
    prerequisite: str,
    target: str,
) -> dict[str, Any]:
    return {
        "available_evidence": [
            f"The accepted ledger preserves the {pair} seam blocker and its pillar identities."
        ],
        "missing_evidence": [
            f"Independent reviewed internal unit systems for {prerequisite}, followed by quantity-pair semantics."
        ],
        "selected_response_route": "RESEARCH_BLOCKED",
        "selection_reason": (
            "SEAM_CONVERSION_MAP is premature because both participating pillars do "
            "not yet have independently reviewed internal unit systems."
        ),
        "required_source_class": "reviewed_internal_unit_systems_for_both_pillars",
        "required_derivation_class": "none_until_both_pillar_prerequisites_are_reviewed",
        "circularity_risk": "high: the desired seam may not define either pillar's internal units",
        "claim_impact": "planning_only_seam_blocker_retained_no_mapping_or_admissibility",
        "successor_target": target,
        "forbidden_shortcut": "do_not_build_a_seam_map_while_either_pillar_unit_system_is_unknown_or_unresolved",
    }


ROUTE_SELECTIONS.update(
    {
        "SEAM-QFT-GR-unit_map-v0": _seam_blocked(
            "SEAM-QFT-GR-unit_map-v0",
            "QFT_GR",
            "QFT and GR",
            "reassess_seam_qft_gr_unit_map_route_after_qft_gr_endpoint_unit_reviews",
        ),
        "SEAM-QM-STAT-unit_map-v0": _seam_blocked(
            "SEAM-QM-STAT-unit_map-v0",
            "QM_STAT",
            "QM and STAT",
            "reassess_seam_qm_stat_unit_map_route_after_qm_stat_endpoint_unit_reviews",
        ),
        "SEAM-EM-QFT-unit_map-v0": _seam_blocked(
            "SEAM-EM-QFT-unit_map-v0",
            "EM_QFT",
            "EM and QFT",
            "reassess_seam_em_qft_unit_map_route_after_em_qft_endpoint_unit_reviews",
        ),
        "SEAM-SR-COSMO-unit_map-v0": _seam_blocked(
            "SEAM-SR-COSMO-unit_map-v0",
            "SR_COSMO",
            "SR and COSMO",
            "reassess_seam_sr_cosmo_unit_map_route_after_sr_cosmo_endpoint_unit_reviews",
        ),
        "SEAM-GR-QM-unit_map-v0": _seam_blocked(
            "SEAM-GR-QM-unit_map-v0",
            "GR_QM",
            "GR and QM",
            "reassess_seam_gr_qm_unit_map_route_after_gr_qm_endpoint_unit_reviews",
        ),
    }
)

ROW_REQUIRED_FIELDS = {
    "authority_limit",
    "available_evidence",
    "blocker_summary",
    "circularity_risk",
    "claim_impact",
    "current_status",
    "forbidden_shortcut",
    "missing_evidence",
    "required_derivation_class",
    "required_source_class",
    "row_id",
    "row_kind",
    "seam_endpoint_readiness",
    "selected_response_route",
    "selection_criteria_evaluation",
    "selection_reason",
    "source_evidence_pointer",
    "source_evidence_sha256",
    "supplemental_evidence_bindings",
    "successor_target",
}

DECISION_IDS = [
    "accepted_review_and_ledger_hashes_match",
    "exact_twelve_row_identity_status_and_evidence_bindings_preserved",
    "each_row_selects_exactly_one_primary_route",
    "route_taxonomy_is_closed_and_selection_order_is_preserved",
    "no_unit_dimension_constant_or_mapping_assignment_is_emitted",
    "unit_unknown_rows_cannot_receive_assignments_without_evidence",
    "natural_units_do_not_resolve_unresolved_rows",
    "dimensionless_coordinates_are_not_physical_distances",
    "suppressed_constants_require_explicit_restoration",
    "seam_map_requires_two_reviewed_internal_unit_systems",
    "candidate_master_action_is_not_self_supporting_evidence",
    "normalization_conventions_are_not_empirical_scales",
    "route_selection_does_not_promote_dimensional_closure",
    "C_k_embedding_remains_forbidden_before_dimensions_are_known",
    "family_level_counts_are_planning_counts_only",
    "all_nonclaims_and_claim_ceiling_boundaries_are_preserved",
]


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _load_json(path: Path, expected_sha256: str) -> dict[str, Any]:
    _require(path.is_file(), f"required input is missing: {path}")
    raw = path.read_bytes()
    _require(sha256_bytes(raw) == expected_sha256, f"input hash mismatch: {path}")
    payload = json.loads(raw)
    _require(isinstance(payload, dict), f"input root is not an object: {path}")
    return payload


def load_inputs() -> tuple[dict[str, Any], dict[str, Any]]:
    ledger = _load_json(LEDGER_PATH, LEDGER_SHA256)
    _load_json(LEDGER_MANIFEST_PATH, LEDGER_MANIFEST_SHA256)
    _load_json(EXECUTION_REPORT_PATH, EXECUTION_REPORT_SHA256)
    review = _load_json(ACCEPTED_REVIEW_PATH, ACCEPTED_REVIEW_SHA256)
    _require(review.get("accepted") is True, "formal ledger review is not accepted")
    _require(
        review.get("selected_next_target") == TARGET,
        "accepted review does not authorize this route-selection target",
    )
    _require(review.get("boundary") == {
        "C_k_action_embedding_authorized": False,
        "ccft_resumed": False,
        "cross_sector_coupling_claim_authorized": False,
        "dimensional_closure_claimed": False,
        "level_4_or_level_5_authorized": False,
        "master_action_promoted": False,
        "physical_calibration_authorized": False,
        "pillar_completion_claimed": False,
        "seam_admissibility_claimed": False,
        "seam_closure_claimed": False,
        "unit_closure_claimed": False,
    }, "accepted review boundary differs from the frozen nonclaim boundary")
    qft_route_evidence_identity.verify_route_evidence(
        [artifact["path"] for artifact in ROUTE_EVIDENCE_ARTIFACTS],
        expected_historical_sha_by_path=ROUTE_EVIDENCE_SHA_BY_PATH,
        repo_root=REPO_ROOT,
    )
    imported_review = json.loads(IMPORTED_SCALAR_ACTION_REVIEW_PATH.read_bytes())
    _require(
        imported_review.get("accepted") is True
        and imported_review.get("provisional_classical_sandbox_route_only") is True
        and imported_review.get("master_action_promoted") is False
        and imported_review.get("toe_native_matter_derivation_claimed") is False
        and imported_review.get("classical_einstein_scalar_coupling_route_reviewed")
        is True,
        "imported scalar-action review does not preserve its bounded authority",
    )
    return ledger, review


def _ledger_rows(ledger: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    return [
        *[("pillar", row) for row in ledger["pillar_rows"]],
        *[("seam", row) for row in ledger["seam_rows"]],
    ]


def _criteria_evaluation(
    row_kind: str, ledger_row: dict[str, Any], selection: dict[str, Any]
) -> list[dict[str, Any]]:
    route = selection["selected_response_route"]
    row_id = ledger_row["row_id"]
    if row_kind == "seam":
        object_answer = "no: no source-to-target quantity pairs are defined"
        authority_answer = "no: endpoint unit systems are not both independently reviewed"
        noncircular_answer = "no: a desired seam may not supply either endpoint's internal units"
        meaning_answer = "not yet: cross-pillar physical-meaning preservation is unproved"
    elif route == "OBJECT_SEMANTICS_REFINEMENT":
        object_answer = "no: the unit-bearing physical object requires semantic refinement"
        authority_answer = "insufficient for units: planning or theorem surfaces do not define the required quantity inventory"
        noncircular_answer = "not yet: object semantics must be fixed first"
        meaning_answer = "not applicable to this pillar-only route"
    elif route == "CONVENTION_AND_CONSTANT_RESTORATION":
        object_answer = "partly: the principal objects are identified but their unit or coordinate convention is open"
        authority_answer = "yes for identifying the convention gap; no convention is selected by this packet"
        noncircular_answer = "not a derivation route: convention restoration must precede dimensional conclusions"
        meaning_answer = "not applicable to this pillar-only route"
    elif row_id == "PILLAR-QFT-units_and_dimensions-v0":
        object_answer = "no at row-wide scope: only the imported real-scalar field is bounded; wider QFT objects remain undefined"
        authority_answer = "bounded scalar-action authority exists only for a later narrowed scalar subrow, not the full QFT row"
        noncircular_answer = "not yet: the row-wide physical objects must be refined before any derivation route is selected"
        meaning_answer = "not applicable to this pillar-only route"
    else:
        object_answer = "partly: bounded weak-field quantities are identified"
        authority_answer = "yes only for the bounded governing-equation surface under its retained assumptions"
        noncircular_answer = "yes in a later tranche by term balance without importing full-action conclusions"
        meaning_answer = "not applicable to this pillar-only route"

    answers = [
        object_answer,
        authority_answer,
        "no: the accepted ledger records no explicit row-level unit system",
        "not established: physical, normalized, and dimensionless coordinates remain distinguished",
        "not established: suppressed constants require an explicit restoration audit",
        noncircular_answer,
        "no empirical scale is established or selected by current evidence",
        meaning_answer,
        "no: this planning route may not alter or validate the candidate master action",
        "yes: the row remains blocked until routed work and independent review are complete",
    ]
    return [
        {
            "answer": answer,
            "criterion": criterion,
            "criterion_number": number,
        }
        for number, (criterion, answer) in enumerate(
            zip(ORDERED_SELECTION_CRITERIA, answers, strict=True), start=1
        )
    ]


def _endpoint_readiness(
    row_kind: str, ledger_row: dict[str, Any], ledger: dict[str, Any]
) -> dict[str, Any]:
    if row_kind != "seam":
        return {
            "applicable": False,
            "both_internal_unit_systems_reviewed": False,
            "endpoints": [],
        }
    pillar_rows = {row["pillar_id"]: row for row in ledger["pillar_rows"]}
    endpoints = [
        {
            "current_status": pillar_rows[pillar_id]["guardrail_unit_state"],
            "internal_unit_system_reviewed": False,
            "pillar_id": pillar_id,
        }
        for pillar_id in ledger_row["pillar_ids"]
    ]
    return {
        "applicable": True,
        "both_internal_unit_systems_reviewed": False,
        "endpoints": endpoints,
    }


def _route_row(
    row_kind: str, ledger_row: dict[str, Any], ledger: dict[str, Any]
) -> dict[str, Any]:
    row_id = ledger_row["row_id"]
    selection = copy.deepcopy(ROUTE_SELECTIONS[row_id])
    supplemental = []
    authority_limit = "planning_route_only_no_unit_resolution_no_master_action_authority"
    if row_id == "PILLAR-QFT-units_and_dimensions-v0":
        supplemental = [
            copy.deepcopy(ROUTE_EVIDENCE_ARTIFACTS[-1])
        ]
        authority_limit = (
            "accepted_imported_real_scalar_action_only_no_candidate_master_action_"
            "no_ToE_native_phi_no_wider_QFT_authority"
        )
    return {
        **selection,
        "authority_limit": authority_limit,
        "blocker_summary": ledger_row["unresolved_items"][0]["reason"],
        "current_status": ledger_row["guardrail_unit_state"],
        "row_id": row_id,
        "row_kind": row_kind,
        "seam_endpoint_readiness": _endpoint_readiness(
            row_kind, ledger_row, ledger
        ),
        "selection_criteria_evaluation": _criteria_evaluation(
            row_kind, ledger_row, selection
        ),
        "source_evidence_pointer": ledger_row["evidence_pointer"],
        "source_evidence_sha256": ROUTE_EVIDENCE_SHA_BY_PATH[
            ledger_row["evidence_pointer"]
        ],
        "supplemental_evidence_bindings": supplemental,
    }


def _family_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    counts = Counter(row["selected_response_route"] for row in rows)
    return {
        "action_derivations_required": counts["ACTION_DIMENSION_DERIVATION"],
        "equation_balance_derivations_required": counts["EQUATION_BALANCE_DERIVATION"],
        "convention_restorations_required": counts["CONVENTION_AND_CONSTANT_RESTORATION"],
        "seam_maps_required": counts["SEAM_CONVERSION_MAP"],
        "empirical_calibrations_required": counts["EMPIRICAL_SCALE_CALIBRATION"],
        "semantic_clarifications_required": counts["OBJECT_SEMANTICS_REFINEMENT"],
        "research_blocked_routes_required": counts["RESEARCH_BLOCKED"],
        "rows_remaining_blocked": sum(
            row.get("current_status") in {"unit_unknown", "unresolved"}
            for row in rows
        ),
        "rows_rejected": counts["DIMENSIONAL_INCOMPATIBILITY_REJECTION"],
        "total_rows": len(rows),
    }


def _input_bindings() -> list[dict[str, str]]:
    return [
        {
            "artifact_id": "PILLAR_SEAM_UNIT_MAPPING_LEDGER_v0",
            "path": LEDGER_RELATIVE_PATH,
            "sha256": LEDGER_SHA256,
        },
        {
            "artifact_id": "PILLAR_SEAM_UNIT_MAPPING_LEDGER_MANIFEST_v0",
            "path": LEDGER_MANIFEST_RELATIVE_PATH,
            "sha256": LEDGER_MANIFEST_SHA256,
        },
        {
            "artifact_id": "PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTION_20260710_v0",
            "path": EXECUTION_REPORT_RELATIVE_PATH,
            "sha256": EXECUTION_REPORT_SHA256,
        },
        {
            "artifact_id": "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_20260712_v0",
            "path": ACCEPTED_REVIEW_RELATIVE_PATH,
            "sha256": ACCEPTED_REVIEW_SHA256,
        },
        *copy.deepcopy(ROUTE_EVIDENCE_ARTIFACTS),
    ]


def build_packet(ledger: dict[str, Any] | None = None) -> dict[str, Any]:
    if ledger is None:
        ledger, _ = load_inputs()
    rows = [_route_row(kind, row, ledger) for kind, row in _ledger_rows(ledger)]
    return {
        "boundary": copy.deepcopy(BOUNDARY),
        "captured_at_utc": CAPTURED_AT_UTC,
        "claim_ceiling_level": 3,
        "family_level_counts": _family_counts(rows),
        "failure_target": FAILURE_TARGET,
        "input_artifacts": _input_bindings(),
        "nonclaims": copy.deepcopy(NONCLAIMS),
        "ordered_selection_criteria": copy.deepcopy(ORDERED_SELECTION_CRITERIA),
        "packet_result": PACKET_RESULT,
        "policy": {
            "candidate_master_action_self_support_allowed": False,
            "dimensionless_coordinates_are_physical_distances": False,
            "normalization_convention_is_empirical_scale": False,
            "route_selection_resolves_blocker": False,
            "suppressed_constant_omission_allowed": False,
            "suppressed_constants_requiring_explicit_treatment": [
                "c",
                "hbar",
                "G",
                "k_B",
            ],
            "unit_or_dimension_assignment_authorized": False,
        },
        "route_count": len(ROUTES),
        "route_selections": rows,
        "route_taxonomy": copy.deepcopy(ROUTE_TAXONOMY),
        "schema_id": PACKET_SCHEMA_ID,
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "status": STATUS,
        "strict_packet_result": STRICT_PACKET_RESULT,
        "target": TARGET,
        "total_row_count": 12,
    }


def _contains_assignment_keys(value: Any) -> bool:
    prohibited = {
        "assigned_unit",
        "declared_unit",
        "dimension_vector",
        "conversion_constant",
        "conversion_map",
        "restoration_map",
        "proposed_unit_assignment",
    }
    if isinstance(value, dict):
        return bool(prohibited & set(value)) or any(
            _contains_assignment_keys(item) for item in value.values()
        )
    if isinstance(value, list):
        return any(_contains_assignment_keys(item) for item in value)
    return False


def packet_validation_failures(
    packet: dict[str, Any], ledger: dict[str, Any]
) -> list[str]:
    failed: set[str] = set()
    rows = packet.get("route_selections")
    if not isinstance(rows, list):
        rows = []
    expected_ledger_rows = {
        row["row_id"]: (kind, row) for kind, row in _ledger_rows(ledger)
    }
    observed_by_id = {
        row.get("row_id"): row
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("row_id"), str)
    }

    input_ok = packet.get("input_artifacts") == _input_bindings()
    input_ok = input_ok and (
        qft_route_evidence_identity.bindings_match_declared_identities(
            _input_bindings(),
            repo_root=REPO_ROOT,
        )
    )
    if not input_ok:
        failed.add("accepted_review_and_ledger_hashes_match")

    identity_ok = (
        len(rows) == 12
        and packet.get("total_row_count") == 12
        and set(observed_by_id) == set(expected_ledger_rows)
        and len(observed_by_id) == len(rows)
    )
    if identity_ok:
        for row_id, (kind, source) in expected_ledger_rows.items():
            observed = observed_by_id[row_id]
            if not (
                set(observed) == ROW_REQUIRED_FIELDS
                and observed == _route_row(kind, source, ledger)
                and observed.get("row_kind") == kind
                and observed.get("current_status") == source["guardrail_unit_state"]
                and observed.get("source_evidence_pointer") == source["evidence_pointer"]
                and observed.get("blocker_summary")
                == source["unresolved_items"][0]["reason"]
            ):
                identity_ok = False
                break
    if not identity_ok:
        failed.add("exact_twelve_row_identity_status_and_evidence_bindings_preserved")

    one_route_ok = all(
        isinstance(row.get("selected_response_route"), str)
        and row["selected_response_route"] in ROUTES
        and row.get("row_id") in ROUTE_SELECTIONS
        and row["selected_response_route"]
        == ROUTE_SELECTIONS[row["row_id"]]["selected_response_route"]
        for row in rows
        if isinstance(row, dict)
    ) and len(rows) == 12
    if not one_route_ok:
        failed.add("each_row_selects_exactly_one_primary_route")

    if not (
        packet.get("route_count") == 8
        and packet.get("route_taxonomy") == ROUTE_TAXONOMY
        and packet.get("ordered_selection_criteria") == ORDERED_SELECTION_CRITERIA
    ):
        failed.add("route_taxonomy_is_closed_and_selection_order_is_preserved")

    boundary = packet.get("boundary")
    policy = packet.get("policy")
    if not isinstance(boundary, dict):
        boundary = {}
    if not isinstance(policy, dict):
        policy = {}
    assignment_free = (
        not _contains_assignment_keys(packet)
        and boundary.get("unit_assignments_emitted") == 0
        and boundary.get("dimension_vectors_emitted") == 0
        and boundary.get("conversion_constants_emitted") == 0
        and boundary.get("seam_mappings_emitted") == 0
        and policy.get("unit_or_dimension_assignment_authorized") is False
    )
    if not assignment_free:
        failed.add("no_unit_dimension_constant_or_mapping_assignment_is_emitted")
    if not assignment_free or any(
        row.get("current_status") == "unit_unknown"
        and any(key in row for key in ("assigned_unit", "dimension_vector", "proposed_unit_assignment"))
        for row in rows
        if isinstance(row, dict)
    ):
        failed.add("unit_unknown_rows_cannot_receive_assignments_without_evidence")

    if not (
        policy.get("route_selection_resolves_blocker") is False
        and all(
            row.get("current_status") in {"unit_unknown", "unresolved"}
            for row in rows
            if isinstance(row, dict)
        )
    ):
        failed.add("natural_units_do_not_resolve_unresolved_rows")
    if policy.get("dimensionless_coordinates_are_physical_distances") is not False:
        failed.add("dimensionless_coordinates_are_not_physical_distances")
    if not (
        policy.get("suppressed_constant_omission_allowed") is False
        and policy.get("suppressed_constants_requiring_explicit_treatment")
        == ["c", "hbar", "G", "k_B"]
    ):
        failed.add("suppressed_constants_require_explicit_restoration")

    seam_prerequisite_ok = True
    pillar_status = {
        row["pillar_id"]: row["guardrail_unit_state"] for row in ledger["pillar_rows"]
    }
    ledger_seams = {row["row_id"]: row for row in ledger["seam_rows"]}
    for row in rows:
        if not isinstance(row, dict) or row.get("row_kind") != "seam":
            continue
        if row.get("selected_response_route") == "SEAM_CONVERSION_MAP":
            source = ledger_seams.get(row.get("row_id"))
            if source is None or any(
                pillar_status.get(pillar_id) != "resolved"
                for pillar_id in source["pillar_ids"]
            ):
                seam_prerequisite_ok = False
    if not seam_prerequisite_ok:
        failed.add("seam_map_requires_two_reviewed_internal_unit_systems")

    if policy.get("candidate_master_action_self_support_allowed") is not False or any(
        "candidate master action" in evidence.lower()
        for row in rows
        if isinstance(row, dict)
        for evidence in row.get("available_evidence", [])
        if isinstance(evidence, str)
    ):
        failed.add("candidate_master_action_is_not_self_supporting_evidence")
    if policy.get("normalization_convention_is_empirical_scale") is not False:
        failed.add("normalization_conventions_are_not_empirical_scales")

    if not (
        packet.get("claim_ceiling_level") == 3
        and boundary.get("route_selection_is_resolution") is False
        and boundary.get("dimensional_closure_claimed") is False
        and boundary.get("pillar_completion_claimed") is False
        and boundary.get("seam_admissibility_claimed") is False
    ):
        failed.add("route_selection_does_not_promote_dimensional_closure")
    if boundary.get("C_k_action_embedding_authorized") is not False:
        failed.add("C_k_embedding_remains_forbidden_before_dimensions_are_known")

    try:
        counts_ok = packet.get("family_level_counts") == _family_counts(rows)
        counts_ok = counts_ok and packet["family_level_counts"] == {
        "action_derivations_required": 0,
            "equation_balance_derivations_required": 1,
            "convention_restorations_required": 2,
            "seam_maps_required": 0,
            "empirical_calibrations_required": 0,
            "semantic_clarifications_required": 4,
            "research_blocked_routes_required": 5,
            "rows_remaining_blocked": 12,
            "rows_rejected": 0,
            "total_rows": 12,
        }
    except (KeyError, TypeError):
        counts_ok = False
    if not counts_ok:
        failed.add("family_level_counts_are_planning_counts_only")

    if not (
        packet.get("schema_id") == PACKET_SCHEMA_ID
        and packet.get("captured_at_utc") == CAPTURED_AT_UTC
        and packet.get("target") == TARGET
        and packet.get("failure_target") == FAILURE_TARGET
        and packet.get("status") == STATUS
        and packet.get("packet_result") == PACKET_RESULT
        and packet.get("strict_packet_result") == STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == SUCCESSOR_TARGET
        and packet.get("selected_next_target_kind") == SUCCESSOR_TARGET_KIND
        and packet.get("nonclaims") == NONCLAIMS
        and boundary == BOUNDARY
    ):
        failed.add("all_nonclaims_and_claim_ceiling_boundaries_are_preserved")

    return [decision_id for decision_id in DECISION_IDS if decision_id in failed]


def _mutate(
    packet: dict[str, Any], mutation: Callable[[dict[str, Any]], None]
) -> dict[str, Any]:
    changed = copy.deepcopy(packet)
    mutation(changed)
    return changed


def run_negative_controls(
    packet: dict[str, Any], ledger: dict[str, Any]
) -> list[dict[str, Any]]:
    controls: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        (
            "assign_unit_to_unit_unknown_without_evidence",
            "unit_unknown_rows_cannot_receive_assignments_without_evidence",
            lambda value: value["route_selections"][0].__setitem__(
                "proposed_unit_assignment", "invented"
            ),
        ),
        (
            "natural_units_mark_unresolved_resolved",
            "natural_units_do_not_resolve_unresolved_rows",
            lambda value: value["route_selections"][1].update(
                {
                    "current_status": "resolved",
                    "resolution_basis": "natural_units_assumed_without_restoration",
                }
            ),
        ),
        (
            "dimensionless_coordinates_promoted_to_physical_distance",
            "dimensionless_coordinates_are_not_physical_distances",
            lambda value: value["policy"].__setitem__(
                "dimensionless_coordinates_are_physical_distances", True
            ),
        ),
        (
            "suppressed_constant_omitted",
            "suppressed_constants_require_explicit_restoration",
            lambda value: value["policy"].update(
                {
                    "suppressed_constant_omission_allowed": True,
                    "suppressed_constants_requiring_explicit_treatment": [],
                }
            ),
        ),
        (
            "two_incompatible_routes_assigned_without_priority",
            "each_row_selects_exactly_one_primary_route",
            lambda value: value["route_selections"][0].__setitem__(
                "selected_response_route",
                ["ACTION_DIMENSION_DERIVATION", "EQUATION_BALANCE_DERIVATION"],
            ),
        ),
        (
            "seam_map_selected_with_incomplete_pillar_units",
            "seam_map_requires_two_reviewed_internal_unit_systems",
            lambda value: value["route_selections"][7].__setitem__(
                "selected_response_route", "SEAM_CONVERSION_MAP"
            ),
        ),
        (
            "candidate_master_action_used_as_self_evidence",
            "candidate_master_action_is_not_self_supporting_evidence",
            lambda value: value["route_selections"][0]["available_evidence"].append(
                "The candidate master action supplies its own missing dimensions."
            ),
        ),
        (
            "normalization_convention_promoted_to_empirical_scale",
            "normalization_conventions_are_not_empirical_scales",
            lambda value: value["policy"].__setitem__(
                "normalization_convention_is_empirical_scale", True
            ),
        ),
        (
            "routed_blocker_promoted_to_dimensional_closure",
            "route_selection_does_not_promote_dimensional_closure",
            lambda value: value["boundary"].__setitem__(
                "dimensional_closure_claimed", True
            ),
        ),
        (
            "C_k_embedding_before_dimensions_known",
            "C_k_embedding_remains_forbidden_before_dimensions_are_known",
            lambda value: value["boundary"].__setitem__(
                "C_k_action_embedding_authorized", True
            ),
        ),
    ]
    results = []
    for control_id, expected, mutation in controls:
        failures = packet_validation_failures(_mutate(packet, mutation), ledger)
        results.append(
            {
                "control_id": control_id,
                "expected_failed_decision_id": expected,
                "fresh_deep_copy_used": True,
                "observed_failed_decision_ids": failures,
                "passed": expected in failures,
            }
        )
    return results


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    ledger, _ = load_inputs()
    packet = build_packet(ledger)
    failures = packet_validation_failures(packet, ledger)
    _require(not failures, f"canonical packet failed decisions: {failures}")
    controls = run_negative_controls(packet, ledger)
    _require(all(item["passed"] for item in controls), "negative control failure")

    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "captured_at_utc": CAPTURED_AT_UTC,
        "canonicalization": "UTF-8 JSON, sorted keys, indent=2, trailing newline",
        "generator": {
            "path": SCRIPT_RELATIVE_PATH,
            "sha256": HISTORICAL_SCRIPT_SHA256,
        },
        "input_artifacts": _input_bindings(),
        "packet": {
            "path": PACKET_RELATIVE_PATH,
            "schema_id": PACKET_SCHEMA_ID,
            "sha256": sha256_bytes(packet_raw),
        },
        "route_count": len(ROUTES),
        "schema_id": MANIFEST_SCHEMA_ID,
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "total_row_count": 12,
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "all_decisions_passed": True,
        "all_negative_controls_passed": True,
        "artifact_hashes": {
            "manifest_sha256": sha256_bytes(manifest_raw),
            "packet_sha256": sha256_bytes(packet_raw),
        },
        "boundary": copy.deepcopy(BOUNDARY),
        "captured_at_utc": CAPTURED_AT_UTC,
        "claim": (
            "All twelve accepted unit blockers receive exactly one planning route; "
            "no unit, dimension, constant, calibration, or seam mapping is derived."
        ),
        "decision_count": len(DECISION_IDS),
        "decisions": [
            {"decision_id": decision_id, "passed": True}
            for decision_id in DECISION_IDS
        ],
        "family_level_counts": copy.deepcopy(packet["family_level_counts"]),
        "failure_target": FAILURE_TARGET,
        "input_artifacts": _input_bindings(),
        "negative_control_count": len(controls),
        "negative_controls": controls,
        "nonclaims": copy.deepcopy(NONCLAIMS),
        "packet_result": PACKET_RESULT,
        "schema_id": REPORT_SCHEMA_ID,
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "status": STATUS,
        "strict_packet_result": STRICT_PACKET_RESULT,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def _check(path: Path, payload: dict[str, Any]) -> bool:
    return path.is_file() and path.read_bytes() == canonical_json_bytes(payload)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build the bounded pillar/seam unit-blocker response-route packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="write all three artifacts")
    mode.add_argument("--check", action="store_true", help="check repository artifacts")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [
        (PACKET_PATH, packet),
        (MANIFEST_PATH, manifest),
        (REPORT_PATH, report),
    ]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print(
            "wrote blocker-response route-selection packet, manifest, and report; "
            "12 rows routed, 0 resolved"
        )
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not _check(path, payload)]
        if stale:
            print("stale or missing artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(
            "blocker-response route-selection artifacts verified; "
            "16/16 decisions and 10/10 controls pass"
        )
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
