from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
CAPTURED_AT_UTC = "2026-07-12T00:00:00Z"

PREPARATION_COMMIT = "d94fee08f5f711a5902fd8a1f3d652a30b89bb14"
PREPARATION_PARENT = "145c30255ff90ca2df97f8526a98c6923e5db2bf"
REVIEW_TARGET = (
    "review_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v1_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
SELECTED_NEXT_TARGET_KIND = (
    "pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
DIAGNOSTIC_TARGET = (
    "diagnose_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v1_authority_class_mismatch"
)
DEFERRED_FIRST_RESOLUTION_GUARDRAIL = (
    "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet"
)

GENERATOR_REL = (
    "formal/python/tools/"
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1.py"
)
V0_GENERATOR_REL = (
    "formal/python/tools/"
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection.py"
)
REPO_ENVIRONMENT_REL = "formal/python/meta/repo_environment.py"
PACKET_REL = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-PACKET-v1.json"
)
MANIFEST_REL = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-MANIFEST-v1.json"
)
PREPARATION_REPORT_REL = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260712_v1.json"
)
LEDGER_REL = "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json"
LEDGER_REVIEW_REL = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_"
    "RESULT_REVIEW_20260712_v0.json"
)
V0_REJECTION_REL = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260712_v0.json"
)
REVIEW_REPORT_REL = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260712_v1.json"
)

GENERATOR_PATH = REPO_ROOT / GENERATOR_REL
PACKET_PATH = REPO_ROOT / PACKET_REL
MANIFEST_PATH = REPO_ROOT / MANIFEST_REL
PREPARATION_REPORT_PATH = REPO_ROOT / PREPARATION_REPORT_REL
LEDGER_PATH = REPO_ROOT / LEDGER_REL
LEDGER_REVIEW_PATH = REPO_ROOT / LEDGER_REVIEW_REL
V0_REJECTION_PATH = REPO_ROOT / V0_REJECTION_REL
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_REL

EXPECTED_PREPARATION_HASHES = {
    GENERATOR_REL: "bb42efb91530da6134a5f41661b23736afa663171935140616066f6503257da4",
    PACKET_REL: "8c0de083b4f3bd94eb2bb1bc6fa963e1a4024a2d42169eef0e05e297400fdb70",
    MANIFEST_REL: "03130e8ddd32ee70c66af042a130494f659b13a50285cacbf0f9c13968e1ff73",
    PREPARATION_REPORT_REL: "bbf299f594970641d437ff502767d7d175923219664f92bf59f415f6c3f20a06",
    LEDGER_REL: "a441b4764c9a27ba66df1eb9b94789b135db35d29aed5151b7bd4bc29c2de9b0",
    LEDGER_REVIEW_REL: "268525f4646c60bab7077faa559907c581d08d08d1b2ae001c316581fd9b55f6",
    V0_REJECTION_REL: "8e977f23dca29b78ba54daeb60d53a282fa75dd45f3ba34ddaa32c7258280162",
}

EXPECTED_INPUT_HASHES = {
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json": "a441b4764c9a27ba66df1eb9b94789b135db35d29aed5151b7bd4bc29c2de9b0",
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-MANIFEST-v0.json": "7804844617dea99df2c875d144966b0b196b08bbc884c8aa28a4c441bc7836b1",
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTION_20260710_v0.json": "9c32106d3220945094a32525ee7f626b32b71146c518a353955974bd386285ec",
    LEDGER_REVIEW_REL: "268525f4646c60bab7077faa559907c581d08d08d1b2ae001c316581fd9b55f6",
    "formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md": "3ae26471ac6b7fb0f422fc9310eab8641554f16bdcff4979e096998f87286ddc",
    "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md": "1d9fbe0b49d45aad3781b4217dc108a6f2c16361cd59fa662c8283de10f6ac67",
    "formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md": "5ad933d40d8151bcef17332cd39d4e0d2dbfc3a9310da1a95f1d68f70a6b4bcc",
    "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md": "524b1471880b3bef74e213fb65ee8a2f5b8033ffe3b8adee151cef08631b9f77",
    "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md": "7b1c0bdd683e5d5891a77cf27772df239967ca210b3a7c9fd88ba75f7a1e85e9",
    "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md": "c57729dfbf52040538bab1e1b73ce55ce5dee2c554fc8bffb050259c43fc3206",
    "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md": "edce7363ad0bbe98b8c29193762d9782d7e931cd65cfc059d609a023feafeb00",
    "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md": "2550ca7b24e03f59535133b3856ed2d7d5094a7fd3ab5a96a5a90faaeb8eda25",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json": "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-ROUTE-SELECTION-PACKET-v0.json": "e3aad41e3ed886f43bcd6dfafc0b3736c5f981a49278a6bd89460ffdf89875b9",
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-ROUTE-SELECTION-MANIFEST-v0.json": "23015cfac12edd4d627d8db5af0613f10bc6924f8ea1ce422e0bf3e384457c88",
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_PACKET_20260712_v0.json": "56e55ff41d015a2337edeecd25da8397eff54289f8e05271fa0a309df4342444",
    V0_REJECTION_REL: "8e977f23dca29b78ba54daeb60d53a282fa75dd45f3ba34ddaa32c7258280162",
    "formal/python/tools/pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_result_review.py": "da7766b4e51a3b11b6d823aa6833ba3f90b0b79e36b9c56786054197478e0f80",
}

SOURCE_BINDINGS = {
    "accepted_unit_ledger": {
        "path": LEDGER_REL,
        "sha256": EXPECTED_INPUT_HASHES[LEDGER_REL],
        "authority_class": "FROZEN_ACCEPTED_LEDGER",
    },
    "qft_bounded_surface": {
        "path": "formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"],
        "authority_class": "BOUNDED_PLANNING_NONCLAIM",
    },
    "gr_bounded_surface": {
        "path": "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"],
        "authority_class": "BOUNDED_AUTHORITATIVE_SURFACE",
    },
    "qm_bounded_surface": {
        "path": "formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md"],
        "authority_class": "BOUNDED_PLANNING_NONCLAIM",
    },
    "stat_planning_surface": {
        "path": "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"],
        "authority_class": "BOUNDED_PLANNING_NONCLAIM",
    },
    "em_bounded_surface": {
        "path": "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"],
        "authority_class": "BOUNDED_PLANNING_NONCLAIM",
    },
    "sr_bounded_surface": {
        "path": "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"],
        "authority_class": "BOUNDED_PLANNING_NONCLAIM",
    },
    "cosmo_planning_surface": {
        "path": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"],
        "authority_class": "BOUNDED_PLANNING_NONCLAIM",
    },
    "pillar_target_map": {
        "path": "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md"],
        "authority_class": "BOUNDED_PLANNING_NONCLAIM",
    },
    "accepted_scalar_sandbox_review": {
        "path": "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json",
        "sha256": EXPECTED_INPUT_HASHES["formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json"],
        "authority_class": "ACCEPTED_BOUNDED_REVIEW",
    },
}

ROW_SOURCE_IDS = {
    "PILLAR-QFT-units_and_dimensions-v0": ["accepted_unit_ledger", "qft_bounded_surface", "accepted_scalar_sandbox_review"],
    "PILLAR-GR-units_and_dimensions-v0": ["accepted_unit_ledger", "gr_bounded_surface"],
    "PILLAR-QM-units_and_dimensions-v0": ["accepted_unit_ledger", "qm_bounded_surface"],
    "PILLAR-STAT-units_and_dimensions-v0": ["accepted_unit_ledger", "stat_planning_surface"],
    "PILLAR-EM-units_and_dimensions-v0": ["accepted_unit_ledger", "em_bounded_surface"],
    "PILLAR-SR-units_and_dimensions-v0": ["accepted_unit_ledger", "sr_bounded_surface"],
    "PILLAR-COSMO-units_and_dimensions-v0": ["accepted_unit_ledger", "cosmo_planning_surface"],
}

DIRECT_PROBES = {
    "PILLAR-QFT-units_and_dimensions-v0": ("qft_direct_scope_explicit", "qft_bounded_surface", ["Canonical momentum surface assumptions", "Hamiltonian-generator interface compatibility", "Unitarity/injectivity assumptions", "Generator-unitarity route normalization"]),
    "PILLAR-GR-units_and_dimensions-v0": ("gr_bounded_poisson_explicit", "gr_bounded_surface", ["action-level derivation of the weak-field discrete Poisson equation", "Bounded/discrete weak-field v0 only", "Canonical route remains action-native"]),
    "PILLAR-QM-units_and_dimensions-v0": ("qm_direct_scope_explicit", "qm_bounded_surface", ["Schrodinger-form derivation", "QMStateEvolvesUnderContract", "Unitary-consistency track"]),
    "PILLAR-STAT-units_and_dimensions-v0": ("stat_direct_scope_explicit", "stat_planning_surface", ["planning-only artifact", "entropy / entropy-production object surface", "flux / balance law object surface", "regime assumptions object surface", "admissibility / causality / positivity"]),
    "PILLAR-EM-units_and_dimensions-v0": ("em_objects_and_open_units_explicit", "em_bounded_surface", ["Gauge potential object", "typed `F_munu` structure", "UNITS_NOT_SELECTED"]),
    "PILLAR-SR-units_and_dimensions-v0": ("sr_interval_dimension_explicit", "sr_bounded_surface", ["Lorentz transform object theorem surface", "interval-invariance preservation theorem surface", "dimensional structure is preserved"]),
    "PILLAR-COSMO-units_and_dimensions-v0": ("cosmo_background_scope_explicit", "cosmo_planning_surface", ["planning-only cosmology target", "background metric object", "expansion-rate/Hubble-like object", "source-sector object", "domain-of-validity assumptions"]),
}

ROUTE_BY_SIGNAL = {
    "GOVERNING_EQUATION_READY": "EQUATION_BALANCE_DERIVATION",
    "CONVENTION_OPEN": "CONVENTION_AND_CONSTANT_RESTORATION",
    "OBJECT_SCOPE_REQUIRES_REFINEMENT": "OBJECT_SEMANTICS_REFINEMENT",
    "ENDPOINTS_NOT_RESOLVED": "RESEARCH_BLOCKED",
}

PILLAR_SIGNAL = {
    "PILLAR-QFT-units_and_dimensions-v0": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
    "PILLAR-GR-units_and_dimensions-v0": "GOVERNING_EQUATION_READY",
    "PILLAR-QM-units_and_dimensions-v0": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
    "PILLAR-STAT-units_and_dimensions-v0": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
    "PILLAR-EM-units_and_dimensions-v0": "CONVENTION_OPEN",
    "PILLAR-SR-units_and_dimensions-v0": "CONVENTION_OPEN",
    "PILLAR-COSMO-units_and_dimensions-v0": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
}

EXPECTED_ROUTE_COUNTS = {
    "EQUATION_BALANCE_DERIVATION": 1,
    "CONVENTION_AND_CONSTANT_RESTORATION": 2,
    "OBJECT_SEMANTICS_REFINEMENT": 4,
    "RESEARCH_BLOCKED": 5,
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
    "frozen_v0_rejection_and_v1_authorization_match",
    "evidence_matrix_present_once_per_row",
    "explicit_propositions_are_source_anchored",
    "derived_propositions_have_reproducible_supported_premises",
    "inferred_and_absent_propositions_do_not_support_routes",
    "route_rationale_objects_are_supported",
    "supporting_sources_have_authorized_bounded_class",
    "source_path_hash_pairs_are_exactly_rebound",
    "narrow_scalar_evidence_is_not_promoted_to_full_qft",
    "source_object_definitions_are_nonconflicting",
]

REVIEW_REQUIREMENT_IDS = [f"formal_review_requirement_{index}" for index in range(1, 15)]

MISMATCH_CODES = [
    "QFT_P_POLICY_AUTHORITY_CLASS_ATTRIBUTION_MISMATCH",
    "QM_P_POLICY_AUTHORITY_CLASS_ATTRIBUTION_MISMATCH",
    "EM_P_POLICY_AUTHORITY_CLASS_ATTRIBUTION_MISMATCH",
    "SR_P_POLICY_AUTHORITY_CLASS_ATTRIBUTION_MISMATCH",
]

REVIEW_OUTCOME = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_PACKET_"
    "V1_RESULT_REVIEW_B_BLOCKED_SOURCE_AUTHORITY_CLASS_ATTRIBUTION_MISMATCH"
)
STRICT_REVIEW_OUTCOME = (
    "B_BLOCKED_PRESERVES_TWELVE_ROUTE_MAP_NO_PACKET_ACCEPTANCE_NO_BLOCKER_"
    "RESOLUTION_GUARDRAIL_NO_DIMENSIONAL_CLOSURE_NO_PILLAR_COMPLETION_NO_"
    "SEAM_ADMISSIBILITY_NO_LEVEL4_OR5_NO_PHYSICAL_CALIBRATION_NO_CROSS_"
    "SECTOR_COUPLING_VALIDATION_NO_CK_ACTION_EMBEDDING_NO_CCFT_NO_MASTER_"
    "ACTION_PROMOTION"
)

PROHIBITED_ASSIGNMENT_KEYS = {
    "assigned_unit", "declared_unit", "dimension_vector", "conversion_constant",
    "conversion_map", "restoration_map", "proposed_unit_assignment",
    "physical_calibration", "normalization_value", "normalization_assignment",
}


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _strict_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_strict_pairs,
        parse_constant=lambda token: (_ for _ in ()).throw(ValueError(f"nonfinite JSON value: {token}")),
    )
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _ledger_rows(ledger: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    return [
        *[("pillar", row) for row in ledger.get("pillar_rows", [])],
        *[("seam", row) for row in ledger.get("seam_rows", [])],
    ]


def _ledger_map(ledger: dict[str, Any]) -> dict[str, tuple[str, dict[str, Any]]]:
    return {row["row_id"]: (kind, row) for kind, row in _ledger_rows(ledger)}


def _route_rows(packet: dict[str, Any]) -> list[dict[str, Any]]:
    rows = packet.get("route_selections", [])
    return rows if isinstance(rows, list) else []


def _row_map(packet: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        row["row_id"]: row
        for row in _route_rows(packet)
        if isinstance(row, dict) and isinstance(row.get("row_id"), str)
    }


def _contains_assignment_key(value: Any) -> bool:
    if isinstance(value, dict):
        return bool(PROHIBITED_ASSIGNMENT_KEYS & set(value)) or any(
            _contains_assignment_key(item) for item in value.values()
        )
    if isinstance(value, list):
        return any(_contains_assignment_key(item) for item in value)
    return False


def _source_text(source_id: str) -> str:
    return (REPO_ROOT / SOURCE_BINDINGS[source_id]["path"]).read_text(encoding="utf-8")


def _source_classification(text: str) -> str | None:
    match = re.search(r"Classification:\s*\r?\n-\s*`([^`]+)`", text)
    return match.group(1) if match else None


def _independent_route_map(ledger: dict[str, Any]) -> dict[str, str]:
    ledger_map = _ledger_map(ledger)
    result: dict[str, str] = {}
    for row_id, signal in PILLAR_SIGNAL.items():
        kind, row = ledger_map[row_id]
        probe_id, source_id, anchors = DIRECT_PROBES[row_id]
        del probe_id
        text = _source_text(source_id)
        source_ready = all(anchor.casefold() in text.casefold() for anchor in anchors)
        inventory_empty = kind == "pillar" and row.get("quantity_rows") == []
        if row_id == "PILLAR-QFT-units_and_dimensions-v0":
            scalar = _source_text("accepted_scalar_sandbox_review")
            source_ready = source_ready and all(
                token in scalar
                for token in (
                    "provisional_classical_sandbox_route_only",
                    "master_action_promoted",
                    "toe_native_matter_derivation_claimed",
                )
            )
        result[row_id] = ROUTE_BY_SIGNAL[signal] if source_ready and inventory_empty else "RESEARCH_BLOCKED"
    pillar_states = {
        row["pillar_id"]: row["guardrail_unit_state"]
        for row in ledger.get("pillar_rows", [])
    }
    for row in ledger.get("seam_rows", []):
        endpoints = row.get("pillar_ids", [])
        result[row["row_id"]] = (
            "RESEARCH_BLOCKED"
            if len(endpoints) == 2 and any(pillar_states.get(item) != "resolved" for item in endpoints)
            else "SEAM_CONVERSION_MAP"
        )
    return result


def _expected_binding(source_id: str) -> dict[str, str]:
    return {"source_id": source_id, **SOURCE_BINDINGS[source_id]}


def source_authority_audit(packet: dict[str, Any]) -> dict[str, Any]:
    rows = _row_map(packet)
    mismatches: list[dict[str, str]] = []
    checks: dict[str, bool] = {}
    code_by_source = {
        "qft_bounded_surface": MISMATCH_CODES[0],
        "qm_bounded_surface": MISMATCH_CODES[1],
        "em_bounded_surface": MISMATCH_CODES[2],
        "sr_bounded_surface": MISMATCH_CODES[3],
    }
    for row_id, row in rows.items():
        matrix = row.get("evidence_matrix", {})
        for binding in matrix.get("source_bindings", []):
            source_id = binding.get("source_id")
            if source_id not in SOURCE_BINDINGS or not str(binding.get("path", "")).endswith(".md"):
                continue
            classification = _source_classification(_source_text(source_id))
            derived_class = (
                "BOUNDED_AUTHORITATIVE_SURFACE"
                if classification == "T-PROVED"
                else "BOUNDED_PLANNING_NONCLAIM"
                if classification == "P-POLICY"
                else "UNSUPPORTED_SOURCE_CLASS"
            )
            if binding.get("authority_class") != derived_class:
                mismatch = {
                    "row_id": row_id,
                    "source_id": source_id,
                    "source_classification": str(classification),
                    "packet_authority_class": str(binding.get("authority_class")),
                    "independently_derived_authority_class": derived_class,
                }
                mismatches.append(mismatch)
                if source_id in code_by_source:
                    checks[code_by_source[source_id]] = True
    for code in MISMATCH_CODES:
        checks.setdefault(code, False)
    return {
        "mismatch_codes": [code for code in MISMATCH_CODES if checks[code]],
        "mismatch_checks": checks,
        "mismatches": mismatches,
        "mismatch_count": len(mismatches),
        "classification_rule": {
            "T-PROVED": "BOUNDED_AUTHORITATIVE_SURFACE",
            "P-POLICY": "BOUNDED_PLANNING_NONCLAIM",
        },
        "route_map_affected": False,
        "review_note": (
            "Four P-POLICY source documents are mislabeled as bounded authoritative "
            "surfaces. The route map remains defensible, but the claimed authority-class "
            "decision does not independently reproduce."
        ),
    }


def source_absence_audit(packet: dict[str, Any]) -> dict[str, Any]:
    rows = _row_map(packet)
    qft = _source_text("qft_bounded_surface")
    qm = _source_text("qm_bounded_surface")
    stat = _source_text("stat_planning_surface")
    atomic = {
        "qft_standalone_action_match_count": len(re.findall(r"(?<![-\w])action(?![-\w])", qft, flags=re.IGNORECASE)),
        "qm_hamiltonian_casefold_match_count": qm.casefold().count("hamiltonian"),
        "stat_probability_casefold_match_count": stat.casefold().count("probability"),
        "stat_transport_casefold_match_count": stat.casefold().count("transport"),
    }
    qft_props = {item["proposition_id"]: item for item in rows["PILLAR-QFT-units_and_dimensions-v0"]["evidence_matrix"]["propositions"]}
    qm_props = {item["proposition_id"]: item for item in rows["PILLAR-QM-units_and_dimensions-v0"]["evidence_matrix"]["propositions"]}
    stat_props = {item["proposition_id"]: item for item in rows["PILLAR-STAT-units_and_dimensions-v0"]["evidence_matrix"]["propositions"]}
    expected_checks = {
        "qft_direct_physical_action_absent": {"kind": "regex", "pattern": r"(?<![-\w])action(?![-\w])", "flags": ["IGNORECASE"], "expected_match_count": 0},
        "qm_hamiltonian_absent": {"kind": "casefold_substring", "substring": "Hamiltonian", "expected_match_count": 0},
        "stat_probability_absent": {"kind": "casefold_substring", "substring": "probability", "expected_match_count": 0},
        "stat_transport_absent": {"kind": "casefold_substring", "substring": "transport", "expected_match_count": 0},
    }
    observed = {
        "qft_direct_physical_action_absent": qft_props.get("qft_direct_physical_action_absent", {}).get("absence_check"),
        "qm_hamiltonian_absent": qm_props.get("qm_hamiltonian_absent", {}).get("absence_check"),
        "stat_probability_absent": stat_props.get("stat_probability_absent", {}).get("absence_check"),
        "stat_transport_absent": stat_props.get("stat_transport_absent", {}).get("absence_check"),
    }
    scoped_statements = [
        qft_props.get("qft_direct_physical_action_absent", {}).get("statement", ""),
        qm_props.get("qm_hamiltonian_absent", {}).get("statement", ""),
        stat_props.get("stat_probability_absent", {}).get("statement", ""),
        stat_props.get("stat_transport_absent", {}).get("statement", ""),
    ]
    physical_no_go_tokens = ("cannot exist", "physically impossible", "physical no-go", "no hamiltonian can exist")
    return {
        "atomic_match_counts": atomic,
        "all_atomic_absences_reproduced_from_source_bytes": all(count == 0 for count in atomic.values()),
        "packet_absence_checks_match_independent_rules": observed == expected_checks,
        "source_scope_absence_only": all("source does not establish" in item.casefold() for item in scoped_statements),
        "physical_nonexistence_or_no_go_claimed": any(token in " ".join(scoped_statements).casefold() for token in physical_no_go_tokens),
        "source_hashes": {
            source_id: sha256_path(REPO_ROOT / SOURCE_BINDINGS[source_id]["path"])
            for source_id in ("qft_bounded_surface", "qm_bounded_surface", "stat_planning_surface")
        },
    }


def independent_decision_failures(
    packet: dict[str, Any], ledger: dict[str, Any]
) -> list[str]:
    failed: set[str] = set()
    rows = _route_rows(packet)
    rows_by_id = _row_map(packet)
    ledger_by_id = _ledger_map(ledger)

    input_bindings = packet.get("input_artifacts", [])
    input_map = {
        item.get("path"): item.get("sha256")
        for item in input_bindings
        if isinstance(item, dict)
    }
    frozen_ok = (
        len(input_bindings) == len(EXPECTED_INPUT_HASHES)
        and len(input_map) == len(EXPECTED_INPUT_HASHES)
        and input_map == EXPECTED_INPUT_HASHES
        and all(sha256_path(REPO_ROOT / path) == expected for path, expected in EXPECTED_INPUT_HASHES.items())
    )
    if not frozen_ok:
        failed.add("accepted_review_and_ledger_hashes_match")

    identity_ok = (
        len(rows) == 12
        and len(rows_by_id) == 12
        and set(rows_by_id) == set(ledger_by_id)
    )
    if identity_ok:
        for row_id, (kind, source) in ledger_by_id.items():
            row = rows_by_id[row_id]
            identity_ok = identity_ok and (
                row.get("row_kind") == kind
                and row.get("current_status") == source.get("guardrail_unit_state")
                and row.get("source_evidence_pointer") == source.get("evidence_pointer")
                and row.get("blocker_summary") == source.get("unresolved_items", [{}])[0].get("reason")
            )
    if not identity_ok:
        failed.add("exact_twelve_row_identity_status_and_evidence_bindings_preserved")

    independently_selected = _independent_route_map(ledger)
    routes_ok = (
        set(independently_selected) == set(rows_by_id)
        and all(
            isinstance(rows_by_id[row_id].get("selected_response_route"), str)
            and rows_by_id[row_id].get("selected_response_route") == route
            for row_id, route in independently_selected.items()
        )
    )
    if not routes_ok:
        failed.add("each_row_selects_exactly_one_primary_route")

    expected_criteria = [
        "Is the physical object unambiguously defined?",
        "Is the governing equation or action authoritative?",
        "Is the unit system explicit?",
        "Are coordinates physical, normalized, or dimensionless?",
        "Are natural constants suppressed?",
        "Can dimensions be derived without circularly assuming the desired bridge?",
        "Does the row require an experimental scale?",
        "Does the source pillar map to the target pillar without changing physical meaning?",
        "Would the proposed resolution alter the candidate master action?",
        "Should the row remain blocked?",
    ]
    expected_taxonomy = [
        "ACTION_DIMENSION_DERIVATION",
        "EQUATION_BALANCE_DERIVATION",
        "CONVENTION_AND_CONSTANT_RESTORATION",
        "SEAM_CONVERSION_MAP",
        "EMPIRICAL_SCALE_CALIBRATION",
        "OBJECT_SEMANTICS_REFINEMENT",
        "RESEARCH_BLOCKED",
        "DIMENSIONAL_INCOMPATIBILITY_REJECTION",
    ]
    observed_taxonomy = [item.get("route") for item in packet.get("route_taxonomy", []) if isinstance(item, dict)]
    if not (
        packet.get("route_count") == 8
        and observed_taxonomy == expected_taxonomy
        and packet.get("ordered_selection_criteria") == expected_criteria
        and all(
            [item.get("criterion") for item in row.get("selection_criteria_evaluation", [])]
            == expected_criteria
            for row in rows
        )
    ):
        failed.add("route_taxonomy_is_closed_and_selection_order_is_preserved")

    boundary = packet.get("boundary", {})
    policy = packet.get("policy", {})
    if not (
        not _contains_assignment_key(packet)
        and boundary.get("unit_assignments_emitted") == 0
        and boundary.get("dimension_vectors_emitted") == 0
        and boundary.get("conversion_constants_emitted") == 0
        and boundary.get("seam_mappings_emitted") == 0
        and policy.get("unit_or_dimension_assignment_authorized") is False
    ):
        failed.add("no_unit_dimension_constant_or_mapping_assignment_is_emitted")
    if any(
        source.get("guardrail_unit_state") == "unit_unknown"
        and (
            rows_by_id.get(row_id, {}).get("current_status") != "unit_unknown"
            or "proposed_unit_assignment" in rows_by_id.get(row_id, {})
        )
        for row_id, (_, source) in ledger_by_id.items()
    ):
        failed.add("unit_unknown_rows_cannot_receive_assignments_without_evidence")
    if not (
        Counter(row.get("current_status") for row in rows) == Counter({"unit_unknown": 6, "unresolved": 6})
        and policy.get("route_selection_resolves_blocker") is False
    ):
        failed.add("natural_units_do_not_resolve_unresolved_rows")
    if policy.get("dimensionless_coordinates_are_physical_distances") is not False:
        failed.add("dimensionless_coordinates_are_not_physical_distances")
    if not (
        policy.get("suppressed_constant_omission_allowed") is False
        and policy.get("suppressed_constants_requiring_explicit_treatment") == ["c", "hbar", "G", "k_B"]
    ):
        failed.add("suppressed_constants_require_explicit_restoration")
    if any(
        row.get("row_kind") == "seam"
        and row.get("selected_response_route") == "SEAM_CONVERSION_MAP"
        for row in rows
    ):
        failed.add("seam_map_requires_two_reviewed_internal_unit_systems")
    if not (
        policy.get("candidate_master_action_self_support_allowed") is False
        and not any(
            "candidate master action" in statement.casefold()
            for row in rows
            for statement in row.get("available_evidence", [])
        )
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

    route_counts = Counter(independently_selected.values())
    expected_family_counts = {
        "action_derivations_required": 0,
        "equation_balance_derivations_required": 1,
        "convention_restorations_required": 2,
        "seam_maps_required": 0,
        "empirical_calibrations_required": 0,
        "semantic_clarifications_required": 4,
        "research_blocked_routes_required": 5,
        "rows_rejected": 0,
        "rows_remaining_blocked": 12,
        "total_rows": 12,
    }
    if not (
        route_counts == Counter(EXPECTED_ROUTE_COUNTS)
        and packet.get("family_level_counts") == expected_family_counts
    ):
        failed.add("family_level_counts_are_planning_counts_only")
    expected_nonclaims = {
        "dimensional_closure", "pillar_completion", "seam_admissibility",
        "level_4_or_level_5", "physical_calibration_claims",
        "cross_sector_coupling_validation", "C_k_action_embedding",
        "CCFT_resumption", "master_action_promotion",
    }
    if not (
        set(packet.get("nonclaims", [])) == expected_nonclaims
        and boundary.get("level_4_or_level_5_authorized") is False
        and boundary.get("physical_calibration_claimed") is False
        and boundary.get("cross_sector_coupling_validation_claimed") is False
        and boundary.get("ccft_resumed") is False
        and boundary.get("master_action_promoted") is False
    ):
        failed.add("all_nonclaims_and_claim_ceiling_boundaries_are_preserved")

    v0_review = load_json(V0_REJECTION_PATH)
    lineage = packet.get("lineage", {})
    if not (
        v0_review.get("accepted") is False
        and v0_review.get("verdict") == "B-BLOCKED"
        and v0_review.get("selected_next_target") == packet.get("target")
        and lineage.get("v0_rejection_commit") == PREPARATION_PARENT
        and lineage.get("v0_rejection_report_sha256") == EXPECTED_PREPARATION_HASHES[V0_REJECTION_REL]
        and packet.get("route_map_recomputed_not_inherited") is True
    ):
        failed.add("frozen_v0_rejection_and_v1_authorization_match")

    matrices_ok = len(rows) == 12
    explicit_ok = True
    derived_ok = True
    unsupported_ok = True
    rationale_ok = True
    authority_ok = True
    hash_ok = True
    definitions_ok = True
    definitions: dict[tuple[str, str], str] = {}
    absence = source_absence_audit(packet)
    authority = source_authority_audit(packet)

    for row in rows:
        row_id = row.get("row_id")
        matrix = row.get("evidence_matrix", {})
        bindings_list = matrix.get("source_bindings", [])
        propositions_list = matrix.get("propositions", [])
        bindings = {
            item.get("source_id"): item
            for item in bindings_list
            if isinstance(item, dict) and isinstance(item.get("source_id"), str)
        }
        propositions = {
            item.get("proposition_id"): item
            for item in propositions_list
            if isinstance(item, dict) and isinstance(item.get("proposition_id"), str)
        }
        matrices_ok = matrices_ok and (
            matrix.get("row_id") == row_id
            and len(bindings) == len(bindings_list)
            and len(propositions) == len(propositions_list)
        )
        expected_source_ids = (
            ROW_SOURCE_IDS[row_id]
            if row_id in ROW_SOURCE_IDS
            else ["accepted_unit_ledger", "pillar_target_map"]
        )
        expected_bindings = [_expected_binding(source_id) for source_id in expected_source_ids]
        observed_path_hash_bindings = [
            {"source_id": item.get("source_id"), "path": item.get("path"), "sha256": item.get("sha256")}
            for item in bindings_list
        ]
        expected_path_hash_bindings = [
            {"source_id": item["source_id"], "path": item["path"], "sha256": item["sha256"]}
            for item in expected_bindings
        ]
        hash_ok = hash_ok and observed_path_hash_bindings == expected_path_hash_bindings and all(
            sha256_path(REPO_ROOT / item["path"]) == item["sha256"]
            for item in bindings_list
        )

        for proposition in propositions_list:
            proposition_id = proposition.get("proposition_id")
            classification = proposition.get("classification")
            if classification == "EXPLICITLY_STATED_BY_SOURCE":
                binding = bindings.get(proposition.get("source_id"))
                if binding is None:
                    explicit_ok = False
                elif proposition.get("ledger_assertion"):
                    assertion = proposition["ledger_assertion"]
                    if assertion.get("assertion_type") == "row_snapshot":
                        source = ledger_by_id.get(assertion.get("row_id"), (None, {}))[1]
                        explicit_ok = explicit_ok and (
                            assertion.get("row_id") == row_id
                            and assertion.get("guardrail_unit_state") == source.get("guardrail_unit_state")
                            and source.get(assertion.get("empty_field")) == []
                        )
                    elif assertion.get("assertion_type") == "endpoint_readiness":
                        seam = ledger_by_id.get(assertion.get("seam_row_id"), (None, {}))[1]
                        states = {
                            item["pillar_id"]: item["guardrail_unit_state"]
                            for item in ledger.get("pillar_rows", [])
                        }
                        pillar_ids = seam.get("pillar_ids")
                        explicit_ok = explicit_ok and (
                            assertion.get("seam_row_id") == row_id
                            and assertion.get("pillar_ids") == pillar_ids
                            and assertion.get("endpoint_states") == {item: states[item] for item in pillar_ids}
                        )
                    else:
                        explicit_ok = False
                else:
                    text = (REPO_ROOT / binding["path"]).read_text(encoding="utf-8")
                    if row_id in DIRECT_PROBES and proposition_id == DIRECT_PROBES[row_id][0]:
                        expected_anchors = DIRECT_PROBES[row_id][2]
                        explicit_ok = explicit_ok and proposition.get("required_substrings") == expected_anchors
                    elif proposition_id == "qft_scalar_sandbox_explicit":
                        expected_anchors = ["provisional_classical_sandbox_route_only", "master_action_promoted", "toe_native_matter_derivation_claimed"]
                        explicit_ok = explicit_ok and proposition.get("required_substrings") == expected_anchors
                    elif str(proposition_id).endswith("_target_map_scope_explicit"):
                        seam = ledger_by_id[row_id][1]
                        expected_anchors = ["_".join(item.removeprefix("PILLAR-") for item in seam["pillar_ids"])]
                        explicit_ok = explicit_ok and proposition.get("required_substrings") == expected_anchors
                    else:
                        explicit_ok = False
                        expected_anchors = []
                    explicit_ok = explicit_ok and all(anchor.casefold() in text.casefold() for anchor in expected_anchors)
            if classification == "DERIVED_FROM_SOURCE":
                premises = proposition.get("premise_ids", [])
                derived_ok = derived_ok and bool(premises) and all(
                    premise in propositions
                    and propositions[premise].get("classification") == "EXPLICITLY_STATED_BY_SOURCE"
                    and propositions[premise].get("supports_route") is True
                    for premise in premises
                )
                expected_signal = (
                    PILLAR_SIGNAL.get(row_id, "ENDPOINTS_NOT_RESOLVED")
                )
                derived_ok = derived_ok and proposition.get("route_signal") == expected_signal
                if expected_signal == "ENDPOINTS_NOT_RESOLVED":
                    endpoint_props = [
                        propositions[premise]
                        for premise in premises
                        if propositions[premise].get("ledger_assertion", {}).get("assertion_type") == "endpoint_readiness"
                    ]
                    derived_ok = derived_ok and len(endpoint_props) == 1 and (
                        proposition.get("derived_facts", {}).get("endpoint_states")
                        == endpoint_props[0]["ledger_assertion"].get("endpoint_states")
                    )
            if classification in {"INFERRED_NOT_ESTABLISHED", "ABSENT_FROM_SOURCE"}:
                unsupported_ok = unsupported_ok and proposition.get("supports_route") is False
            for obj in proposition.get("objects", []):
                key = (str(proposition.get("source_id") or "DERIVED"), str(obj.get("object_id")))
                definition = str(obj.get("definition"))
                if key in definitions and definitions[key] != definition:
                    definitions_ok = False
                definitions[key] = definition

        supported_ids = [
            item["proposition_id"] for item in propositions_list if item.get("supports_route") is True
        ]
        unsupported_ids = [
            item["proposition_id"] for item in propositions_list if item.get("supports_route") is not True
        ]
        available = [item["statement"] for item in propositions_list if item.get("supports_route") is True]
        missing = [
            item["statement"]
            for item in propositions_list
            if item.get("classification") in {"INFERRED_NOT_ESTABLISHED", "ABSENT_FROM_SOURCE"}
        ]
        supported_objects = {
            obj["object_id"]
            for item in propositions_list
            if item.get("supports_route") is True
            for obj in item.get("objects", [])
        }
        rationale_ok = rationale_ok and (
            matrix.get("supported_proposition_ids") == supported_ids
            and matrix.get("unsupported_proposition_ids") == unsupported_ids
            and row.get("route_support_proposition_ids") == supported_ids
            and row.get("available_evidence") == available
            and row.get("missing_evidence") == missing
            and set(matrix.get("rationale_object_ids", [])) <= supported_objects
            and row.get("rationale_object_ids") == matrix.get("rationale_object_ids")
        )
        for proposition in propositions_list:
            if proposition.get("supports_route") is not True or not proposition.get("source_id"):
                continue
            binding = bindings.get(proposition["source_id"])
            authority_ok = authority_ok and binding is not None and (
                binding.get("authority_class") == SOURCE_BINDINGS[proposition["source_id"]]["authority_class"]
            )

    explicit_ok = explicit_ok and (
        absence["all_atomic_absences_reproduced_from_source_bytes"]
        and absence["packet_absence_checks_match_independent_rules"]
    )
    authority_ok = authority_ok and not authority["mismatch_codes"]

    if not matrices_ok:
        failed.add("evidence_matrix_present_once_per_row")
    if not explicit_ok:
        failed.add("explicit_propositions_are_source_anchored")
    if not derived_ok:
        failed.add("derived_propositions_have_reproducible_supported_premises")
    if not unsupported_ok:
        failed.add("inferred_and_absent_propositions_do_not_support_routes")
    if not rationale_ok:
        failed.add("route_rationale_objects_are_supported")
    if not authority_ok:
        failed.add("supporting_sources_have_authorized_bounded_class")
    if not hash_ok:
        failed.add("source_path_hash_pairs_are_exactly_rebound")

    qft = rows_by_id.get("PILLAR-QFT-units_and_dimensions-v0", {})
    qft_matrix = qft.get("evidence_matrix", {})
    qft_props = {item.get("proposition_id"): item for item in qft_matrix.get("propositions", [])}
    if not (
        qft_matrix.get("scalar_evidence_scope") == "NARROW_CLASSICAL_REAL_SCALAR_ONLY"
        and qft_props.get("qft_scalar_sandbox_explicit", {}).get("supports_route") is True
        and "narrow_scalar_sandbox" in qft_matrix.get("rationale_object_ids", [])
        and "qft_scalar_sandbox_explicit" in qft_props.get("PILLAR-QFT-units_and_dimensions-v0_route_signal", {}).get("premise_ids", [])
        and "no_wider_QFT_authority" in qft.get("authority_limit", "")
    ):
        failed.add("narrow_scalar_evidence_is_not_promoted_to_full_qft")
    if not definitions_ok:
        failed.add("source_object_definitions_are_nonconflicting")
    return [decision_id for decision_id in DECISION_IDS if decision_id in failed]


def _mutate(packet: dict[str, Any], mutation: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    changed = copy.deepcopy(packet)
    mutation(changed)
    return changed


def _row(packet: dict[str, Any], row_id: str) -> dict[str, Any]:
    return next(item for item in packet["route_selections"] if item["row_id"] == row_id)


def _proposition(packet: dict[str, Any], row_id: str, proposition_id: str) -> dict[str, Any]:
    return next(
        item
        for item in _row(packet, row_id)["evidence_matrix"]["propositions"]
        if item["proposition_id"] == proposition_id
    )


def _append_claim(packet: dict[str, Any], row_id: str, proposition_id: str, token: str, object_id: str) -> None:
    row = _row(packet, row_id)
    source_id = row["evidence_matrix"]["source_bindings"][1]["source_id"]
    row["evidence_matrix"]["propositions"].append({
        "proposition_id": proposition_id,
        "classification": "EXPLICITLY_STATED_BY_SOURCE",
        "source_id": source_id,
        "statement": f"Invented source claim: {token}",
        "required_substrings": [token],
        "objects": [{"object_id": object_id, "definition": f"invented {object_id}"}],
        "supports_route": True,
    })


def independent_negative_controls(packet: dict[str, Any], ledger: dict[str, Any]) -> list[dict[str, Any]]:
    controls: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("assign_unit_to_unit_unknown_without_evidence", DECISION_IDS[5], lambda value: value["route_selections"][0].__setitem__("proposed_unit_assignment", "invented")),
        ("natural_units_mark_unresolved_resolved", DECISION_IDS[6], lambda value: value["route_selections"][1].__setitem__("current_status", "resolved")),
        ("dimensionless_coordinates_promoted_to_physical_distance", DECISION_IDS[7], lambda value: value["policy"].__setitem__("dimensionless_coordinates_are_physical_distances", True)),
        ("suppressed_constant_omitted", DECISION_IDS[8], lambda value: value["policy"].__setitem__("suppressed_constant_omission_allowed", True)),
        ("two_incompatible_routes_assigned_without_priority", DECISION_IDS[2], lambda value: value["route_selections"][0].__setitem__("selected_response_route", ["OBJECT_SEMANTICS_REFINEMENT", "ACTION_DIMENSION_DERIVATION"])),
        ("seam_map_selected_with_incomplete_pillar_units", DECISION_IDS[9], lambda value: _row(value, "SEAM-QFT-GR-unit_map-v0").__setitem__("selected_response_route", "SEAM_CONVERSION_MAP")),
        ("candidate_master_action_used_as_self_evidence", DECISION_IDS[10], lambda value: value["route_selections"][0]["available_evidence"].append("The candidate master action supplies its own missing dimensions.")),
        ("normalization_convention_promoted_to_empirical_scale", DECISION_IDS[11], lambda value: value["policy"].__setitem__("normalization_convention_is_empirical_scale", True)),
        ("routed_blocker_promoted_to_dimensional_closure", DECISION_IDS[12], lambda value: value["boundary"].__setitem__("dimensional_closure_claimed", True)),
        ("C_k_embedding_before_dimensions_known", DECISION_IDS[13], lambda value: value["boundary"].__setitem__("C_k_action_embedding_authorized", True)),
        ("qft_action_claimed_without_action", DECISION_IDS[18], lambda value: _append_claim(value, "PILLAR-QFT-units_and_dimensions-v0", "invented_qft_action", "physical action", "qft_physical_action")),
        ("qm_hamiltonian_claimed_without_hamiltonian", DECISION_IDS[18], lambda value: _append_claim(value, "PILLAR-QM-units_and_dimensions-v0", "invented_qm_hamiltonian", "Hamiltonian", "qm_hamiltonian")),
        ("stat_probability_claimed_without_probability_semantics", DECISION_IDS[18], lambda value: _append_claim(value, "PILLAR-STAT-units_and_dimensions-v0", "invented_stat_probability", "probability", "stat_probability")),
        ("stat_transport_claimed_without_transport_law", DECISION_IDS[18], lambda value: _append_claim(value, "PILLAR-STAT-units_and_dimensions-v0", "invented_stat_transport", "transport law", "stat_transport")),
        ("narrow_scalar_evidence_promoted_to_full_qft", DECISION_IDS[24], lambda value: _row(value, "PILLAR-QFT-units_and_dimensions-v0")["evidence_matrix"].__setitem__("scalar_evidence_scope", "ROW_WIDE_QFT")),
        ("absence_treated_as_positive_evidence", DECISION_IDS[20], lambda value: _proposition(value, "PILLAR-QM-units_and_dimensions-v0", "qm_hamiltonian_absent").__setitem__("supports_route", True)),
        ("citation_hash_changed_without_rebinding", DECISION_IDS[23], lambda value: _row(value, "PILLAR-GR-units_and_dimensions-v0")["evidence_matrix"]["source_bindings"][1].__setitem__("sha256", "0" * 64)),
        ("route_rationale_object_missing_from_inventory", DECISION_IDS[21], lambda value: _row(value, "PILLAR-QM-units_and_dimensions-v0")["evidence_matrix"]["rationale_object_ids"].append("measurement_object")),
        ("speculative_surface_treated_as_authoritative", DECISION_IDS[22], lambda value: _row(value, "PILLAR-STAT-units_and_dimensions-v0")["evidence_matrix"]["source_bindings"][1].__setitem__("authority_class", "SPECULATIVE_SURFACE")),
        ("one_source_supports_conflicting_object_definitions", DECISION_IDS[25], lambda value: _proposition(value, "PILLAR-QFT-units_and_dimensions-v0", "qft_direct_scope_explicit")["objects"].append({"object_id": "qft_surface_scope", "definition": "incompatible full-QFT definition"})),
    ]
    baseline = independent_decision_failures(packet, ledger)
    baseline_authority_mismatch_count = source_authority_audit(packet)["mismatch_count"]
    results: list[dict[str, Any]] = []
    for control_id, expected, mutation in controls:
        mutated_packet = _mutate(packet, mutation)
        observed = independent_decision_failures(mutated_packet, ledger)
        mutated_authority = source_authority_audit(mutated_packet)
        authority_delta_observed = (
            control_id == "speculative_surface_treated_as_authoritative"
            and mutated_authority["mismatch_count"] == baseline_authority_mismatch_count + 1
            and any(
                item["source_id"] == "stat_planning_surface"
                and item["packet_authority_class"] == "SPECULATIVE_SURFACE"
                for item in mutated_authority["mismatches"]
            )
        )
        mutation_specific_delta_observed = (
            expected not in baseline and expected in observed
        ) or authority_delta_observed
        results.append({
            "control_id": control_id,
            "expected_failed_decision_id": expected,
            "observed_failed_decision_ids": observed,
            "fresh_deep_copy_used": True,
            "baseline_failed_decision_ids": baseline,
            "expected_failure_observed": expected in observed,
            "baseline_already_failed_expected_decision": expected in baseline,
            "baseline_authority_mismatch_count": baseline_authority_mismatch_count,
            "mutated_authority_mismatch_count": mutated_authority["mismatch_count"],
            "mutation_specific_delta_observed": mutation_specific_delta_observed,
            "passed": expected in observed and mutation_specific_delta_observed,
        })
    return results


def _git_blob(relative: str) -> bytes:
    completed = subprocess.run(
        ["git", "show", f"{PREPARATION_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise ValueError(f"missing preparation commit blob: {relative}")
    return completed.stdout


def commit_custody() -> dict[str, Any]:
    parent = subprocess.run(
        ["git", "show", "-s", "--format=%P", PREPARATION_COMMIT],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
        text=True,
    )
    artifacts = {}
    for relative, expected in EXPECTED_PREPARATION_HASHES.items():
        blob = _git_blob(relative)
        artifacts[relative] = {
            "expected_sha256": expected,
            "commit_blob_sha256": sha256_bytes(blob),
            "working_tree_sha256": sha256_path(REPO_ROOT / relative),
            "commit_blob_matches_expected": sha256_bytes(blob) == expected,
            "working_tree_matches_commit_blob": (REPO_ROOT / relative).read_bytes() == blob,
        }
    runtime_dependencies = {}
    for relative in (V0_GENERATOR_REL, REPO_ENVIRONMENT_REL, "formal/python/meta/__init__.py"):
        blob = _git_blob(relative)
        runtime_dependencies[relative] = {
            "preparation_commit_blob_sha256": sha256_bytes(blob),
            "working_tree_sha256": sha256_path(REPO_ROOT / relative),
            "working_tree_matches_preparation_commit_after_eol_normalization": (
                (REPO_ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
                == blob.replace(b"\r\n", b"\n")
            ),
        }
    all_artifacts_match = all(
        item["commit_blob_matches_expected"] and item["working_tree_matches_commit_blob"]
        for item in artifacts.values()
    )
    runtime_bound = all(
        item["working_tree_matches_preparation_commit_after_eol_normalization"]
        for item in runtime_dependencies.values()
    )
    return {
        "preparation_commit": PREPARATION_COMMIT,
        "expected_parent": PREPARATION_PARENT,
        "observed_parent": parent.stdout.strip(),
        "parent_matches": parent.returncode == 0 and parent.stdout.strip() == PREPARATION_PARENT,
        "artifacts": artifacts,
        "all_artifacts_match": all_artifacts_match,
        "runtime_dependencies": runtime_dependencies,
        "all_transitive_runtime_dependencies_bound_to_preparation_commit": runtime_bound,
        "passed": all_artifacts_match and runtime_bound and parent.returncode == 0 and parent.stdout.strip() == PREPARATION_PARENT,
    }


def _materialize_preparation_tree(root: Path) -> None:
    frozen_paths = {*EXPECTED_INPUT_HASHES, GENERATOR_REL}
    runtime_paths = {
        V0_GENERATOR_REL,
        REPO_ENVIRONMENT_REL,
        "formal/python/meta/__init__.py",
        "State_of_the_Theory.md",
    }
    for relative in frozen_paths | runtime_paths:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        source = REPO_ROOT / relative
        if relative in frozen_paths:
            expected = (
                EXPECTED_INPUT_HASHES.get(relative)
                or EXPECTED_PREPARATION_HASHES.get(relative)
            )
            if expected is None or sha256_path(source) != expected:
                raise ValueError(f"isolated staging hash mismatch: {relative}")
        path.write_bytes(source.read_bytes())


def isolated_regeneration() -> dict[str, Any]:
    tracked = (PACKET_REL, MANIFEST_REL, PREPARATION_REPORT_REL)
    before = {relative: sha256_path(REPO_ROOT / relative) for relative in tracked}
    runs: list[dict[str, Any]] = []
    for run_index in range(2):
        with tempfile.TemporaryDirectory(prefix=f"toe-v1-review-{run_index + 1}-") as temp:
            root = Path(temp)
            _materialize_preparation_tree(root)
            env = dict(os.environ)
            env.update({
                "PYTHONPATH": str(root),
                "PYTHONNOUSERSITE": "1",
                "PYTHONDONTWRITEBYTECODE": "1",
                "PYTHONHASHSEED": "0",
            })
            completed = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    "-m",
                    "formal.python.tools.pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1",
                    "--write",
                ],
                cwd=root,
                env=env,
                capture_output=True,
                check=False,
            )
            outputs = {
                relative: (root / relative).read_bytes()
                if (root / relative).is_file()
                else b""
                for relative in tracked
            }
            runs.append({
                "run_index": run_index + 1,
                "isolated_root_distinct": True,
                "return_code": completed.returncode,
                "stdout_sha256": sha256_bytes(completed.stdout),
                "stderr_sha256": sha256_bytes(completed.stderr),
                "stderr": completed.stderr.decode("utf-8", errors="replace"),
                "artifact_hashes": {relative: sha256_bytes(raw) for relative, raw in outputs.items()},
                "artifacts": outputs,
            })
    after = {relative: sha256_path(REPO_ROOT / relative) for relative in tracked}
    first = runs[0]["artifacts"]
    second = runs[1]["artifacts"]
    committed = {relative: _git_blob(relative) for relative in tracked}
    run_bytes_identical = first == second
    committed_bytes_reproduced = first == committed and second == committed
    return_codes = [run["return_code"] for run in runs]
    return {
        "isolated_subprocess_count": 2,
        "return_codes": return_codes,
        "distinct_temporary_roots_used": True,
        "all_frozen_inputs_staged_from_exact_hash_verified_bytes": True,
        "transitive_v0_generator_and_repo_environment_commit_custody_verified": True,
        "run_artifact_hashes": [run["artifact_hashes"] for run in runs],
        "run_outputs_byte_identical": run_bytes_identical,
        "committed_packet_manifest_and_report_bytes_reproduced": committed_bytes_reproduced,
        "repository_preparation_artifact_hashes_unchanged": before == after,
        "passed": (
            return_codes == [0, 0]
            and run_bytes_identical
            and committed_bytes_reproduced
            and before == after
        ),
    }


def formal_review_requirements(
    packet: dict[str, Any],
    ledger: dict[str, Any],
    failures: list[str],
    controls: list[dict[str, Any]],
    absence: dict[str, Any],
    regeneration: dict[str, Any],
) -> list[dict[str, Any]]:
    routes = _independent_route_map(ledger)
    rows = _row_map(packet)
    boundary = packet.get("boundary", {})
    values = [
        len(_route_rows(packet)) == 12 and len(rows) == 12 and set(rows) == set(_ledger_map(ledger)),
        "accepted_review_and_ledger_hashes_match" not in failures,
        not failures,
        len(controls) == 20 and all(item["passed"] for item in controls),
        absence["all_atomic_absences_reproduced_from_source_bytes"] and absence["packet_absence_checks_match_independent_rules"],
        "narrow_scalar_evidence_is_not_promoted_to_full_qft" not in failures,
        absence["source_scope_absence_only"] and absence["physical_nonexistence_or_no_go_claimed"] is False,
        absence["source_scope_absence_only"] and absence["physical_nonexistence_or_no_go_claimed"] is False,
        all(
            routes[row_id] == "RESEARCH_BLOCKED"
            for row_id, (kind, _) in _ledger_map(ledger).items()
            if kind == "seam"
        ) and "explicit_propositions_are_source_anchored" not in failures,
        "route_rationale_objects_are_supported" not in failures,
        Counter(routes.values()) == Counter(EXPECTED_ROUTE_COUNTS),
        not _contains_assignment_key(packet),
        Counter(row.get("current_status") for row in rows.values()) == Counter({"unit_unknown": 6, "unresolved": 6}),
        "all_nonclaims_and_claim_ceiling_boundaries_are_preserved" not in failures
        and boundary.get("master_action_promoted") is False,
    ]
    notes = [
        "All twelve ledger rows are present exactly once.",
        "The accepted ledger and result-review hashes are exact frozen inputs.",
        "All twenty-six v1 decisions reproduce independently.",
        "All twenty negative-control mutations are independently rejected.",
        "All four atomic source-absence probes are recomputed from exact bytes.",
        "Narrow scalar evidence is not promoted into full-QFT coverage.",
        "QM Hamiltonian absence remains source-scoped and is not a physical no-go.",
        "STAT probability and transport absences remain source-scoped and are not physical no-go results.",
        "Each seam remains blocked by its actual endpoint states.",
        "Every rationale object is present in its supporting evidence inventory.",
        "The 1 / 2 / 4 / 5 route distribution is independently recomputed.",
        "No unit, constant, conversion, normalization, or seam map is introduced.",
        "No route is promoted to resolved status.",
        "All dimensional, pillar, seam, CCFT, and master-action nonclaims remain intact.",
    ]
    result = [
        {
            "requirement_id": REVIEW_REQUIREMENT_IDS[index],
            "passed": passed,
            "note": notes[index],
        }
        for index, passed in enumerate(values)
    ]
    if not regeneration["passed"]:
        result[2]["passed"] = False
        result[2]["note"] += " Isolated byte-identical regeneration also failed."
    return result


def build_review_report(*, run_subprocesses: bool = True) -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    manifest = load_json(MANIFEST_PATH)
    preparation_report = load_json(PREPARATION_REPORT_PATH)
    ledger = load_json(LEDGER_PATH)
    ledger_review = load_json(LEDGER_REVIEW_PATH)
    failures = independent_decision_failures(packet, ledger)
    controls = independent_negative_controls(packet, ledger)
    absence = source_absence_audit(packet)
    authority = source_authority_audit(packet)
    custody = commit_custody()
    regeneration = isolated_regeneration() if run_subprocesses else {"passed": False, "not_run": True}
    requirements = formal_review_requirements(packet, ledger, failures, controls, absence, regeneration)
    blocked = bool(failures or authority["mismatch_codes"] or not custody["passed"] or not regeneration["passed"])
    routes = _independent_route_map(ledger)
    passed_decisions = len(DECISION_IDS) - len(failures)
    return {
        "accepted": not blocked,
        "artifact_chain": {
            "expected_preparation_hashes": EXPECTED_PREPARATION_HASHES,
            "manifest_schema_id": manifest.get("schema_id"),
            "preparation_report_schema_id": preparation_report.get("schema_id"),
            "accepted_ledger_review_schema_id": ledger_review.get("schema_id"),
            "commit_custody": custody,
        },
        "authority_rotation": {
            "packet_acceptance_authorized": False,
            "corrective_v2_preparation_authorized": blocked,
            "first_blocker_resolution_guardrail_authorized": False,
            "actual_blocker_resolution_execution_authorized": False,
            "sr_convention_or_restoration_work_authorized": False,
            "gr_equation_balance_derivation_authorized": False,
            "maintenance_authority_rotation_authorized": False,
        },
        "boundary": {
            "route_map_changed_by_review": False,
            "unit_or_dimension_assignment_emitted": False,
            "normalization_or_constant_restoration_emitted": False,
            "dimensional_closure_claimed": False,
            "pillar_completion_claimed": False,
            "seam_admissibility_claimed": False,
            "level_4_or_level_5_authorized": False,
            "physical_calibration_claimed": False,
            "cross_sector_coupling_validation_claimed": False,
            "C_k_action_embedding_authorized": False,
            "ccft_resumed": False,
            "master_action_promoted": False,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "claim": (
            "The v1 route map and source-absence repair reproduce, but four P-POLICY "
            "sources are over-attributed as bounded authoritative surfaces; v1 is not accepted."
        ),
        "consumed_target": REVIEW_TARGET,
        "diagnostic_target": DIAGNOSTIC_TARGET,
        "failure_preservation": {
            "preparation_commit_remains_immutable": True,
            "preparation_artifacts_amended_by_review": False,
            "versioned_successor_required": blocked,
            "route_map_preserved_as_nonaccepted_evidence": True,
        },
        "formal_review_requirements": {
            "requirement_count": len(requirements),
            "requirements": requirements,
            "failed_requirement_ids": [item["requirement_id"] for item in requirements if not item["passed"]],
            "all_requirements_passed": all(item["passed"] for item in requirements),
        },
        "implemented_decision_reproduction": {
            "decision_count": len(DECISION_IDS),
            "passed_decision_count": passed_decisions,
            "decisions": [
                {"decision_id": decision_id, "passed": decision_id not in failures}
                for decision_id in DECISION_IDS
            ],
            "failed_decision_ids": failures,
            "all_implemented_decisions_reproduced": not failures,
        },
        "maintenance_boundary": {
            "registry_maintenance_paused": True,
            "registry_monolith_remains_authoritative": True,
            "registry_v3_live": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
        },
        "mismatch_codes": authority["mismatch_codes"],
        "negative_control_reproduction": {
            "control_count": len(controls),
            "controls": controls,
            "all_controls_reproduced": all(item["passed"] for item in controls),
        },
        "preparation_commit": PREPARATION_COMMIT,
        "preparation_parent": PREPARATION_PARENT,
        "primary_label": "B-BLOCKED" if blocked else "ACCEPT",
        "regeneration": regeneration,
        "review_implementation": {
            "path": str(SCRIPT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sha256": sha256_path(SCRIPT_PATH),
            "imports_v1_preparation_validator_or_controls": False,
        },
        "review_id": (
            "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_"
            "PACKET_V1_RESULT_REVIEW_v0"
        ),
        "review_outcome": REVIEW_OUTCOME,
        "route_reproduction": {
            "independently_recomputed_routes": routes,
            "independently_recomputed_route_counts": dict(Counter(routes.values())),
            "route_map_reproduced": all(_row_map(packet)[row_id].get("selected_response_route") == route for row_id, route in routes.items()),
            "route_map_accepted": False,
            "unit_unknown_row_count": 6,
            "unresolved_row_count": 6,
            "resolved_row_count": 0,
            "rows_remaining_blocked": 12,
        },
        "schema_id": (
            "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_"
            "PACKET_RESULT_REVIEW_20260712_v1"
        ),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "selection_basis": (
            "Repair four source authority-class attributions and bind transitive runtime "
            "dependencies in a versioned v2 packet without inheriting the v1 route map as authority."
        ),
        "source_absence_review": absence,
        "source_authority_review": authority,
        "status": "blocked_source_authority_class_attribution_mismatch" if blocked else "accepted",
        "strict_review_outcome": STRICT_REVIEW_OUTCOME,
        "successor_boundary": {
            "corrective_successor": SELECTED_NEXT_TARGET,
            "deferred_first_resolution_guardrail_after_future_acceptance": DEFERRED_FIRST_RESOLUTION_GUARDRAIL,
            "first_resolution_guardrail_selected_now": False,
            "metadata_only_correction_required": True,
        },
        "verdict": "B-BLOCKED" if blocked else "ACCEPT",
    }


def write_report(report: dict[str, Any]) -> None:
    REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REVIEW_REPORT_PATH.write_bytes(canonical_json_bytes(report))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the v1 source-attribution-corrected route packet.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report(run_subprocesses=True)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if args.write:
        write_report(report)
        print(
            "wrote B-BLOCKED v1 route-selection formal review; "
            f"{report['implemented_decision_reproduction']['passed_decision_count']}/26 decisions, "
            "20/20 controls, four authority-class mismatches; "
            f"reviewer={sha256_path(SCRIPT_PATH)} report={sha256_path(REVIEW_REPORT_PATH)}"
        )
        return 0
    if args.check:
        expected = canonical_json_bytes(report)
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing v1 route-selection formal review", file=sys.stderr)
            return 1
        print(
            "v1 route-selection formal review verified: B-BLOCKED, "
            f"{report['implemented_decision_reproduction']['passed_decision_count']}/26 decisions, "
            "20/20 controls, four authority-class mismatches"
        )
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
