from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection as v0,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/"
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1.py"
)
PACKET_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-PACKET-v1.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-MANIFEST-v1.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260712_v1.json"
)
V0_PACKET_RELATIVE_PATH = v0.PACKET_RELATIVE_PATH
V0_MANIFEST_RELATIVE_PATH = v0.MANIFEST_RELATIVE_PATH
V0_REPORT_RELATIVE_PATH = v0.REPORT_RELATIVE_PATH
V0_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260712_v0.json"
)
V0_REVIEW_TOOL_RELATIVE_PATH = (
    "formal/python/tools/pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_result_review.py"
)

PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

V0_PACKET_SHA256 = "e3aad41e3ed886f43bcd6dfafc0b3736c5f981a49278a6bd89460ffdf89875b9"
V0_MANIFEST_SHA256 = "23015cfac12edd4d627d8db5af0613f10bc6924f8ea1ce422e0bf3e384457c88"
V0_REPORT_SHA256 = "56e55ff41d015a2337edeecd25da8397eff54289f8e05271fa0a309df4342444"
V0_REVIEW_SHA256 = "8e977f23dca29b78ba54daeb60d53a282fa75dd45f3ba34ddaa32c7258280162"
V0_REVIEW_TOOL_SHA256 = "da7766b4e51a3b11b6d823aa6833ba3f90b0b79e36b9c56786054197478e0f80"
V0_PREPARATION_COMMIT = "5d11196086e12f161f51785fb86dc88bbd803081"
V0_REVIEW_COMMIT = "145c30255ff90ca2df97f8526a98c6923e5db2bf"

CAPTURED_AT_UTC = "2026-07-12T00:00:00Z"
TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v1"
)
FAILURE_TARGET = (
    "diagnose_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v1_mismatch"
)
SUCCESSOR_TARGET = (
    "review_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v1_result"
)
SUCCESSOR_TARGET_KIND = (
    "pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v1_result_review"
)
PACKET_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_v1"
)
MANIFEST_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_MANIFEST_v1"
)
REPORT_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260712_v1"
)
STATUS = (
    "prepared_twelve_row_source_attribution_corrected_route_selection_"
    "v1_only_resolution_not_performed"
)
PACKET_RESULT = (
    "TWELVE_UNIT_BLOCKERS_RECOMPUTED_AND_ROUTED_ONCE_FROM_EXACT_SOURCE_"
    "ATTRIBUTION_WITHOUT_UNIT_ASSIGNMENT_OR_DIMENSIONAL_RESOLUTION_"
    "PENDING_INDEPENDENT_REVIEW"
)
STRICT_PACKET_RESULT = (
    "SOURCE_ATTRIBUTION_CORRECTION_AND_ROUTE_SELECTION_ONLY_NO_DIMENSIONAL_"
    "CLOSURE_NO_PILLAR_COMPLETION_NO_SEAM_ADMISSIBILITY_NO_LEVEL4_OR5_NO_"
    "PHYSICAL_CALIBRATION_NO_CROSS_SECTOR_COUPLING_VALIDATION_NO_CK_ACTION_"
    "EMBEDDING_NO_CCFT_NO_MASTER_ACTION_PROMOTION"
)
CORRECTED_MISMATCH_CODES = [
    "QFT_BOUND_SOURCE_ACTION_ATTRIBUTION_MISMATCH",
    "QM_BOUND_SOURCE_HAMILTONIAN_ATTRIBUTION_MISMATCH",
    "STAT_BOUND_SOURCE_PROBABILITY_TRANSPORT_ATTRIBUTION_MISMATCH",
]
CLASSIFICATIONS = (
    "EXPLICITLY_STATED_BY_SOURCE",
    "DERIVED_FROM_SOURCE",
    "INFERRED_NOT_ESTABLISHED",
    "ABSENT_FROM_SOURCE",
)
SUPPORTING_CLASSIFICATIONS = set(CLASSIFICATIONS[:2])
SUPPORTING_AUTHORITY_CLASSES = {
    "FROZEN_ACCEPTED_LEDGER",
    "ACCEPTED_BOUNDED_REVIEW",
    "BOUNDED_AUTHORITATIVE_SURFACE",
    "BOUNDED_PLANNING_NONCLAIM",
}


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _binding(source_id: str, path: str, sha256: str, authority_class: str) -> dict[str, str]:
    return {
        "source_id": source_id,
        "path": path,
        "sha256": sha256,
        "authority_class": authority_class,
    }


SOURCES = {
    "ledger": _binding(
        "accepted_unit_ledger",
        v0.LEDGER_RELATIVE_PATH,
        v0.LEDGER_SHA256,
        "FROZEN_ACCEPTED_LEDGER",
    ),
    "qft": _binding("qft_bounded_surface", v0.ROUTE_EVIDENCE_ARTIFACTS[0]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[0]["sha256"], "BOUNDED_AUTHORITATIVE_SURFACE"),
    "gr": _binding("gr_bounded_surface", v0.ROUTE_EVIDENCE_ARTIFACTS[1]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[1]["sha256"], "BOUNDED_AUTHORITATIVE_SURFACE"),
    "qm": _binding("qm_bounded_surface", v0.ROUTE_EVIDENCE_ARTIFACTS[2]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[2]["sha256"], "BOUNDED_AUTHORITATIVE_SURFACE"),
    "stat": _binding("stat_planning_surface", v0.ROUTE_EVIDENCE_ARTIFACTS[3]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[3]["sha256"], "BOUNDED_PLANNING_NONCLAIM"),
    "em": _binding("em_bounded_surface", v0.ROUTE_EVIDENCE_ARTIFACTS[4]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[4]["sha256"], "BOUNDED_AUTHORITATIVE_SURFACE"),
    "sr": _binding("sr_bounded_surface", v0.ROUTE_EVIDENCE_ARTIFACTS[5]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[5]["sha256"], "BOUNDED_AUTHORITATIVE_SURFACE"),
    "cosmo": _binding("cosmo_planning_surface", v0.ROUTE_EVIDENCE_ARTIFACTS[6]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[6]["sha256"], "BOUNDED_PLANNING_NONCLAIM"),
    "target_map": _binding("pillar_target_map", v0.ROUTE_EVIDENCE_ARTIFACTS[7]["path"], v0.ROUTE_EVIDENCE_ARTIFACTS[7]["sha256"], "BOUNDED_PLANNING_NONCLAIM"),
    "scalar_review": _binding("accepted_scalar_sandbox_review", v0.IMPORTED_SCALAR_ACTION_REVIEW_RELATIVE_PATH, v0.IMPORTED_SCALAR_ACTION_REVIEW_SHA256, "ACCEPTED_BOUNDED_REVIEW"),
}


def _obj(object_id: str, definition: str) -> dict[str, str]:
    return {"object_id": object_id, "definition": definition}


def _explicit(
    proposition_id: str,
    source_key: str,
    statement: str,
    anchors: list[str],
    objects: list[dict[str, str]],
    *,
    supports_route: bool = True,
) -> dict[str, Any]:
    return {
        "proposition_id": proposition_id,
        "classification": "EXPLICITLY_STATED_BY_SOURCE",
        "source_id": SOURCES[source_key]["source_id"],
        "statement": statement,
        "required_substrings": anchors,
        "objects": objects,
        "supports_route": supports_route,
    }


def _unsupported(
    proposition_id: str,
    classification: str,
    statement: str,
    objects: list[dict[str, str]],
    *,
    source_key: str | None = None,
    absence_check: dict[str, Any] | None = None,
) -> dict[str, Any]:
    proposition = {
        "proposition_id": proposition_id,
        "classification": classification,
        "source_id": SOURCES[source_key]["source_id"] if source_key else None,
        "statement": statement,
        "required_substrings": [],
        "objects": objects,
        "supports_route": False,
    }
    if absence_check is not None:
        proposition["absence_check"] = absence_check
    return proposition


PILLAR_SPECS: dict[str, dict[str, Any]] = {
    "PILLAR-QFT-units_and_dimensions-v0": {
        "source_keys": ["ledger", "qft", "scalar_review"],
        "direct": _explicit(
            "qft_direct_scope_explicit", "qft",
            "The QFT surface explicitly covers canonical momentum, Hamiltonian-generator compatibility, unitarity, and normalization under bounded assumptions.",
            ["Canonical momentum surface assumptions", "Hamiltonian-generator interface compatibility", "Unitarity/injectivity assumptions", "Generator-unitarity route normalization"],
            [_obj("qft_surface_scope", "bounded canonical-momentum, generator, unitarity, and normalization surfaces")],
        ),
        "supplemental": _explicit(
            "qft_scalar_sandbox_explicit", "scalar_review",
            "The accepted imported action evidence is confined to a provisional classical real-scalar sandbox and grants no row-wide QFT or master-action authority.",
            ["provisional_classical_sandbox_route_only", "master_action_promoted", "toe_native_matter_derivation_claimed"],
            [_obj("narrow_scalar_sandbox", "accepted imported classical real-scalar sandbox only")],
        ),
        "signal": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
        "reason": "The accepted ledger has no QFT quantity inventory, while the direct source covers several bounded QFT surfaces and the separate scalar action remains narrow; row-wide object semantics must be fixed first.",
        "rationale_objects": ["qft_quantity_inventory", "qft_surface_scope", "narrow_scalar_sandbox"],
        "unsupported": [
            _unsupported(
                "qft_direct_physical_action_absent",
                "ABSENT_FROM_SOURCE",
                "The direct QFT source does not establish a physical action.",
                [_obj("qft_physical_action", "row-wide QFT physical action")],
                source_key="qft",
                absence_check={
                    "kind": "regex",
                    "pattern": r"(?<![-\w])action(?![-\w])",
                    "flags": ["IGNORECASE"],
                    "expected_match_count": 0,
                },
            ),
            _unsupported("qft_row_wide_inventory_unestablished", "INFERRED_NOT_ESTABLISHED", "A row-wide QFT object and unit inventory is not established.", [_obj("qft_row_wide_inventory", "complete row-wide QFT unit-bearing object inventory")]),
        ],
    },
    "PILLAR-GR-units_and_dimensions-v0": {
        "source_keys": ["ledger", "gr"],
        "direct": _explicit("gr_bounded_poisson_explicit", "gr", "The GR source explicitly supplies a bounded discrete weak-field Poisson surface and an action-native route.", ["action-level derivation of the weak-field discrete Poisson equation", "Bounded/discrete weak-field v0 only", "Canonical route remains action-native"], [_obj("weak_field_poisson_surface", "bounded discrete weak-field Poisson governing-equation surface")]),
        "signal": "GOVERNING_EQUATION_READY",
        "reason": "The bounded weak-field Poisson equation surface can organize a later term-balance derivation without importing full-GR or master-action authority.",
        "rationale_objects": ["gr_quantity_inventory", "weak_field_poisson_surface"],
        "unsupported": [_unsupported("gr_full_dimensional_closure_unestablished", "INFERRED_NOT_ESTABLISHED", "Full Einstein dimensional closure, term units, coordinate conventions, and explicit constants are not established.", [_obj("full_gr_dimensional_system", "full GR dimensional system")])],
    },
    "PILLAR-QM-units_and_dimensions-v0": {
        "source_keys": ["ledger", "qm"],
        "direct": _explicit("qm_direct_scope_explicit", "qm", "The QM source explicitly supplies bounded Schrodinger-form, state-evolution-contract, and unitary-consistency surfaces.", ["Schrodinger-form derivation", "QMStateEvolvesUnderContract", "Unitary-consistency track"], [_obj("qm_supported_surfaces", "bounded Schrodinger-form, state-contract, and unitary-consistency surfaces")]),
        "signal": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
        "reason": "The accepted ledger has no QM quantity inventory; the supported bounded surfaces do not by themselves define the row-wide state, observable, generator, time, probability, measurement, or open-system object inventory.",
        "rationale_objects": ["qm_quantity_inventory", "qm_supported_surfaces"],
        "unsupported": [
            _unsupported(
                "qm_hamiltonian_absent",
                "ABSENT_FROM_SOURCE",
                "The bound QM source does not establish a Hamiltonian.",
                [_obj("qm_hamiltonian", "QM Hamiltonian object")],
                source_key="qm",
                absence_check={
                    "kind": "casefold_substring",
                    "substring": "Hamiltonian",
                    "expected_match_count": 0,
                },
            ),
            _unsupported("qm_row_wide_inventory_unestablished", "INFERRED_NOT_ESTABLISHED", "The row-wide QM object inventory is not established.", [_obj("qm_row_wide_inventory", "state, observable, generator, time, probability, measurement, and open-system objects")]),
        ],
    },
    "PILLAR-STAT-units_and_dimensions-v0": {
        "source_keys": ["ledger", "stat"],
        "direct": _explicit("stat_direct_scope_explicit", "stat", "The STAT planning source explicitly names entropy/entropy-production, flux/balance-law, regime, and admissibility surfaces as bounded placeholders.", ["planning-only artifact", "entropy / entropy-production object surface", "flux / balance law object surface", "regime assumptions object surface", "admissibility / causality / positivity"], [_obj("stat_supported_surfaces", "bounded entropy, flux, balance, regime, and admissibility planning surfaces")]),
        "signal": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
        "reason": "The accepted ledger has no STAT quantity inventory and the bounded planning surface distinguishes several carriers; exact object semantics must precede dimensional analysis.",
        "rationale_objects": ["stat_quantity_inventory", "stat_supported_surfaces"],
        "unsupported": [
            _unsupported(
                "stat_probability_absent",
                "ABSENT_FROM_SOURCE",
                "The bound STAT source does not establish probability semantics.",
                [_obj("stat_probability", "probability distribution or probability rule")],
                source_key="stat",
                absence_check={
                    "kind": "casefold_substring",
                    "substring": "probability",
                    "expected_match_count": 0,
                },
            ),
            _unsupported(
                "stat_transport_absent",
                "ABSENT_FROM_SOURCE",
                "The bound STAT source does not establish a transport law.",
                [_obj("stat_transport", "transport equation or transport law")],
                source_key="stat",
                absence_check={
                    "kind": "casefold_substring",
                    "substring": "transport",
                    "expected_match_count": 0,
                },
            ),
        ],
    },
    "PILLAR-EM-units_and_dimensions-v0": {
        "source_keys": ["ledger", "em"],
        "direct": _explicit("em_objects_and_open_units_explicit", "em", "The EM source explicitly identifies gauge-potential and field-strength objects while recording UNITS_NOT_SELECTED.", ["Gauge potential object", "typed `F_munu` structure", "UNITS_NOT_SELECTED"], [_obj("em_typed_objects", "gauge-potential and field-strength object chain"), _obj("em_unit_convention", "currently unselected EM unit convention")]),
        "signal": "CONVENTION_OPEN",
        "reason": "Typed EM objects are available but the source explicitly leaves the unit convention unselected, so convention and constant-restoration work must precede assignments.",
        "rationale_objects": ["em_typed_objects", "em_unit_convention"],
        "unsupported": [_unsupported("em_units_unestablished", "INFERRED_NOT_ESTABLISHED", "No EM unit system, dimensions, constants, or restoration map is established.", [_obj("em_dimensional_system", "complete EM dimensional convention")])],
    },
    "PILLAR-SR-units_and_dimensions-v0": {
        "source_keys": ["ledger", "sr"],
        "direct": _explicit("sr_interval_dimension_explicit", "sr", "The SR source explicitly records Lorentz-transform, interval-invariance, and symbolic dimensional-structure checks.", ["Lorentz transform object theorem surface", "interval-invariance preservation theorem surface", "dimensional structure is preserved"], [_obj("sr_transform_interval", "Lorentz-transform and interval dimensional-structure surface")]),
        "signal": "CONVENTION_OPEN",
        "reason": "The transform and interval surfaces are explicit while the accepted ledger leaves the coordinate/unit convention null; a convention audit and possible constant restoration must come first.",
        "rationale_objects": ["sr_transform_interval", "sr_quantity_inventory"],
        "unsupported": [_unsupported("sr_c_suppression_unestablished", "INFERRED_NOT_ESTABLISHED", "The source does not establish whether coordinates are normalized or whether c is suppressed; v1 asserts no restoration value.", [_obj("sr_constant_policy", "SR coordinate and c-restoration policy")])],
    },
    "PILLAR-COSMO-units_and_dimensions-v0": {
        "source_keys": ["ledger", "cosmo"],
        "direct": _explicit("cosmo_background_scope_explicit", "cosmo", "The COSMO source explicitly freezes a planning-only background surface with metric, expansion-rate/Hubble-like, source-sector, and validity-domain objects.", ["planning-only cosmology target", "background metric object", "expansion-rate/Hubble-like object", "source-sector object", "domain-of-validity assumptions"], [_obj("cosmo_background_objects", "background metric, Hubble-like expansion, source-sector, and validity-domain planning objects")]),
        "signal": "OBJECT_SCOPE_REQUIRES_REFINEMENT",
        "reason": "The accepted ledger has no COSMO quantity inventory; the bounded planning source names several background carriers but does not define a row-wide unit-bearing inventory.",
        "rationale_objects": ["cosmo_quantity_inventory", "cosmo_background_objects"],
        "unsupported": [_unsupported("cosmo_unit_inventory_unestablished", "INFERRED_NOT_ESTABLISHED", "Exact coordinates, scale factor, density variables, observables, and units are not established by this source.", [_obj("cosmo_unit_inventory", "row-wide cosmology unit-bearing object inventory")])],
    },
}


def _ledger_row_map(ledger: dict[str, Any]) -> dict[str, tuple[str, dict[str, Any]]]:
    return {row["row_id"]: (kind, row) for kind, row in v0._ledger_rows(ledger)}


def _ledger_proposition(row_id: str, kind: str, row: dict[str, Any]) -> dict[str, Any]:
    empty_field = "quantity_rows" if kind == "pillar" else "mapping_rows"
    object_id = row_id.split("-")[1].lower() + ("_quantity_inventory" if kind == "pillar" else "_seam_readiness")
    return {
        "proposition_id": f"{row_id}_accepted_ledger_snapshot",
        "classification": "EXPLICITLY_STATED_BY_SOURCE",
        "source_id": SOURCES["ledger"]["source_id"],
        "statement": f"The accepted ledger records {row_id} as {row['guardrail_unit_state']} with an empty {empty_field} array.",
        "required_substrings": [],
        "ledger_assertion": {
            "assertion_type": "row_snapshot",
            "row_id": row_id,
            "guardrail_unit_state": row["guardrail_unit_state"],
            "empty_field": empty_field,
        },
        "objects": [_obj(object_id, f"accepted-ledger {row_id} {empty_field} and blocker state")],
        "supports_route": True,
    }


def _matrix_for_row(row_id: str, kind: str, row: dict[str, Any], ledger: dict[str, Any]) -> dict[str, Any]:
    ledger_prop = _ledger_proposition(row_id, kind, row)
    if kind == "seam":
        source_keys = ["ledger", "target_map"]
        direct = _explicit(
            f"{row_id}_target_map_scope_explicit", "target_map",
            "The bounded target map identifies this seam as an open nonclaim scope.",
            ["_".join(item.removeprefix("PILLAR-") for item in row["pillar_ids"])],
            [_obj("seam_scope", "bounded seam identity and open-scope planning surface")],
            supports_route=False,
        )
        endpoint_states = {item["pillar_id"]: item["guardrail_unit_state"] for item in ledger["pillar_rows"]}
        endpoints = row["pillar_ids"]
        exact_endpoint_states = {pillar: endpoint_states[pillar] for pillar in endpoints}
        endpoint_prop = {
            "proposition_id": f"{row_id}_endpoint_readiness_explicit",
            "classification": "EXPLICITLY_STATED_BY_SOURCE",
            "source_id": SOURCES["ledger"]["source_id"],
            "statement": (
                "The accepted ledger binds this seam to the exact endpoint pillar states "
                f"{exact_endpoint_states}."
            ),
            "required_substrings": [],
            "ledger_assertion": {
                "assertion_type": "endpoint_readiness",
                "seam_row_id": row_id,
                "pillar_ids": endpoints,
                "endpoint_states": exact_endpoint_states,
            },
            "objects": [
                _obj(
                    f"{row_id}_endpoint_readiness",
                    "accepted-ledger endpoint pillar identities and exact blocker states",
                )
            ],
            "supports_route": True,
        }
        derived = {
            "proposition_id": f"{row_id}_route_research_blocked",
            "classification": "DERIVED_FROM_SOURCE",
            "source_id": None,
            "statement": "Neither endpoint has a resolved internal unit system, so SEAM_CONVERSION_MAP is unavailable and the closed taxonomy selects RESEARCH_BLOCKED.",
            "premise_ids": [ledger_prop["proposition_id"], endpoint_prop["proposition_id"]],
            "derivation_rule": "UNRESOLVED_ENDPOINTS_BLOCK_SEAM_CONVERSION",
            "derived_facts": {"endpoint_states": exact_endpoint_states},
            "objects": [],
            "supports_route": True,
            "route_signal": "ENDPOINTS_NOT_RESOLVED",
        }
        unsupported = [
            _unsupported(f"{row_id}_conversion_unestablished", "INFERRED_NOT_ESTABLISHED", "Quantity pairs, conversion constants/maps, matching dimensions, physical-meaning preservation, and seam admissibility are not established.", [_obj("seam_conversion_map", "reviewed cross-pillar unit conversion map")])
        ]
        propositions = [ledger_prop, endpoint_prop, direct, derived, *unsupported]
        reason = "The accepted ledger explicitly leaves both endpoint unit systems unresolved or unknown; therefore no seam conversion route is available."
        rationale_objects = [
            ledger_prop["objects"][0]["object_id"],
            endpoint_prop["objects"][0]["object_id"],
        ]
    else:
        spec = PILLAR_SPECS[row_id]
        source_keys = spec["source_keys"]
        propositions = [ledger_prop, spec["direct"]]
        if "supplemental" in spec:
            propositions.append(spec["supplemental"])
        premise_ids = [ledger_prop["proposition_id"], spec["direct"]["proposition_id"]]
        if spec.get("supplemental", {}).get("supports_route"):
            premise_ids.append(spec["supplemental"]["proposition_id"])
        derived = {
            "proposition_id": f"{row_id}_route_signal",
            "classification": "DERIVED_FROM_SOURCE",
            "source_id": None,
            "statement": f"The supported ledger and bounded-source propositions produce the route signal {spec['signal']} without assigning a unit.",
            "premise_ids": premise_ids,
            "derivation_rule": "CLOSED_ROUTE_TAXONOMY_FROM_SUPPORTED_EVIDENCE",
            "objects": [],
            "supports_route": True,
            "route_signal": spec["signal"],
        }
        propositions.extend([derived, *spec["unsupported"]])
        reason = spec["reason"]
        rationale_objects = spec["rationale_objects"]
    return {
        "row_id": row_id,
        "source_bindings": [copy.deepcopy(SOURCES[key]) for key in source_keys],
        "propositions": copy.deepcopy(propositions),
        "supported_proposition_ids": [item["proposition_id"] for item in propositions if item["supports_route"]],
        "unsupported_proposition_ids": [item["proposition_id"] for item in propositions if not item["supports_route"]],
        "object_coverage": sorted({obj["object_id"] for item in propositions for obj in item["objects"]}),
        "rationale_object_ids": rationale_objects,
        "route_reason": reason,
        "route_recomputed_not_inherited": True,
        "scalar_evidence_scope": "NARROW_CLASSICAL_REAL_SCALAR_ONLY" if row_id.startswith("PILLAR-QFT") else "NOT_APPLICABLE",
    }


def _select_route(matrix: dict[str, Any]) -> str:
    signals = {
        item.get("route_signal")
        for item in matrix["propositions"]
        if item["classification"] == "DERIVED_FROM_SOURCE" and item["supports_route"]
    }
    mapping = {
        "GOVERNING_EQUATION_READY": "EQUATION_BALANCE_DERIVATION",
        "CONVENTION_OPEN": "CONVENTION_AND_CONSTANT_RESTORATION",
        "OBJECT_SCOPE_REQUIRES_REFINEMENT": "OBJECT_SEMANTICS_REFINEMENT",
        "ENDPOINTS_NOT_RESOLVED": "RESEARCH_BLOCKED",
    }
    routes = {mapping[signal] for signal in signals if signal in mapping}
    if len(routes) != 1:
        raise ValueError(f"evidence matrix does not yield exactly one route: {matrix['row_id']}")
    return routes.pop()


def _frozen_inputs() -> list[dict[str, str]]:
    return [
        *copy.deepcopy(v0._input_bindings()),
        {"artifact_id": "ROUTE_SELECTION_PACKET_v0", "path": V0_PACKET_RELATIVE_PATH, "sha256": V0_PACKET_SHA256},
        {"artifact_id": "ROUTE_SELECTION_MANIFEST_v0", "path": V0_MANIFEST_RELATIVE_PATH, "sha256": V0_MANIFEST_SHA256},
        {"artifact_id": "ROUTE_SELECTION_REPORT_v0", "path": V0_REPORT_RELATIVE_PATH, "sha256": V0_REPORT_SHA256},
        {"artifact_id": "ROUTE_SELECTION_RESULT_REVIEW_v0", "path": V0_REVIEW_RELATIVE_PATH, "sha256": V0_REVIEW_SHA256},
        {"artifact_id": "ROUTE_SELECTION_RESULT_REVIEW_TOOL_v0", "path": V0_REVIEW_TOOL_RELATIVE_PATH, "sha256": V0_REVIEW_TOOL_SHA256},
    ]


def load_inputs() -> tuple[dict[str, Any], dict[str, Any]]:
    ledger, _ = v0.load_inputs()
    for binding in _frozen_inputs():
        path = REPO_ROOT / binding["path"]
        if not path.is_file() or sha256_path(path) != binding["sha256"]:
            raise ValueError(f"frozen input mismatch: {binding['path']}")
    review = json.loads((REPO_ROOT / V0_REVIEW_RELATIVE_PATH).read_bytes())
    if not (
        review.get("accepted") is False
        and review.get("verdict") == "B-BLOCKED"
        and review.get("mismatch_codes") == CORRECTED_MISMATCH_CODES
        and review.get("selected_next_target") == TARGET
    ):
        raise ValueError("v0 review does not authorize the exact v1 correction target")
    return ledger, review


ROW_REQUIRED_FIELDS = v0.ROW_REQUIRED_FIELDS | {
    "evidence_matrix",
    "rationale_object_ids",
    "route_recomputed_from_supported_evidence",
    "route_support_proposition_ids",
}


def build_packet(ledger: dict[str, Any] | None = None) -> dict[str, Any]:
    if ledger is None:
        ledger, _ = load_inputs()
    packet = v0.build_packet(ledger)
    row_map = _ledger_row_map(ledger)
    for route_row in packet["route_selections"]:
        row_id = route_row["row_id"]
        kind, ledger_row = row_map[row_id]
        matrix = _matrix_for_row(row_id, kind, ledger_row, ledger)
        route_row["evidence_matrix"] = matrix
        route_row["available_evidence"] = [
            item["statement"]
            for item in matrix["propositions"]
            if item["supports_route"]
        ]
        route_row["missing_evidence"] = [
            item["statement"]
            for item in matrix["propositions"]
            if item["classification"] in {"INFERRED_NOT_ESTABLISHED", "ABSENT_FROM_SOURCE"}
        ]
        route_row["selected_response_route"] = _select_route(matrix)
        route_row["selection_reason"] = matrix["route_reason"]
        route_row["supplemental_evidence_bindings"] = [
            {"path": item["path"], "sha256": item["sha256"]}
            for item in matrix["source_bindings"]
            if item["source_id"] != SOURCES["ledger"]["source_id"]
        ]
        route_row["rationale_object_ids"] = matrix["rationale_object_ids"]
        route_row["route_support_proposition_ids"] = matrix["supported_proposition_ids"]
        route_row["route_recomputed_from_supported_evidence"] = True
    packet.update(
        {
            "schema_id": PACKET_SCHEMA_ID,
            "target": TARGET,
            "failure_target": FAILURE_TARGET,
            "selected_next_target": SUCCESSOR_TARGET,
            "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
            "status": STATUS,
            "packet_result": PACKET_RESULT,
            "strict_packet_result": STRICT_PACKET_RESULT,
            "input_artifacts": _frozen_inputs(),
            "evidence_classification_taxonomy": list(CLASSIFICATIONS),
            "route_map_recomputed_not_inherited": True,
            "source_attribution_repair": {
                "correction_scope": "SOURCE_ATTRIBUTION_ONLY",
                "corrected_mismatch_codes": CORRECTED_MISMATCH_CODES,
                "v0_route_map_treated_as_authority": False,
                "v1_route_map_changed_after_recomputation": False,
            },
            "lineage": {
                "v0_preparation_commit": V0_PREPARATION_COMMIT,
                "v0_rejection_commit": V0_REVIEW_COMMIT,
                "v0_preparation_packet_sha256": V0_PACKET_SHA256,
                "v0_rejection_report_sha256": V0_REVIEW_SHA256,
            },
        }
    )
    return packet


DECISION_IDS = [
    *v0.DECISION_IDS,
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


def _row_by_id(packet: dict[str, Any], row_id: str) -> dict[str, Any]:
    return next(row for row in packet["route_selections"] if row["row_id"] == row_id)


def _absence_check_passes(text: str, check: dict[str, Any]) -> bool:
    expected = check.get("expected_match_count")
    if expected != 0:
        return False
    kind = check.get("kind")
    if kind == "casefold_substring":
        substring = check.get("substring")
        return isinstance(substring, str) and text.casefold().count(substring.casefold()) == expected
    if kind == "regex":
        pattern = check.get("pattern")
        flags = check.get("flags", [])
        if not isinstance(pattern, str) or flags not in ([], ["IGNORECASE"]):
            return False
        regex_flags = re.IGNORECASE if flags == ["IGNORECASE"] else 0
        return len(re.findall(pattern, text, flags=regex_flags)) == expected
    return False


def packet_validation_failures(packet: dict[str, Any], ledger: dict[str, Any]) -> list[str]:
    failed: set[str] = set()
    rows = packet.get("route_selections", [])
    row_map = _ledger_row_map(ledger)
    by_id = {row.get("row_id"): row for row in rows if isinstance(row, dict)}
    try:
        frozen_ok = packet.get("input_artifacts") == _frozen_inputs() and all(
            sha256_path(REPO_ROOT / item["path"]) == item["sha256"]
            for item in _frozen_inputs()
        )
    except (OSError, KeyError):
        frozen_ok = False
    if not frozen_ok:
        failed.add("accepted_review_and_ledger_hashes_match")
        failed.add("source_path_hash_pairs_are_exactly_rebound")
    identity_ok = len(rows) == 12 and set(by_id) == set(row_map)
    if identity_ok:
        identity_ok = all(
            set(by_id[row_id]) == ROW_REQUIRED_FIELDS
            and by_id[row_id]["current_status"] == source["guardrail_unit_state"]
            and by_id[row_id]["source_evidence_pointer"] == source["evidence_pointer"]
            for row_id, (_, source) in row_map.items()
        )
    if not identity_ok:
        failed.add("exact_twelve_row_identity_status_and_evidence_bindings_preserved")
    one_route_ok = len(rows) == 12
    for row in rows:
        try:
            one_route_ok = one_route_ok and isinstance(row["selected_response_route"], str)
            one_route_ok = one_route_ok and row["selected_response_route"] == _select_route(row["evidence_matrix"])
        except (KeyError, TypeError, ValueError):
            one_route_ok = False
    if not one_route_ok:
        failed.add("each_row_selects_exactly_one_primary_route")
    if packet.get("route_count") != 8 or packet.get("route_taxonomy") != v0.ROUTE_TAXONOMY or packet.get("ordered_selection_criteria") != v0.ORDERED_SELECTION_CRITERIA:
        failed.add("route_taxonomy_is_closed_and_selection_order_is_preserved")
    if v0._contains_assignment_keys(packet) or packet.get("boundary") != v0.BOUNDARY:
        failed.add("no_unit_dimension_constant_or_mapping_assignment_is_emitted")
    if any(row.get("current_status") == "unit_unknown" and "proposed_unit_assignment" in row for row in rows):
        failed.add("unit_unknown_rows_cannot_receive_assignments_without_evidence")
    if any(row.get("current_status") not in {"unit_unknown", "unresolved"} for row in rows) or packet.get("policy", {}).get("route_selection_resolves_blocker") is not False:
        failed.add("natural_units_do_not_resolve_unresolved_rows")
    if packet.get("policy", {}).get("dimensionless_coordinates_are_physical_distances") is not False:
        failed.add("dimensionless_coordinates_are_not_physical_distances")
    if packet.get("policy", {}).get("suppressed_constant_omission_allowed") is not False or packet.get("policy", {}).get("suppressed_constants_requiring_explicit_treatment") != ["c", "hbar", "G", "k_B"]:
        failed.add("suppressed_constants_require_explicit_restoration")
    if any(row.get("row_kind") == "seam" and row.get("selected_response_route") == "SEAM_CONVERSION_MAP" for row in rows):
        failed.add("seam_map_requires_two_reviewed_internal_unit_systems")
    if packet.get("policy", {}).get("candidate_master_action_self_support_allowed") is not False or any("candidate master action" in text.lower() for row in rows for text in row.get("available_evidence", [])):
        failed.add("candidate_master_action_is_not_self_supporting_evidence")
    if packet.get("policy", {}).get("normalization_convention_is_empirical_scale") is not False:
        failed.add("normalization_conventions_are_not_empirical_scales")
    boundary = packet.get("boundary", {})
    if packet.get("claim_ceiling_level") != 3 or boundary.get("route_selection_is_resolution") is not False or boundary.get("dimensional_closure_claimed") is not False or boundary.get("pillar_completion_claimed") is not False or boundary.get("seam_admissibility_claimed") is not False:
        failed.add("route_selection_does_not_promote_dimensional_closure")
    if boundary.get("C_k_action_embedding_authorized") is not False:
        failed.add("C_k_embedding_remains_forbidden_before_dimensions_are_known")
    try:
        counts_ok = packet.get("family_level_counts") == v0._family_counts(rows)
    except (KeyError, TypeError):
        counts_ok = False
    if not counts_ok:
        failed.add("family_level_counts_are_planning_counts_only")
    if not (
        packet.get("schema_id") == PACKET_SCHEMA_ID
        and packet.get("target") == TARGET
        and packet.get("status") == STATUS
        and packet.get("packet_result") == PACKET_RESULT
        and packet.get("strict_packet_result") == STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == SUCCESSOR_TARGET
        and packet.get("selected_next_target_kind") == SUCCESSOR_TARGET_KIND
        and packet.get("nonclaims") == v0.NONCLAIMS
    ):
        failed.add("all_nonclaims_and_claim_ceiling_boundaries_are_preserved")
    review_ok = packet.get("lineage") == {
        "v0_preparation_commit": V0_PREPARATION_COMMIT,
        "v0_rejection_commit": V0_REVIEW_COMMIT,
        "v0_preparation_packet_sha256": V0_PACKET_SHA256,
        "v0_rejection_report_sha256": V0_REVIEW_SHA256,
    } and packet.get("source_attribution_repair", {}).get("corrected_mismatch_codes") == CORRECTED_MISMATCH_CODES
    if not review_ok:
        failed.add("frozen_v0_rejection_and_v1_authorization_match")

    matrices_ok = len(rows) == 12 and all(row.get("evidence_matrix", {}).get("row_id") == row.get("row_id") for row in rows)
    anchored_ok = derived_ok = unsupported_ok = rationale_ok = authority_ok = hash_ok = definitions_ok = True
    definitions: dict[tuple[str, str], str] = {}
    for row in rows:
        matrix = row.get("evidence_matrix", {})
        bindings = {item.get("source_id"): item for item in matrix.get("source_bindings", []) if isinstance(item, dict)}
        propositions = {item.get("proposition_id"): item for item in matrix.get("propositions", []) if isinstance(item, dict)}
        for binding in bindings.values():
            try:
                hash_ok = hash_ok and sha256_path(REPO_ROOT / binding["path"]) == binding["sha256"]
            except (OSError, KeyError):
                hash_ok = False
        for prop in propositions.values():
            classification = prop.get("classification")
            if classification == "EXPLICITLY_STATED_BY_SOURCE":
                binding = bindings.get(prop.get("source_id"))
                if binding is None:
                    anchored_ok = False
                    continue
                if prop.get("ledger_assertion"):
                    assertion = prop["ledger_assertion"]
                    assertion_type = assertion.get("assertion_type")
                    if assertion_type == "row_snapshot":
                        source = row_map.get(assertion.get("row_id"), (None, {}))[1]
                        anchored_ok = (
                            anchored_ok
                            and source.get("guardrail_unit_state") == assertion.get("guardrail_unit_state")
                            and source.get(assertion.get("empty_field")) == []
                        )
                    elif assertion_type == "endpoint_readiness":
                        seam = row_map.get(assertion.get("seam_row_id"), (None, {}))[1]
                        pillar_states = {
                            item["pillar_id"]: item["guardrail_unit_state"]
                            for item in ledger.get("pillar_rows", [])
                        }
                        pillar_ids = assertion.get("pillar_ids")
                        expected_states = (
                            {pillar_id: pillar_states.get(pillar_id) for pillar_id in pillar_ids}
                            if isinstance(pillar_ids, list)
                            else None
                        )
                        anchored_ok = (
                            anchored_ok
                            and seam.get("pillar_ids") == pillar_ids
                            and assertion.get("endpoint_states") == expected_states
                            and isinstance(expected_states, dict)
                            and all(state in {"unit_unknown", "unresolved"} for state in expected_states.values())
                        )
                    else:
                        anchored_ok = False
                else:
                    text = (REPO_ROOT / binding["path"]).read_text(encoding="utf-8").casefold()
                    anchored_ok = anchored_ok and all(token.casefold() in text for token in prop.get("required_substrings", []))
            if classification == "DERIVED_FROM_SOURCE":
                premises = prop.get("premise_ids", [])
                derived_ok = derived_ok and bool(premises) and all(
                    premise in propositions
                    and propositions[premise].get("classification") in SUPPORTING_CLASSIFICATIONS
                    and propositions[premise].get("supports_route") is True
                    for premise in premises
                )
                derived_ok = derived_ok and prop.get("derivation_rule") in {"CLOSED_ROUTE_TAXONOMY_FROM_SUPPORTED_EVIDENCE", "UNRESOLVED_ENDPOINTS_BLOCK_SEAM_CONVERSION"}
                if prop.get("derivation_rule") == "UNRESOLVED_ENDPOINTS_BLOCK_SEAM_CONVERSION":
                    endpoint_premises = [
                        propositions[premise]
                        for premise in premises
                        if premise in propositions
                        and propositions[premise].get("ledger_assertion", {}).get("assertion_type")
                        == "endpoint_readiness"
                    ]
                    derived_ok = (
                        derived_ok
                        and len(endpoint_premises) == 1
                        and prop.get("derived_facts", {}).get("endpoint_states")
                        == endpoint_premises[0]["ledger_assertion"].get("endpoint_states")
                    )
            if classification == "ABSENT_FROM_SOURCE":
                binding = bindings.get(prop.get("source_id"))
                check = prop.get("absence_check")
                if binding is None or not isinstance(check, dict):
                    anchored_ok = False
                else:
                    text = (REPO_ROOT / binding["path"]).read_text(encoding="utf-8")
                    anchored_ok = anchored_ok and _absence_check_passes(text, check)
            if classification in {"INFERRED_NOT_ESTABLISHED", "ABSENT_FROM_SOURCE"} and prop.get("supports_route") is not False:
                unsupported_ok = False
            if prop.get("supports_route"):
                binding = bindings.get(prop.get("source_id")) if prop.get("source_id") else None
                if binding is not None and binding.get("authority_class") not in SUPPORTING_AUTHORITY_CLASSES:
                    authority_ok = False
            for obj in prop.get("objects", []):
                source_id = prop.get("source_id") or "DERIVED"
                key = (source_id, obj.get("object_id"))
                definition = obj.get("definition")
                if key in definitions and definitions[key] != definition:
                    definitions_ok = False
                definitions[key] = definition
        support_ids = set(matrix.get("supported_proposition_ids", []))
        supported_objects = {
            obj["object_id"]
            for prop_id, prop in propositions.items()
            if prop_id in support_ids and prop.get("supports_route")
            for obj in prop.get("objects", [])
        }
        rationale_ok = rationale_ok and set(matrix.get("rationale_object_ids", [])) <= supported_objects
    if not matrices_ok:
        failed.add("evidence_matrix_present_once_per_row")
    if not anchored_ok:
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
    qft = by_id.get("PILLAR-QFT-units_and_dimensions-v0", {})
    if qft.get("evidence_matrix", {}).get("scalar_evidence_scope") != "NARROW_CLASSICAL_REAL_SCALAR_ONLY" or packet.get("source_attribution_repair", {}).get("v0_route_map_treated_as_authority") is not False:
        failed.add("narrow_scalar_evidence_is_not_promoted_to_full_qft")
    if not definitions_ok:
        failed.add("source_object_definitions_are_nonconflicting")
    return [decision_id for decision_id in DECISION_IDS if decision_id in failed]


def _mutate(packet: dict[str, Any], mutation: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    changed = copy.deepcopy(packet)
    mutation(changed)
    return changed


def _append_claim(packet: dict[str, Any], row_id: str, proposition_id: str, token: str, object_id: str) -> None:
    row = _row_by_id(packet, row_id)
    source_id = row["evidence_matrix"]["source_bindings"][1]["source_id"]
    row["evidence_matrix"]["propositions"].append({
        "proposition_id": proposition_id,
        "classification": "EXPLICITLY_STATED_BY_SOURCE",
        "source_id": source_id,
        "statement": f"Invented source claim: {token}",
        "required_substrings": [token],
        "objects": [_obj(object_id, f"invented {object_id}")],
        "supports_route": True,
    })
    row["evidence_matrix"]["supported_proposition_ids"].append(proposition_id)


def run_negative_controls(packet: dict[str, Any], ledger: dict[str, Any]) -> list[dict[str, Any]]:
    controls: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("assign_unit_to_unit_unknown_without_evidence", "unit_unknown_rows_cannot_receive_assignments_without_evidence", lambda p: p["route_selections"][0].__setitem__("proposed_unit_assignment", "invented")),
        ("natural_units_mark_unresolved_resolved", "natural_units_do_not_resolve_unresolved_rows", lambda p: p["route_selections"][1].__setitem__("current_status", "resolved")),
        ("dimensionless_coordinates_promoted_to_physical_distance", "dimensionless_coordinates_are_not_physical_distances", lambda p: p["policy"].__setitem__("dimensionless_coordinates_are_physical_distances", True)),
        ("suppressed_constant_omitted", "suppressed_constants_require_explicit_restoration", lambda p: p["policy"].__setitem__("suppressed_constant_omission_allowed", True)),
        ("two_incompatible_routes_assigned_without_priority", "each_row_selects_exactly_one_primary_route", lambda p: p["route_selections"][0].__setitem__("selected_response_route", ["ACTION_DIMENSION_DERIVATION", "OBJECT_SEMANTICS_REFINEMENT"])),
        ("seam_map_selected_with_incomplete_pillar_units", "seam_map_requires_two_reviewed_internal_unit_systems", lambda p: _row_by_id(p, "SEAM-QFT-GR-unit_map-v0").__setitem__("selected_response_route", "SEAM_CONVERSION_MAP")),
        ("candidate_master_action_used_as_self_evidence", "candidate_master_action_is_not_self_supporting_evidence", lambda p: p["route_selections"][0]["available_evidence"].append("The candidate master action supplies its own missing dimensions.")),
        ("normalization_convention_promoted_to_empirical_scale", "normalization_conventions_are_not_empirical_scales", lambda p: p["policy"].__setitem__("normalization_convention_is_empirical_scale", True)),
        ("routed_blocker_promoted_to_dimensional_closure", "route_selection_does_not_promote_dimensional_closure", lambda p: p["boundary"].__setitem__("dimensional_closure_claimed", True)),
        ("C_k_embedding_before_dimensions_known", "C_k_embedding_remains_forbidden_before_dimensions_are_known", lambda p: p["boundary"].__setitem__("C_k_action_embedding_authorized", True)),
        ("qft_action_claimed_without_action", "explicit_propositions_are_source_anchored", lambda p: _append_claim(p, "PILLAR-QFT-units_and_dimensions-v0", "invented_qft_action", "physical action", "qft_physical_action")),
        ("qm_hamiltonian_claimed_without_hamiltonian", "explicit_propositions_are_source_anchored", lambda p: _append_claim(p, "PILLAR-QM-units_and_dimensions-v0", "invented_qm_hamiltonian", "Hamiltonian", "qm_hamiltonian")),
        ("stat_probability_claimed_without_probability_semantics", "explicit_propositions_are_source_anchored", lambda p: _append_claim(p, "PILLAR-STAT-units_and_dimensions-v0", "invented_stat_probability", "probability", "stat_probability")),
        ("stat_transport_claimed_without_transport_law", "explicit_propositions_are_source_anchored", lambda p: _append_claim(p, "PILLAR-STAT-units_and_dimensions-v0", "invented_stat_transport", "transport law", "stat_transport")),
        ("narrow_scalar_evidence_promoted_to_full_qft", "narrow_scalar_evidence_is_not_promoted_to_full_qft", lambda p: _row_by_id(p, "PILLAR-QFT-units_and_dimensions-v0")["evidence_matrix"].__setitem__("scalar_evidence_scope", "ROW_WIDE_QFT")),
        ("absence_treated_as_positive_evidence", "inferred_and_absent_propositions_do_not_support_routes", lambda p: _row_by_id(p, "PILLAR-QM-units_and_dimensions-v0")["evidence_matrix"]["propositions"][-2].__setitem__("supports_route", True)),
        ("citation_hash_changed_without_rebinding", "source_path_hash_pairs_are_exactly_rebound", lambda p: _row_by_id(p, "PILLAR-GR-units_and_dimensions-v0")["evidence_matrix"]["source_bindings"][1].__setitem__("sha256", "0" * 64)),
        ("route_rationale_object_missing_from_inventory", "route_rationale_objects_are_supported", lambda p: _row_by_id(p, "PILLAR-QM-units_and_dimensions-v0")["evidence_matrix"]["rationale_object_ids"].append("measurement_object")),
        ("speculative_surface_treated_as_authoritative", "supporting_sources_have_authorized_bounded_class", lambda p: _row_by_id(p, "PILLAR-STAT-units_and_dimensions-v0")["evidence_matrix"]["source_bindings"][1].__setitem__("authority_class", "SPECULATIVE_SURFACE")),
        ("one_source_supports_conflicting_object_definitions", "source_object_definitions_are_nonconflicting", lambda p: _row_by_id(p, "PILLAR-QFT-units_and_dimensions-v0")["evidence_matrix"]["propositions"][1]["objects"].append(_obj("qft_surface_scope", "incompatible full-QFT definition"))),
    ]
    results = []
    for control_id, expected, mutation in controls:
        failures = packet_validation_failures(_mutate(packet, mutation), ledger)
        results.append({
            "control_id": control_id,
            "expected_failed_decision_id": expected,
            "fresh_deep_copy_used": True,
            "observed_failed_decision_ids": failures,
            "passed": expected in failures,
        })
    return results


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    ledger, _ = load_inputs()
    packet = build_packet(ledger)
    failures = packet_validation_failures(packet, ledger)
    if failures:
        details: list[str] = []
        for row in packet["route_selections"]:
            matrix = row["evidence_matrix"]
            bindings = {item["source_id"]: item for item in matrix["source_bindings"]}
            supported_objects = {
                obj["object_id"]
                for prop in matrix["propositions"]
                if prop["supports_route"]
                for obj in prop["objects"]
            }
            missing_objects = set(matrix["rationale_object_ids"]) - supported_objects
            if missing_objects:
                details.append(f"{row['row_id']}: unsupported rationale objects {sorted(missing_objects)}")
            for prop in matrix["propositions"]:
                if prop["classification"] != "EXPLICITLY_STATED_BY_SOURCE" or prop.get("ledger_assertion"):
                    continue
                binding = bindings[prop["source_id"]]
                text = (REPO_ROOT / binding["path"]).read_text(encoding="utf-8").casefold()
                missing = [token for token in prop["required_substrings"] if token.casefold() not in text]
                if missing:
                    details.append(f"{row['row_id']}: {prop['proposition_id']} missing {missing}")
        raise ValueError(f"canonical v1 packet failed decisions: {failures}; {'; '.join(details)}")
    controls = run_negative_controls(packet, ledger)
    if not all(control["passed"] for control in controls):
        raise ValueError("v1 negative control failure")
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "canonicalization": "UTF-8 JSON, sorted keys, indent=2, trailing newline",
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "input_artifacts": _frozen_inputs(),
        "packet": {"path": PACKET_RELATIVE_PATH, "schema_id": PACKET_SCHEMA_ID, "sha256": sha256_bytes(packet_raw)},
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "total_row_count": 12,
        "decision_count": len(DECISION_IDS),
        "negative_control_count": len(controls),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "status": STATUS,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "packet_result": PACKET_RESULT,
        "strict_packet_result": STRICT_PACKET_RESULT,
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "lineage": copy.deepcopy(packet["lineage"]),
        "source_attribution_repair": copy.deepcopy(packet["source_attribution_repair"]),
        "route_map_recomputed_not_inherited": True,
        "route_map": {row["row_id"]: row["selected_response_route"] for row in packet["route_selections"]},
        "family_level_counts": copy.deepcopy(packet["family_level_counts"]),
        "unit_unknown_row_count": 6,
        "unresolved_row_count": 6,
        "resolved_row_count": 0,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "negative_control_count": len(controls),
        "negative_controls": controls,
        "all_negative_controls_passed": True,
        "input_artifacts": _frozen_inputs(),
        "artifact_hashes": {"packet_sha256": sha256_bytes(packet_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "boundary": copy.deepcopy(v0.BOUNDARY),
        "nonclaims": copy.deepcopy(v0.NONCLAIMS),
        "packet_acceptance_authorized": False,
        "first_blocker_resolution_guardrail_authorized": False,
        "claim": "All twelve routes were recomputed from exact source-attribution matrices; no unit, dimension, constant, calibration, or seam mapping was derived.",
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build source-attribution-corrected unit-blocker route packet v1.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print(
            "wrote v1 source-attribution route packet; 12 routes recomputed, 0 resolved; "
            f"generator={sha256_path(SCRIPT_PATH)} "
            f"packet={sha256_path(PACKET_PATH)} "
            f"manifest={sha256_path(MANIFEST_PATH)} "
            f"report={sha256_path(REPORT_PATH)}"
        )
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(f"v1 route packet verified; {len(DECISION_IDS)}/{len(DECISION_IDS)} decisions and 20/20 controls pass")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
