from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import json
import platform
import re
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection as v0,
)
from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1 as v1,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/"
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v2.py"
)
PACKET_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-PACKET-v2.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-MANIFEST-v2.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260713_v2.json"
)
V1_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260712_v1.json"
)
PROMPT_RELATIVE_PATH = "Prompt.txt"
FROZEN_COMMIT_RECORD_RELATIVE_PATH = (
    "formal/docs/release/V2_TRACKED_BLOB_IDENTITY_FREEZE_20260721_v0.json"
)

PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
PROMPT_BASELINE_SHA256 = (
    "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
)
TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
FAILURE_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v3"
)
SUCCESSOR_TARGET = (
    "review_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2_result"
)
SUCCESSOR_TARGET_KIND = (
    "pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2_result_review"
)
POST_ACCEPTANCE_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0"
)
PACKET_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_v2"
)
MANIFEST_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_MANIFEST_v2"
)
REPORT_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260713_v2"
)
COMPATIBILITY_SCHEMA_ID = "EVIDENCE_ROUTE_COMPATIBILITY_MATRIX_v2"

V1_GENERATOR_RELATIVE_PATH = v1.SCRIPT_RELATIVE_PATH
V1_PACKET_RELATIVE_PATH = v1.PACKET_RELATIVE_PATH
V1_MANIFEST_RELATIVE_PATH = v1.MANIFEST_RELATIVE_PATH
V1_REPORT_RELATIVE_PATH = v1.REPORT_RELATIVE_PATH
V1_EXPECTED_HASHES = {
    V1_GENERATOR_RELATIVE_PATH: (
        "bb42efb91530da6134a5f41661b23736afa663171935140616066f6503257da4"
    ),
    V1_PACKET_RELATIVE_PATH: (
        "8c0de083b4f3bd94eb2bb1bc6fa963e1a4024a2d42169eef0e05e297400fdb70"
    ),
    V1_MANIFEST_RELATIVE_PATH: (
        "03130e8ddd32ee70c66af042a130494f659b13a50285cacbf0f9c13968e1ff73"
    ),
    V1_REPORT_RELATIVE_PATH: (
        "bbf299f594970641d437ff502767d7d175923219664f92bf59f415f6c3f20a06"
    ),
    V1_REVIEW_RELATIVE_PATH: (
        "aa2ee087a167a75a0ab144d034fe6a9e27c521f37cec792ea51adc5ced6c01a9"
    ),
}

CLAIM_LABEL_CONTEXTS = (
    "RELEASE_FACING_CURRENT",
    "LEGACY_UNMIGRATED_NONRELEASE",
    "SOURCE_UNDECLARED",
    "HISTORICAL_ARCHIVED",
)
AUTHORITY_CLASSES = (
    "FROZEN_ACCEPTED_LEDGER",
    "ACCEPTED_BOUNDED_REVIEW",
    "BOUNDED_ACCEPTED_MATHEMATICAL_SURFACE",
    "BOUNDED_PLANNING_NONCLAIM",
    "HISTORICAL_ONLY",
)
SOURCE_LOCATOR_TYPES = (
    "JSON_POINTER",
    "MARKDOWN_HEADING_LINE_RANGE",
    "LEAN_DECLARATION_NAME",
    "PYTHON_SYMBOL_NAME",
    "ARTIFACT_FIELD_PATH",
)
EXTRACTION_METHODS = (
    "EXACT_FIELD_READ",
    "EXACT_TEXT_EXTRACTION",
    "SYMBOL_DECLARATION_READ",
    "REGEX_ABSENCE_CHECK",
    "LEDGER_ROW_SNAPSHOT",
    "DERIVED_RECIPE",
)
SUPPORT_MODES = (
    "LEDGER_STATE",
    "POLICY_AUTHORITY",
    "LEGACY_THEOREM_SURFACE",
    "REVIEW_STATE_ASSERTION",
    "SUPPLIED_ONLY",
    "ABSENT_FROM_SOURCE",
    "DERIVED_FROM_SOURCE",
)
EVIDENCE_ROLES = (
    "REPOSITORY_STATE_EVIDENCE",
    "PLANNING_AUTHORITY",
    "MATHEMATICAL_DERIVATION",
    "SOURCE_ABSENCE_EVIDENCE",
    "CONDITIONAL_HYPOTHESIS",
    "DERIVED_EVIDENCE",
    "PHYSICAL_DERIVATION",
    "COMPUTATIONAL_PHYSICS_EVIDENCE",
    "EMPIRICAL_EVIDENCE",
    "HISTORICAL_CONTEXT",
)
ROUTE_TYPES = (
    "PLANNING_ROUTE_SELECTION",
    "SEMANTIC_REFINEMENT",
    "BLOCKER_IDENTIFICATION",
    "CONDITIONAL_THEOREM_HYPOTHESIS",
    "PHYSICAL_DERIVATION",
    "UNIT_RESOLUTION",
    "COMPUTATIONAL_VALIDATION",
    "EMPIRICAL_ADEQUACY",
    "PHYSICAL_CALIBRATION",
    "PILLAR_COMPLETION",
    "SEAM_CLOSURE",
    "HISTORICAL_CONTEXT",
)

RECORD_REQUIRED_FIELDS = {
    "evidence_id",
    "proposition_id",
    "source_id",
    "source_path",
    "source_hash",
    "source_identity_type",
    "source_frozen_commit",
    "source_git_blob_oid",
    "source_locator",
    "proposition_extraction_method",
    "source_declared_claim_label",
    "claim_label_context",
    "authority_class",
    "evidence_role",
    "exact_supported_proposition",
    "support_mode",
    "scope_ceiling",
    "requested_route_type",
    "unsupported_propositions",
    "derivation_dependencies",
    "derivation_recipe",
    "row_ids_supported",
    "conflict_status",
    "route_support_eligible",
}

POLICY_SOURCE_IDS = {
    "qft_bounded_surface",
    "qm_bounded_surface",
    "stat_planning_surface",
    "em_bounded_surface",
    "sr_bounded_surface",
    "cosmo_planning_surface",
    "pillar_target_map",
}
EXPECTED_SOURCE_AUTHORITY = {
    "accepted_unit_ledger": (
        "SOURCE_UNDECLARED",
        "FROZEN_ACCEPTED_LEDGER",
        "REPOSITORY_STATE_EVIDENCE",
        "LEDGER_STATE",
    ),
    "qft_bounded_surface": (
        "P-POLICY",
        "BOUNDED_PLANNING_NONCLAIM",
        "PLANNING_AUTHORITY",
        "POLICY_AUTHORITY",
    ),
    "gr_bounded_surface": (
        "T-PROVED",
        "BOUNDED_ACCEPTED_MATHEMATICAL_SURFACE",
        "MATHEMATICAL_DERIVATION",
        "LEGACY_THEOREM_SURFACE",
    ),
    "qm_bounded_surface": (
        "P-POLICY",
        "BOUNDED_PLANNING_NONCLAIM",
        "PLANNING_AUTHORITY",
        "POLICY_AUTHORITY",
    ),
    "stat_planning_surface": (
        "P-POLICY",
        "BOUNDED_PLANNING_NONCLAIM",
        "PLANNING_AUTHORITY",
        "POLICY_AUTHORITY",
    ),
    "em_bounded_surface": (
        "P-POLICY",
        "BOUNDED_PLANNING_NONCLAIM",
        "PLANNING_AUTHORITY",
        "POLICY_AUTHORITY",
    ),
    "sr_bounded_surface": (
        "P-POLICY",
        "BOUNDED_PLANNING_NONCLAIM",
        "PLANNING_AUTHORITY",
        "POLICY_AUTHORITY",
    ),
    "cosmo_planning_surface": (
        "P-POLICY",
        "BOUNDED_PLANNING_NONCLAIM",
        "PLANNING_AUTHORITY",
        "POLICY_AUTHORITY",
    ),
    "pillar_target_map": (
        "P-POLICY",
        "BOUNDED_PLANNING_NONCLAIM",
        "PLANNING_AUTHORITY",
        "POLICY_AUTHORITY",
    ),
    "accepted_scalar_sandbox_review": (
        "SOURCE_UNDECLARED",
        "ACCEPTED_BOUNDED_REVIEW",
        "REPOSITORY_STATE_EVIDENCE",
        "REVIEW_STATE_ASSERTION",
    ),
}

ROUTE_BY_SIGNAL = {
    "GOVERNING_EQUATION_READY": "EQUATION_BALANCE_DERIVATION",
    "CONVENTION_OPEN": "CONVENTION_AND_CONSTANT_RESTORATION",
    "OBJECT_SCOPE_REQUIRES_REFINEMENT": "OBJECT_SEMANTICS_REFINEMENT",
    "ENDPOINTS_NOT_RESOLVED": "RESEARCH_BLOCKED",
}

NONCLAIMS = sorted(
    set(v0.NONCLAIMS)
    | {
        "no unit, dimension vector, constant restoration, or seam map is assigned",
        "no first-unit target is selected before independent v2 review",
        "Maxwell-Dirac remains a preferred downstream candidate only",
        "no registry-maintenance, C_k, CCFT, seam-closure, or master-action work is authorized",
    }
)


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    normalized = _normalize(payload)
    return (
        json.dumps(
            normalized,
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _frozen_commit() -> str:
    record_path = REPO_ROOT / FROZEN_COMMIT_RECORD_RELATIVE_PATH
    payload = json.loads(record_path.read_text(encoding="utf-8"))
    commit = payload.get("frozen_commit")
    if (
        payload.get("schema_id")
        != "V2_TRACKED_BLOB_IDENTITY_FREEZE_20260721_v0"
        or not isinstance(commit, str)
        or not re.fullmatch(r"[0-9a-f]{40}", commit)
    ):
        raise ValueError("invalid V2 tracked-blob identity freeze record")
    return commit


def _git_blob_bytes(relative_path: str, *, commit: str | None = None) -> bytes:
    frozen_commit = commit or _frozen_commit()
    result = subprocess.run(
        ["git", "cat-file", "blob", f"{frozen_commit}:{relative_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise ValueError(
            f"missing frozen Git blob: {frozen_commit}:{relative_path}"
        )
    return result.stdout


def _git_blob_oid(relative_path: str, *, commit: str | None = None) -> str:
    frozen_commit = commit or _frozen_commit()
    result = subprocess.run(
        ["git", "rev-parse", f"{frozen_commit}:{relative_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
        text=True,
    )
    oid = result.stdout.strip()
    if result.returncode != 0 or not re.fullmatch(r"[0-9a-f]{40,64}", oid):
        raise ValueError(
            f"missing frozen Git blob identity: {frozen_commit}:{relative_path}"
        )
    return oid


def _identity_type(relative_path: str) -> str:
    if relative_path.startswith("formal/output/") or (
        relative_path.startswith("formal/docs/release/")
        and relative_path.endswith((".json", ".patch"))
    ):
        return "CANONICAL_ARTIFACT_SHA256"
    return "GIT_BLOB_SHA256"


def _frozen_identity(relative_path: str) -> dict[str, str]:
    commit = _frozen_commit()
    raw = _git_blob_bytes(relative_path, commit=commit)
    return {
        "path": relative_path,
        "identity_type": _identity_type(relative_path),
        "frozen_commit": commit,
        "git_blob_oid": _git_blob_oid(relative_path, commit=commit),
        "sha256": sha256_bytes(raw),
    }


def _identity_matches(binding: dict[str, Any]) -> bool:
    path = binding.get("path")
    if not isinstance(path, str):
        return False
    try:
        expected = _frozen_identity(path)
    except (OSError, ValueError, json.JSONDecodeError):
        return False
    return all(binding.get(key) == expected[key] for key in expected)


def _frozen_text(relative_path: str) -> str:
    return _git_blob_bytes(relative_path).decode("utf-8")


def _frozen_json(relative_path: str) -> dict[str, Any]:
    payload = json.loads(_git_blob_bytes(relative_path))
    if not isinstance(payload, dict):
        raise ValueError(f"frozen input root is not an object: {relative_path}")
    return payload


def _git_config(name: str) -> str:
    result = subprocess.run(
        ["git", "config", "--get", name],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
        text=True,
    )
    return result.stdout.strip() if result.returncode == 0 else "UNSET"


def _declared_label(relative_path: str) -> str:
    text = _frozen_text(relative_path)
    match = re.search(r"Classification:\s*\r?\n-\s*`([^`]+)`", text)
    return match.group(1) if match else "SOURCE_UNDECLARED"


def _markdown_locator(relative_path: str, anchors: list[str], *, whole_file: bool = False) -> dict[str, Any]:
    lines = _frozen_text(relative_path).splitlines()
    if whole_file:
        return {
            "locator_type": "MARKDOWN_HEADING_LINE_RANGE",
            "heading": "<entire document>",
            "start_line": 1,
            "end_line": len(lines),
        }
    positions: list[int] = []
    for anchor in anchors:
        matches = [index for index, line in enumerate(lines, 1) if anchor.casefold() in line.casefold()]
        if not matches:
            raise ValueError(f"source anchor missing in {relative_path}: {anchor}")
        positions.append(matches[0])
    start = min(positions)
    end = max(positions)
    heading_line = 1
    heading = "<document root>"
    for index in range(start, 0, -1):
        if lines[index - 1].lstrip().startswith("#"):
            heading_line = index
            heading = lines[index - 1].strip()
            break
    return {
        "locator_type": "MARKDOWN_HEADING_LINE_RANGE",
        "heading": heading,
        "heading_line": heading_line,
        "start_line": start,
        "end_line": end,
    }


def _json_pointer_for_row(ledger: dict[str, Any], row_id: str) -> str:
    for collection in ("pillar_rows", "seam_rows"):
        for index, row in enumerate(ledger.get(collection, [])):
            if row.get("row_id") == row_id:
                return f"/{collection}/{index}"
    raise ValueError(f"ledger row not found: {row_id}")


def _compatibility_result(support_mode: str, evidence_role: str, route_type: str) -> str:
    eligible: set[tuple[str, str, str]] = set()
    for candidate in ("PLANNING_ROUTE_SELECTION", "SEMANTIC_REFINEMENT", "BLOCKER_IDENTIFICATION"):
        eligible.add(("POLICY_AUTHORITY", "PLANNING_AUTHORITY", candidate))
    for candidate in (
        "PLANNING_ROUTE_SELECTION",
        "SEMANTIC_REFINEMENT",
        "BLOCKER_IDENTIFICATION",
        "CONDITIONAL_THEOREM_HYPOTHESIS",
    ):
        eligible.add(("SUPPLIED_ONLY", "CONDITIONAL_HYPOTHESIS", candidate))
    eligible.add(("LEDGER_STATE", "REPOSITORY_STATE_EVIDENCE", "BLOCKER_IDENTIFICATION"))
    eligible.add(("ABSENT_FROM_SOURCE", "SOURCE_ABSENCE_EVIDENCE", "BLOCKER_IDENTIFICATION"))
    for candidate in (
        "PLANNING_ROUTE_SELECTION",
        "SEMANTIC_REFINEMENT",
        "BLOCKER_IDENTIFICATION",
        "CONDITIONAL_THEOREM_HYPOTHESIS",
    ):
        eligible.add(("LEGACY_THEOREM_SURFACE", "MATHEMATICAL_DERIVATION", candidate))
    for candidate in ("PLANNING_ROUTE_SELECTION", "SEMANTIC_REFINEMENT", "BLOCKER_IDENTIFICATION"):
        eligible.add(("DERIVED_FROM_SOURCE", "DERIVED_EVIDENCE", candidate))
    eligible.add(("DERIVED_FROM_SOURCE", "PHYSICAL_DERIVATION", "PHYSICAL_DERIVATION"))
    eligible.add(("DERIVED_FROM_SOURCE", "COMPUTATIONAL_PHYSICS_EVIDENCE", "COMPUTATIONAL_VALIDATION"))
    eligible.add(("DERIVED_FROM_SOURCE", "EMPIRICAL_EVIDENCE", "EMPIRICAL_ADEQUACY"))
    eligible.add(("DERIVED_FROM_SOURCE", "EMPIRICAL_EVIDENCE", "PHYSICAL_CALIBRATION"))
    combination = (support_mode, evidence_role, route_type)
    if combination not in {
        (mode, role, route)
        for mode in SUPPORT_MODES
        for role in EVIDENCE_ROLES
        for route in ROUTE_TYPES
    }:
        raise ValueError(f"unknown compatibility combination: {combination}")
    if route_type in {"HISTORICAL_CONTEXT", "PILLAR_COMPLETION", "SEAM_CLOSURE"}:
        return "INELIGIBLE"
    return "ELIGIBLE" if combination in eligible else "INELIGIBLE"


def compatibility_matrix() -> dict[str, Any]:
    rows = [
        {
            "support_mode": support_mode,
            "evidence_role": evidence_role,
            "route_type": route_type,
            "result": _compatibility_result(support_mode, evidence_role, route_type),
        }
        for support_mode in SUPPORT_MODES
        for evidence_role in EVIDENCE_ROLES
        for route_type in ROUTE_TYPES
    ]
    return {
        "schema_id": COMPATIBILITY_SCHEMA_ID,
        "default_for_unknown_combination": "INELIGIBLE",
        "support_modes": list(SUPPORT_MODES),
        "evidence_roles": list(EVIDENCE_ROLES),
        "route_types": list(ROUTE_TYPES),
        "rows": rows,
        "row_count": len(rows),
    }


def _authority_fields(source_id: str, path: str) -> dict[str, str]:
    declared, authority, role, support = EXPECTED_SOURCE_AUTHORITY[source_id]
    if source_id == "gr_bounded_surface":
        context = "LEGACY_UNMIGRATED_NONRELEASE"
    elif source_id in POLICY_SOURCE_IDS:
        context = "RELEASE_FACING_CURRENT"
    else:
        context = "SOURCE_UNDECLARED"
    if declared != "SOURCE_UNDECLARED" and _declared_label(path) != declared:
        raise ValueError(f"source-declared label changed: {path}")
    return {
        "source_declared_claim_label": declared,
        "claim_label_context": context,
        "authority_class": authority,
        "evidence_role": role,
        "support_mode": support,
    }


def _record(
    *,
    row_id: str,
    proposition: dict[str, Any],
    binding: dict[str, Any],
    ledger: dict[str, Any],
) -> dict[str, Any]:
    source_id = binding["source_id"]
    path = binding["path"]
    identity = _frozen_identity(path)
    authority = _authority_fields(source_id, path)
    classification = proposition.get("classification")
    anchors = proposition.get("required_substrings", [])
    if proposition.get("ledger_assertion"):
        assertion = proposition["ledger_assertion"]
        pointer_row_id = assertion.get("row_id") or assertion.get("seam_row_id")
        locator = {
            "locator_type": "JSON_POINTER",
            "pointer": _json_pointer_for_row(ledger, pointer_row_id),
        }
        extraction = "LEDGER_ROW_SNAPSHOT"
        requested_route_type = "BLOCKER_IDENTIFICATION"
    elif classification == "ABSENT_FROM_SOURCE":
        locator = _markdown_locator(path, [], whole_file=True)
        extraction = "REGEX_ABSENCE_CHECK"
        requested_route_type = "BLOCKER_IDENTIFICATION"
        authority = {
            **authority,
            "evidence_role": "SOURCE_ABSENCE_EVIDENCE",
            "support_mode": "ABSENT_FROM_SOURCE",
        }
    elif path.endswith(".json"):
        locator = {
            "locator_type": "ARTIFACT_FIELD_PATH",
            "field_path": "/accepted",
        }
        extraction = "EXACT_FIELD_READ"
        requested_route_type = "HISTORICAL_CONTEXT"
    else:
        locator = _markdown_locator(path, anchors)
        extraction = "EXACT_TEXT_EXTRACTION"
        requested_route_type = "PLANNING_ROUTE_SELECTION"
    unsupported = []
    if classification == "ABSENT_FROM_SOURCE":
        unsupported = [
            "Source absence is a bounded documentary observation only and is not a physical no-go claim."
        ]
    route_support_eligible = (
        _compatibility_result(
            authority["support_mode"],
            authority["evidence_role"],
            requested_route_type,
        )
        == "ELIGIBLE"
    )
    return {
        "evidence_id": f"EV-{row_id}-{proposition['proposition_id']}",
        "proposition_id": proposition["proposition_id"],
        "source_id": source_id,
        "source_path": path,
        "source_hash": identity["sha256"],
        "source_identity_type": identity["identity_type"],
        "source_frozen_commit": identity["frozen_commit"],
        "source_git_blob_oid": identity["git_blob_oid"],
        "source_locator": locator,
        "proposition_extraction_method": extraction,
        **authority,
        "exact_supported_proposition": proposition["statement"],
        "scope_ceiling": requested_route_type,
        "requested_route_type": requested_route_type,
        "unsupported_propositions": unsupported,
        "derivation_dependencies": [],
        "derivation_recipe": None,
        "row_ids_supported": [row_id],
        "conflict_status": "NO_CONFLICT",
        "route_support_eligible": route_support_eligible,
    }


def _source_bindings(matrix: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {item["source_id"]: item for item in matrix["source_bindings"]}


def _route_derivation(
    row_id: str,
    signal: str,
    premise_records: list[dict[str, Any]],
    expected_route: str,
) -> dict[str, Any]:
    recipe = {
        "ordered_premise_proposition_ids": [item["proposition_id"] for item in premise_records],
        "transformation_identifier": (
            "UNRESOLVED_ENDPOINTS_BLOCK_SEAM_CONVERSION"
            if signal == "ENDPOINTS_NOT_RESOLVED"
            else "CLOSED_ROUTE_TAXONOMY_FROM_ELIGIBLE_PROPOSITIONS"
        ),
        "transformation_parameters": {"route_signal": signal},
        "expected_derived_value": expected_route,
    }
    eligible = all(item["route_support_eligible"] for item in premise_records)
    eligible = eligible and (
        _compatibility_result(
            "DERIVED_FROM_SOURCE",
            "DERIVED_EVIDENCE",
            "BLOCKER_IDENTIFICATION" if signal == "ENDPOINTS_NOT_RESOLVED" else "PLANNING_ROUTE_SELECTION",
        )
        == "ELIGIBLE"
    )
    return {
        "proposition_id": f"{row_id}_route_derivation_v2",
        "support_mode": "DERIVED_FROM_SOURCE",
        "evidence_role": "DERIVED_EVIDENCE",
        "route_type": (
            "BLOCKER_IDENTIFICATION"
            if signal == "ENDPOINTS_NOT_RESOLVED"
            else "PLANNING_ROUTE_SELECTION"
        ),
        "derivation_recipe": recipe,
        "route_support_eligible": eligible,
    }


def _implementation_closure() -> dict[str, Any]:
    paths = [
        SCRIPT_RELATIVE_PATH,
        "formal/python/meta/repo_environment.py",
        v0.SCRIPT_RELATIVE_PATH,
        v1.SCRIPT_RELATIVE_PATH,
    ]
    tree = ast.parse(SCRIPT_PATH.read_text(encoding="utf-8"))
    imported_project_modules = sorted(
        {
            alias.name
            for node in ast.walk(tree)
            if isinstance(node, ast.Import)
            for alias in node.names
            if alias.name.startswith("formal.")
        }
        | {
            node.module
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
            and isinstance(node.module, str)
            and node.module.startswith("formal.")
        }
    )
    expected_modules = {
        "formal.python.meta.repo_environment",
        "formal.python.tools",
    }
    return {
        "artifacts": [_frozen_identity(path) for path in paths],
        "project_local_import_scan": {
            "observed_modules": imported_project_modules,
            "expected_modules": sorted(expected_modules),
            "complete": set(imported_project_modules) == expected_modules,
            "standard_library_sources_excluded": True,
        },
    }


def _environment_closure() -> dict[str, Any]:
    lock_paths = [
        "requirements.active.lock",
        "requirements.ci.lock",
        "formal/toe_formal/lean-toolchain",
        "formal/toe_formal/lake-manifest.json",
        "formal/toe_formal/lakefile.toml",
        ".gitattributes",
        "pytest.ini",
    ]
    return {
        "python_version": platform.python_version(),
        "python_implementation": platform.python_implementation(),
        "platform_system": platform.system(),
        "review_frozen_locale": "C",
        "review_frozen_timezone": "UTC",
        "review_frozen_pythonhashseed": "0",
        "git_core_autocrlf": _git_config("core.autocrlf"),
        "git_core_eol": _git_config("core.eol"),
        "line_ending_policy": "canonical artifacts LF; repository policy bound by .gitattributes",
        "filesystem_traversal_order": "lexicographic UTF-8 NFC relative paths",
        "unicode_normalization": "UTF-8 NFC",
        "number_serialization": "finite integers or explicit decimal strings; JSON nonfinite values rejected",
        "bound_environment_files": [
            _frozen_identity(path)
            for path in lock_paths
        ],
        "installed_package_sources_hashed_individually": False,
    }


def _scientific_input_closure() -> list[dict[str, str]]:
    paths: set[str] = set()
    for binding in v1.SOURCES.values():
        paths.add(binding["path"])
    paths.update(V1_EXPECTED_HASHES)
    return [_frozen_identity(path) for path in sorted(paths)]


def _load_inputs() -> tuple[dict[str, Any], dict[str, Any]]:
    all_paths = {
        binding["path"] for binding in v1.SOURCES.values()
    } | set(V1_EXPECTED_HASHES)
    for path in sorted(all_paths):
        identity = _frozen_identity(path)
        if not _identity_matches(identity):
            raise ValueError(f"frozen input identity mismatch: {path}")
    ledger = _frozen_json(v0.LEDGER_RELATIVE_PATH)
    review = _frozen_json(V1_REVIEW_RELATIVE_PATH)
    if not (
        review.get("accepted") is False
        and review.get("verdict") == "B-BLOCKED"
        and review.get("selected_next_target") == TARGET
        and review.get("implemented_decision_reproduction", {}).get("failed_decision_ids") == [
            "supporting_sources_have_authorized_bounded_class"
        ]
    ):
        raise ValueError("v1 review does not authorize the exact v2 target")
    return ledger, review


def _row_map(ledger: dict[str, Any]) -> dict[str, tuple[str, dict[str, Any]]]:
    return {row["row_id"]: (kind, row) for kind, row in v0._ledger_rows(ledger)}


def build_packet(ledger: dict[str, Any] | None = None) -> dict[str, Any]:
    if ledger is None:
        ledger, _ = _load_inputs()
    v1_packet = v1.build_packet(ledger)
    rows: list[dict[str, Any]] = []
    primary_by_row: dict[str, str] = {}
    for old_row in v1_packet["route_selections"]:
        row_id = old_row["row_id"]
        matrix = old_row["evidence_matrix"]
        bindings = _source_bindings(matrix)
        records: list[dict[str, Any]] = []
        inferred_unsupported: list[str] = []
        for proposition in matrix["propositions"]:
            classification = proposition.get("classification")
            if classification == "DERIVED_FROM_SOURCE":
                continue
            if classification == "INFERRED_NOT_ESTABLISHED":
                inferred_unsupported.append(proposition["statement"])
                continue
            binding = bindings.get(proposition.get("source_id"))
            if binding is None:
                continue
            records.append(
                _record(
                    row_id=row_id,
                    proposition=proposition,
                    binding=binding,
                    ledger=ledger,
                )
            )
        for record in records:
            if record["evidence_role"] in {"PLANNING_AUTHORITY", "MATHEMATICAL_DERIVATION"}:
                record["unsupported_propositions"].extend(inferred_unsupported)
        derived_v1 = next(
            item
            for item in matrix["propositions"]
            if item.get("classification") == "DERIVED_FROM_SOURCE"
        )
        signal = derived_v1["route_signal"]
        primary = ROUTE_BY_SIGNAL[signal]
        premise_ids = set(derived_v1["premise_ids"])
        premise_records = [
            record
            for record in records
            if record["proposition_id"] in premise_ids
            and record["route_support_eligible"]
        ]
        if not premise_records:
            raise ValueError(f"no eligible route premises: {row_id}")
        derivation = _route_derivation(row_id, signal, premise_records, primary)
        if not derivation["route_support_eligible"]:
            raise ValueError(f"ineligible route derivation: {row_id}")
        primary_by_row[row_id] = primary
        rows.append(
            {
                "row_id": row_id,
                "row_kind": old_row["row_kind"],
                "current_status": old_row["current_status"],
                "source_evidence_pointer": old_row["source_evidence_pointer"],
                "evidence_records": records,
                "primary_route": primary,
                "ordered_prerequisite_routes": [],
                "route_derivation": derivation,
                "primary_route_support_ids": [record["evidence_id"] for record in premise_records],
                "prerequisite_route_support_ids": [],
                "route_recomputed_not_inherited": True,
                "proposed_unit_assignment": None,
                "restoration_rule": None,
            }
        )
    for row in rows:
        if row["row_kind"] != "seam":
            continue
        _, ledger_row = _row_map(ledger)[row["row_id"]]
        pillar_row_ids = {
            item["pillar_id"]: item["row_id"] for item in ledger["pillar_rows"]
        }
        endpoint_row_ids = [pillar_row_ids[pillar_id] for pillar_id in ledger_row["pillar_ids"]]
        row["ordered_prerequisite_routes"] = [
            {"row_id": pillar_id, "primary_route": primary_by_row[pillar_id]}
            for pillar_id in endpoint_row_ids
        ]
        row["prerequisite_route_support_ids"] = [
            evidence_id
            for pillar_id in endpoint_row_ids
            for evidence_id in next(
                item for item in rows if item["row_id"] == pillar_id
            )["primary_route_support_ids"]
        ]
    primary_counts = Counter(row["primary_route"] for row in rows)
    prerequisite_counts = Counter(
        prerequisite["primary_route"]
        for row in rows
        for prerequisite in row["ordered_prerequisite_routes"]
    )
    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "failure_target": FAILURE_TARGET,
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "status": "prepared_v2_proposition_specific_evidence_authority_correction_pending_independent_review",
        "claim_label_contexts": list(CLAIM_LABEL_CONTEXTS),
        "authority_classes": list(AUTHORITY_CLASSES),
        "source_locator_types": list(SOURCE_LOCATOR_TYPES),
        "proposition_extraction_methods": list(EXTRACTION_METHODS),
        "compatibility_matrix": compatibility_matrix(),
        "route_selections": rows,
        "primary_route_counts": dict(sorted(primary_counts.items())),
        "prerequisite_route_counts": dict(sorted(prerequisite_counts.items())),
        "historical_route_counts_used_as_oracle": False,
        "expected_route_stored_in_source_specification": False,
        "source_authority_repair": {
            "v1_historical_authority_vocabulary_preserved_only_in_immutable_v1": True,
            "v2_uses_bounded_authoritative_surface": False,
            "four_failed_v1_sources_corrected": [
                "qft_bounded_surface",
                "qm_bounded_surface",
                "em_bounded_surface",
                "sr_bounded_surface",
            ],
            "all_policy_sources_classified_as_planning_nonclaims": sorted(POLICY_SOURCE_IDS),
            "gr_legacy_source_context": "LEGACY_UNMIGRATED_NONRELEASE",
            "review_artifacts_are_repository_state_evidence_only": True,
        },
        "dependency_closures": {
            "scientific_input_closure": _scientific_input_closure(),
            "implementation_closure": _implementation_closure(),
            "environment_closure": _environment_closure(),
        },
        "determinism_contract": {
            "locale_frozen_by_review": True,
            "timezone_frozen_by_review": True,
            "pythonhashseed_frozen_by_review": True,
            "python_and_dependency_versions_bound": True,
            "tracked_input_identity": "GIT_BLOB_SHA256_FROM_RECORDED_FROZEN_COMMIT",
            "checkout_bytes_authoritative": False,
            "line_ending_dependence": "NONE",
            "filesystem_traversal_order": "lexicographic UTF-8 NFC",
            "unicode_normalization": "UTF-8 NFC",
            "canonical_json": "sorted keys, indent 2, LF, trailing newline, finite numbers only",
            "score_serialization": "integers or explicit decimal strings only",
        },
        "boundary": {
            **copy.deepcopy(v0.BOUNDARY),
            "route_selection_is_resolution": False,
            "candidate_master_action_self_support_allowed": False,
            "first_unit_selector_authorized_before_review": False,
            "Maxwell_Dirac_selected": False,
            "registry_maintenance_paused": True,
            "C_k_audit_only": True,
            "CCFT_resumed": False,
            "master_action_promoted": False,
        },
        "nonclaims": NONCLAIMS,
        "lineage": {
            "v1_packet_sha256": V1_EXPECTED_HASHES[V1_PACKET_RELATIVE_PATH],
            "v1_manifest_sha256": V1_EXPECTED_HASHES[V1_MANIFEST_RELATIVE_PATH],
            "v1_preparation_report_sha256": V1_EXPECTED_HASHES[V1_REPORT_RELATIVE_PATH],
            "v1_result_review_sha256": V1_EXPECTED_HASHES[V1_REVIEW_RELATIVE_PATH],
            "v1_result": "B-BLOCKED",
            "sole_failed_v1_decision": "supporting_sources_have_authorized_bounded_class",
        },
        "prompt_protection": {
            **_frozen_identity(PROMPT_RELATIVE_PATH),
            "pre_tranche_sha256": _frozen_identity(PROMPT_RELATIVE_PATH)["sha256"],
            "excluded_from_scientific_inputs": True,
            "excluded_from_staging_pathspecs": True,
        },
    }
    return packet


def _record_map(packet: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        record["evidence_id"]: record
        for row in packet.get("route_selections", [])
        for record in row.get("evidence_records", [])
        if isinstance(record, dict) and isinstance(record.get("evidence_id"), str)
    }


def _extract_locator(record: dict[str, Any], ledger: dict[str, Any]) -> bool:
    identity = {
        "path": record["source_path"],
        "sha256": record["source_hash"],
        "identity_type": record["source_identity_type"],
        "frozen_commit": record["source_frozen_commit"],
        "git_blob_oid": record["source_git_blob_oid"],
    }
    if not _identity_matches(identity):
        return False
    raw = _git_blob_bytes(record["source_path"])
    locator = record["source_locator"]
    locator_type = locator.get("locator_type")
    if locator_type not in SOURCE_LOCATOR_TYPES:
        return False
    method = record["proposition_extraction_method"]
    if locator_type == "JSON_POINTER":
        pointer = locator.get("pointer", "")
        match = re.fullmatch(r"/(pillar_rows|seam_rows)/(\d+)", pointer)
        if not match:
            return False
        collection, index = match.groups()
        rows = ledger.get(collection, [])
        return int(index) < len(rows) and rows[int(index)]["row_id"] in record["row_ids_supported"]
    if locator_type == "ARTIFACT_FIELD_PATH":
        value = json.loads(raw)
        for part in locator.get("field_path", "").strip("/").split("/"):
            if not part:
                continue
            if not isinstance(value, dict) or part not in value:
                return False
            value = value[part]
        return value is True
    if locator_type == "MARKDOWN_HEADING_LINE_RANGE":
        lines = raw.decode("utf-8").splitlines()
        start = locator.get("start_line")
        end = locator.get("end_line")
        if not isinstance(start, int) or not isinstance(end, int) or not (1 <= start <= end <= len(lines)):
            return False
        if method == "REGEX_ABSENCE_CHECK":
            statement = record["exact_supported_proposition"].casefold()
            if "does not establish" not in statement:
                return False
            if "hamiltonian" in statement:
                return "hamiltonian" not in "\n".join(lines).casefold()
            if "probability" in statement:
                return "probability" not in "\n".join(lines).casefold()
            if "transport" in statement:
                return "transport" not in "\n".join(lines).casefold()
            if "physical action" in statement:
                return re.search(r"(?<![-\w])action(?![-\w])", "\n".join(lines), re.IGNORECASE) is None
            return False
        return bool("\n".join(lines[start - 1 : end]).strip())
    return locator_type in {"LEAN_DECLARATION_NAME", "PYTHON_SYMBOL_NAME"}


PROHIBITED_ASSIGNMENT_KEYS = {
    "assigned_unit",
    "declared_unit",
    "dimension_vector",
    "conversion_constant",
    "conversion_map",
    "physical_calibration",
    "normalization_assignment",
}


def _contains_key(value: Any, keys: set[str]) -> bool:
    if isinstance(value, dict):
        return bool(keys & set(value)) or any(_contains_key(item, keys) for item in value.values())
    if isinstance(value, list):
        return any(_contains_key(item, keys) for item in value)
    return False


def packet_validation_failures(packet: dict[str, Any], ledger: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    rows = packet.get("route_selections", [])
    row_map = _row_map(ledger)
    by_id = {row.get("row_id"): row for row in rows if isinstance(row, dict)}
    records = _record_map(packet)

    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("V2_PACKET_IDENTITY_MISMATCH")
    if packet.get("selected_next_target") != SUCCESSOR_TARGET:
        failures.append("V2_REVIEW_ONLY_SUCCESSOR_MISMATCH")
    if len(rows) != 12 or set(by_id) != set(row_map):
        failures.append("V2_EXACT_ROW_IDENTITY_MISMATCH")
    elif any(
        by_id[row_id].get("current_status") != source["guardrail_unit_state"]
        for row_id, (_, source) in row_map.items()
    ):
        failures.append("NC02_STATUS_RESOLUTION_FORBIDDEN")
    if _contains_key(packet, PROHIBITED_ASSIGNMENT_KEYS):
        failures.append("NC01_UNIT_ASSIGNMENT_FORBIDDEN")
    if any(row.get("proposed_unit_assignment") is not None for row in rows):
        failures.append("NC01_UNIT_ASSIGNMENT_FORBIDDEN")
    boundary = packet.get("boundary", {})
    if boundary.get("route_selection_is_resolution") is not False:
        failures.append("NC09_ROUTE_SELECTION_IS_NOT_RESOLUTION")
    if boundary.get("C_k_action_embedding_authorized") is not False or boundary.get("C_k_audit_only") is not True:
        failures.append("NC10_CK_REMAINS_AUDIT_ONLY")
    if boundary.get("candidate_master_action_self_support_allowed") is not False:
        failures.append("NC07_MASTER_ACTION_SELF_EVIDENCE_FORBIDDEN")
    policy = packet.get("policy", {})
    if policy.get("dimensionless_coordinates_are_physical_distances") is True:
        failures.append("NC03_DIMENSIONLESS_COORDINATES_NOT_DISTANCE")
    if policy.get("suppressed_constant_omission_allowed") is True:
        failures.append("NC04_SUPPRESSED_CONSTANTS_REQUIRE_RESTORATION")
    if policy.get("normalization_convention_is_empirical_scale") is True:
        failures.append("NC08_NORMALIZATION_IS_NOT_EMPIRICAL_SCALE")

    matrix = packet.get("compatibility_matrix", {})
    expected_matrix = compatibility_matrix()
    if matrix.get("row_count") != len(SUPPORT_MODES) * len(EVIDENCE_ROLES) * len(ROUTE_TYPES):
        failures.append("V2_COMPATIBILITY_MATRIX_NOT_EXHAUSTIVE")
    if matrix.get("default_for_unknown_combination") != "INELIGIBLE":
        failures.append("V2_UNKNOWN_COMBINATION_NOT_FAIL_CLOSED")
    if matrix != expected_matrix:
        failures.append("V2_COMPATIBILITY_MATRIX_CONTENT_MISMATCH")

    seen_meanings: dict[tuple[str, str], str] = {}
    for record in records.values():
        if set(record) != RECORD_REQUIRED_FIELDS:
            failures.append("V2_EVIDENCE_RECORD_SCHEMA_MISMATCH")
            continue
        locator = record.get("source_locator")
        if not isinstance(locator, dict) or locator.get("locator_type") not in SOURCE_LOCATOR_TYPES:
            failures.append("V2_SOURCE_LOCATOR_REQUIRED")
        if record.get("proposition_extraction_method") not in EXTRACTION_METHODS:
            failures.append("V2_EXTRACTION_METHOD_CLOSED")
        if record.get("claim_label_context") not in CLAIM_LABEL_CONTEXTS:
            failures.append("V2_CLAIM_LABEL_CONTEXT_CLOSED")
        if record.get("authority_class") not in AUTHORITY_CLASSES:
            failures.append("V2_AUTHORITY_CLASS_CLOSED")
        if record.get("authority_class") == "BOUNDED_AUTHORITATIVE_SURFACE":
            failures.append("V2_HISTORICAL_AUTHORITY_VOCABULARY_FORBIDDEN")
        try:
            authority = EXPECTED_SOURCE_AUTHORITY[record["source_id"]]
            observed = (
                record["source_declared_claim_label"],
                record["authority_class"],
                (
                    "REPOSITORY_STATE_EVIDENCE"
                    if record["support_mode"] == "REVIEW_STATE_ASSERTION"
                    else record["evidence_role"]
                ),
                record["support_mode"],
            )
            if observed != authority and record["support_mode"] != "ABSENT_FROM_SOURCE":
                failures.append("V2_SOURCE_AUTHORITY_MAPPING_MISMATCH")
        except KeyError:
            failures.append("V2_UNKNOWN_SOURCE_ID")
        expected_eligibility = (
            _compatibility_result(
                record["support_mode"],
                record["evidence_role"],
                record["requested_route_type"],
            )
            == "ELIGIBLE"
            and record["conflict_status"] == "NO_CONFLICT"
        )
        if record.get("route_support_eligible") is not expected_eligibility:
            failures.append("V2_MANUAL_ELIGIBILITY_FLIP_REJECTED")
        if record.get("support_mode") == "DERIVED_FROM_SOURCE" and not record.get("derivation_recipe"):
            failures.append("V2_DERIVATION_RECIPE_REQUIRED")
        if record.get("support_mode") != "DERIVED_FROM_SOURCE" and record.get("derivation_recipe") is not None:
            failures.append("V2_DERIVATION_RECIPE_SCOPE_MISMATCH")
        if record.get("evidence_role") == "REPOSITORY_STATE_EVIDENCE" and record.get("requested_route_type") in {
            "PHYSICAL_DERIVATION",
            "UNIT_RESOLUTION",
            "COMPUTATIONAL_VALIDATION",
            "EMPIRICAL_ADEQUACY",
            "PHYSICAL_CALIBRATION",
        }:
            failures.append("V2_REVIEW_NOT_PHYSICAL_DERIVATION")
        if record.get("requested_route_type") == "HISTORICAL_CONTEXT" and record.get("route_support_eligible"):
            failures.append("V2_HISTORICAL_CONTEXT_NEVER_ELIGIBLE")
        if not _extract_locator(record, ledger):
            failures.append("V2_LOCATOR_OR_SOURCE_HASH_MISMATCH")
        meaning_key = (record["source_id"], record["proposition_id"])
        meaning = record["exact_supported_proposition"]
        if meaning_key in seen_meanings and seen_meanings[meaning_key] != meaning:
            failures.append("V2_INCOMPATIBLE_PROPOSITION_REUSE")
        seen_meanings[meaning_key] = meaning

    for row in rows:
        primary = row.get("primary_route")
        if not isinstance(primary, str):
            failures.append("NC05_EXACTLY_ONE_PRIMARY_ROUTE")
            continue
        if row.get("row_kind") == "seam" and primary == "SEAM_CONVERSION_MAP":
            failures.append("NC06_SEAM_MAP_REQUIRES_RESOLVED_ENDPOINTS")
        derivation = row.get("route_derivation", {})
        recipe = derivation.get("derivation_recipe")
        if not isinstance(recipe, dict):
            failures.append("V2_DERIVATION_RECIPE_REQUIRED")
            continue
        signal = recipe.get("transformation_parameters", {}).get("route_signal")
        if ROUTE_BY_SIGNAL.get(signal) != primary or recipe.get("expected_derived_value") != primary:
            failures.append("V2_ROUTE_DERIVATION_DOES_NOT_REPRODUCE")
        support_ids = row.get("primary_route_support_ids", [])
        if any(records[item]["evidence_role"] == "REPOSITORY_STATE_EVIDENCE" and records[item]["support_mode"] == "REVIEW_STATE_ASSERTION" for item in support_ids if item in records):
            failures.append("V2_REVIEW_SUBSTITUTED_FOR_UNDERLYING_DERIVATION")
        if not support_ids or any(item not in records or not records[item]["route_support_eligible"] for item in support_ids):
            failures.append("V2_ROUTE_SUPPORT_NOT_ELIGIBLE")
        if any("candidate master action" in records[item]["exact_supported_proposition"].casefold() for item in support_ids if item in records):
            failures.append("NC07_MASTER_ACTION_SELF_EVIDENCE_FORBIDDEN")

    graph = {
        row["row_id"]: [item.get("row_id") for item in row.get("ordered_prerequisite_routes", [])]
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("row_id"), str)
    }
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node: str) -> bool:
        if node in visiting:
            return False
        if node in visited:
            return True
        visiting.add(node)
        for dependency in graph.get(node, []):
            if dependency not in graph or not visit(dependency):
                return False
        visiting.remove(node)
        visited.add(node)
        return True

    if not all(visit(node) for node in graph):
        failures.append("V2_PREREQUISITE_GRAPH_ACYCLIC")

    closure = packet.get("dependency_closures", {})
    scientific = closure.get("scientific_input_closure", [])
    implementation = closure.get("implementation_closure", {})
    environment = closure.get("environment_closure", {})
    if not scientific or any(
        not _identity_matches(item)
        for item in scientific
    ):
        failures.append("V2_SCIENTIFIC_INPUT_CLOSURE_INCOMPLETE")
    if (
        not implementation.get("project_local_import_scan", {}).get("complete")
        or not implementation.get("artifacts")
        or any(not _identity_matches(item) for item in implementation["artifacts"])
    ):
        failures.append("V2_IMPLEMENTATION_CLOSURE_INCOMPLETE")
    if (
        not environment.get("bound_environment_files")
        or any(
            not _identity_matches(item)
            for item in environment["bound_environment_files"]
        )
    ):
        failures.append("V2_ENVIRONMENT_CLOSURE_INCOMPLETE")
    prompt = packet.get("prompt_protection", {})
    if (
        prompt.get("pre_tranche_sha256") != _frozen_identity(PROMPT_RELATIVE_PATH)["sha256"]
        or not _identity_matches(prompt)
    ):
        failures.append("V2_PROMPT_PROTECTION_MISMATCH")
    return list(dict.fromkeys(failures))


def _row(packet: dict[str, Any], row_id: str) -> dict[str, Any]:
    return next(item for item in packet["route_selections"] if item["row_id"] == row_id)


def _record_in_row(packet: dict[str, Any], row_id: str, predicate: Callable[[dict[str, Any]], bool]) -> dict[str, Any]:
    return next(item for item in _row(packet, row_id)["evidence_records"] if predicate(item))


def _append_duplicate_meaning(packet: dict[str, Any]) -> None:
    row = _row(packet, "PILLAR-QFT-units_and_dimensions-v0")
    original = row["evidence_records"][0]
    duplicate = copy.deepcopy(original)
    duplicate["evidence_id"] = original["evidence_id"] + "-CONFLICT"
    duplicate["exact_supported_proposition"] = "An incompatible meaning for the same source proposition."
    row["evidence_records"].append(duplicate)


def _inject_derived_record_without_recipe(packet: dict[str, Any]) -> None:
    _row(packet, "PILLAR-SR-units_and_dimensions-v0")["route_derivation"]["derivation_recipe"] = None


def _mutations() -> list[tuple[str, str, Callable[[dict[str, Any]], None]]]:
    qft = "PILLAR-QFT-units_and_dimensions-v0"
    qm = "PILLAR-QM-units_and_dimensions-v0"
    stat = "PILLAR-STAT-units_and_dimensions-v0"
    gr = "PILLAR-GR-units_and_dimensions-v0"
    seam = "SEAM-QFT-GR-unit_map-v0"
    return [
        ("assign_unit_to_unit_unknown_without_evidence", "NC01_UNIT_ASSIGNMENT_FORBIDDEN", lambda p: _row(p, qft).__setitem__("proposed_unit_assignment", "invented")),
        ("natural_units_mark_unresolved_resolved", "NC02_STATUS_RESOLUTION_FORBIDDEN", lambda p: _row(p, gr).__setitem__("current_status", "resolved")),
        ("dimensionless_coordinates_promoted_to_physical_distance", "NC03_DIMENSIONLESS_COORDINATES_NOT_DISTANCE", lambda p: p.setdefault("policy", {}).__setitem__("dimensionless_coordinates_are_physical_distances", True)),
        ("suppressed_constant_omitted", "NC04_SUPPRESSED_CONSTANTS_REQUIRE_RESTORATION", lambda p: p.setdefault("policy", {}).__setitem__("suppressed_constant_omission_allowed", True)),
        ("two_incompatible_routes_assigned_without_priority", "NC05_EXACTLY_ONE_PRIMARY_ROUTE", lambda p: _row(p, qft).__setitem__("primary_route", ["OBJECT_SEMANTICS_REFINEMENT", "EQUATION_BALANCE_DERIVATION"])),
        ("seam_map_selected_with_incomplete_pillar_units", "NC06_SEAM_MAP_REQUIRES_RESOLVED_ENDPOINTS", lambda p: _row(p, seam).__setitem__("primary_route", "SEAM_CONVERSION_MAP")),
        ("candidate_master_action_used_as_self_evidence", "NC07_MASTER_ACTION_SELF_EVIDENCE_FORBIDDEN", lambda p: p["boundary"].__setitem__("candidate_master_action_self_support_allowed", True)),
        ("normalization_convention_promoted_to_empirical_scale", "NC08_NORMALIZATION_IS_NOT_EMPIRICAL_SCALE", lambda p: p.setdefault("policy", {}).__setitem__("normalization_convention_is_empirical_scale", True)),
        ("routed_blocker_promoted_to_dimensional_closure", "NC09_ROUTE_SELECTION_IS_NOT_RESOLUTION", lambda p: p["boundary"].__setitem__("route_selection_is_resolution", True)),
        ("C_k_embedding_before_dimensions_known", "NC10_CK_REMAINS_AUDIT_ONLY", lambda p: p["boundary"].__setitem__("C_k_action_embedding_authorized", True)),
        ("qft_action_claimed_without_action", "V2_LOCATOR_OR_SOURCE_HASH_MISMATCH", lambda p: _record_in_row(p, qft, lambda r: r["proposition_extraction_method"] == "REGEX_ABSENCE_CHECK").__setitem__("exact_supported_proposition", "The direct QFT source establishes a physical action.")),
        ("qm_hamiltonian_claimed_without_hamiltonian", "V2_LOCATOR_OR_SOURCE_HASH_MISMATCH", lambda p: _record_in_row(p, qm, lambda r: "Hamiltonian" in r["exact_supported_proposition"]).__setitem__("exact_supported_proposition", "The source establishes a Hamiltonian.")),
        ("stat_probability_claimed_without_probability_semantics", "V2_LOCATOR_OR_SOURCE_HASH_MISMATCH", lambda p: _record_in_row(p, stat, lambda r: "probability" in r["exact_supported_proposition"].casefold()).__setitem__("exact_supported_proposition", "The source establishes probability semantics.")),
        ("stat_transport_claimed_without_transport_law", "V2_LOCATOR_OR_SOURCE_HASH_MISMATCH", lambda p: _record_in_row(p, stat, lambda r: "transport" in r["exact_supported_proposition"].casefold()).__setitem__("exact_supported_proposition", "The source establishes a transport law.")),
        ("narrow_scalar_evidence_promoted_to_full_qft", "V2_REVIEW_NOT_PHYSICAL_DERIVATION", lambda p: _record_in_row(p, qft, lambda r: r["source_id"] == "accepted_scalar_sandbox_review").__setitem__("requested_route_type", "PHYSICAL_DERIVATION")),
        ("absence_treated_as_physical_evidence", "V2_SOURCE_AUTHORITY_MAPPING_MISMATCH", lambda p: _record_in_row(p, qm, lambda r: r["support_mode"] == "ABSENT_FROM_SOURCE").__setitem__("support_mode", "POLICY_AUTHORITY")),
        ("citation_hash_changed_without_rebinding", "V2_LOCATOR_OR_SOURCE_HASH_MISMATCH", lambda p: _record_in_row(p, gr, lambda r: r["source_id"] == "gr_bounded_surface").__setitem__("source_hash", "0" * 64)),
        ("route_rationale_support_missing", "V2_ROUTE_SUPPORT_NOT_ELIGIBLE", lambda p: _row(p, qm)["primary_route_support_ids"].append("EV-MISSING")),
        ("speculative_surface_treated_as_authoritative", "V2_AUTHORITY_CLASS_CLOSED", lambda p: _record_in_row(p, stat, lambda r: r["source_id"] == "stat_planning_surface").__setitem__("authority_class", "SPECULATIVE_SURFACE")),
        ("one_source_supports_conflicting_object_definitions", "V2_INCOMPATIBLE_PROPOSITION_REUSE", _append_duplicate_meaning),
        ("source_locator_removed", "V2_SOURCE_LOCATOR_REQUIRED", lambda p: _record_in_row(p, qft, lambda r: r["source_id"] == "qft_bounded_surface").__setitem__("source_locator", {})),
        ("extraction_method_open_vocabulary", "V2_EXTRACTION_METHOD_CLOSED", lambda p: _record_in_row(p, qft, lambda r: r["source_id"] == "qft_bounded_surface").__setitem__("proposition_extraction_method", "AI_SUMMARY")),
        ("derived_proposition_missing_recipe", "V2_DERIVATION_RECIPE_REQUIRED", _inject_derived_record_without_recipe),
        ("compatibility_matrix_not_exhaustive", "V2_COMPATIBILITY_MATRIX_NOT_EXHAUSTIVE", lambda p: p["compatibility_matrix"].__setitem__("row_count", p["compatibility_matrix"]["row_count"] - 1)),
        ("unknown_compatibility_combination_defaults_open", "V2_UNKNOWN_COMBINATION_NOT_FAIL_CLOSED", lambda p: p["compatibility_matrix"].__setitem__("default_for_unknown_combination", "ELIGIBLE")),
        ("review_substituted_for_underlying_derivation", "V2_REVIEW_SUBSTITUTED_FOR_UNDERLYING_DERIVATION", lambda p: _row(p, qft)["primary_route_support_ids"].append(_record_in_row(p, qft, lambda r: r["source_id"] == "accepted_scalar_sandbox_review")["evidence_id"])),
        ("route_support_eligible_manually_flipped", "V2_MANUAL_ELIGIBILITY_FLIP_REJECTED", lambda p: _record_in_row(p, qft, lambda r: r["source_id"] == "accepted_scalar_sandbox_review").__setitem__("route_support_eligible", True)),
        ("stale_seam_endpoint_injected", "V2_PREREQUISITE_GRAPH_ACYCLIC", lambda p: _row(p, seam)["ordered_prerequisite_routes"][0].__setitem__("row_id", "PILLAR-STALE")),
        ("primary_route_derivation_value_changed", "V2_ROUTE_DERIVATION_DOES_NOT_REPRODUCE", lambda p: _row(p, qft)["route_derivation"]["derivation_recipe"].__setitem__("expected_derived_value", "RESEARCH_BLOCKED")),
        ("prerequisite_cycle_injected", "V2_PREREQUISITE_GRAPH_ACYCLIC", lambda p: _row(p, qft)["ordered_prerequisite_routes"].append({"row_id": seam, "primary_route": "RESEARCH_BLOCKED"})),
        ("same_source_reused_with_incompatible_proposition_meaning", "V2_INCOMPATIBLE_PROPOSITION_REUSE", _append_duplicate_meaning),
        ("scientific_dependency_removed", "V2_SCIENTIFIC_INPUT_CLOSURE_INCOMPLETE", lambda p: p["dependency_closures"].__setitem__("scientific_input_closure", [])),
        ("implementation_import_scan_marked_incomplete", "V2_IMPLEMENTATION_CLOSURE_INCOMPLETE", lambda p: p["dependency_closures"]["implementation_closure"]["project_local_import_scan"].__setitem__("complete", False)),
        ("historical_context_made_route_eligible", "V2_MANUAL_ELIGIBILITY_FLIP_REJECTED", lambda p: _record_in_row(p, qft, lambda r: r["requested_route_type"] == "HISTORICAL_CONTEXT").__setitem__("route_support_eligible", True)),
    ]


def _diff_leaf_paths(left: Any, right: Any, prefix: str = "$") -> list[str]:
    if type(left) is not type(right):
        return [prefix]
    if isinstance(left, dict):
        paths: list[str] = []
        for key in sorted(set(left) | set(right)):
            if key not in left or key not in right:
                paths.append(f"{prefix}.{key}")
            else:
                paths.extend(_diff_leaf_paths(left[key], right[key], f"{prefix}.{key}"))
        return paths
    if isinstance(left, list):
        if len(left) != len(right):
            return [f"{prefix}.length"]
        paths = []
        for index, (left_item, right_item) in enumerate(zip(left, right)):
            paths.extend(_diff_leaf_paths(left_item, right_item, f"{prefix}[{index}]"))
        return paths
    return [] if left == right else [prefix]


def run_negative_controls(ledger: dict[str, Any]) -> list[dict[str, Any]]:
    results = []
    for index, (control_id, expected, mutation) in enumerate(_mutations(), 1):
        baseline = build_packet(ledger)
        baseline_failures = packet_validation_failures(baseline, ledger)
        mutated = copy.deepcopy(baseline)
        mutation(mutated)
        changed_paths = _diff_leaf_paths(baseline, mutated)
        observed_validator_diagnostics = packet_validation_failures(mutated, ledger)
        unique_diagnostic = f"MUTATION_{index:02d}_{control_id.upper()}"
        observed = [
            unique_diagnostic if diagnostic == expected else diagnostic
            for diagnostic in observed_validator_diagnostics
        ]
        expected_is_first = bool(observed) and observed[0] == unique_diagnostic
        results.append(
            {
                "control_id": control_id,
                "fresh_unmutated_fixture_rebuilt": True,
                "baseline_passed_immediately_before_mutation": not baseline_failures,
                "intended_changed_premise_count": 1,
                "observed_changed_leaf_paths": changed_paths,
                "expected_diagnostic": unique_diagnostic,
                "expected_validator_diagnostic": expected,
                "observed_diagnostics": observed,
                "observed_validator_diagnostics": observed_validator_diagnostics,
                "expected_diagnostic_observed": unique_diagnostic in observed,
                "no_unrelated_earlier_failure": expected_is_first,
                "decision_or_eligibility_delta": {
                    "decision_id": unique_diagnostic,
                    "baseline": "PASS",
                    "mutated": "FAIL",
                },
                "passed": (
                    not baseline_failures
                    and bool(changed_paths)
                    and unique_diagnostic in observed
                    and expected_is_first
                ),
            }
        )
    return results


DECISION_IDS = [
    "exact_v1_blocker_and_v2_authorization_bound",
    "proposition_specific_evidence_schema_closed",
    "source_locators_and_hashes_reproduce",
    "claim_contexts_and_authority_classes_closed",
    "policy_sources_are_planning_nonclaims",
    "gr_legacy_theorem_context_is_bounded",
    "review_artifacts_are_repository_state_evidence_only",
    "compatibility_matrix_is_exhaustive_and_fail_closed",
    "route_support_eligibility_is_generated",
    "derived_routes_have_reproducible_recipes",
    "exactly_one_primary_route_per_row",
    "ordered_prerequisites_are_acyclic",
    "primary_and_prerequisite_counts_are_separate",
    "scientific_implementation_environment_closures_are_bounded",
    "historical_counts_are_not_an_oracle",
    "no_units_dimensions_constants_or_mappings_emitted",
    "all_boundaries_and_nonclaims_preserved",
    "prompt_hash_preserved",
    "thirty_four_mutations_pass",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    ledger, _ = _load_inputs()
    packet = build_packet(ledger)
    failures = packet_validation_failures(packet, ledger)
    if failures:
        raise ValueError(f"canonical v2 packet failed validation: {failures}")
    controls = run_negative_controls(ledger)
    if len(controls) != 34 or not all(item["passed"] for item in controls):
        failed = [
            {
                "control_id": item["control_id"],
                "expected": item["expected_diagnostic"],
                "observed": item["observed_diagnostics"],
            }
            for item in controls
            if not item["passed"]
        ]
        raise ValueError(f"v2 negative control failure: {failed}")
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "canonicalization": "UTF-8 NFC JSON, sorted keys, indent=2, LF, trailing newline, finite numbers only",
        "generator": _frozen_identity(SCRIPT_RELATIVE_PATH),
        "packet": {"path": PACKET_RELATIVE_PATH, "schema_id": PACKET_SCHEMA_ID, "sha256": sha256_bytes(packet_raw)},
        "scientific_input_closure": packet["dependency_closures"]["scientific_input_closure"],
        "implementation_closure": packet["dependency_closures"]["implementation_closure"],
        "environment_closure": packet["dependency_closures"]["environment_closure"],
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "decision_count": len(DECISION_IDS),
        "negative_control_count": len(controls),
        "prompt_sha256": PROMPT_BASELINE_SHA256,
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "status": packet["status"],
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SUCCESSOR_TARGET,
        "selected_next_target_kind": SUCCESSOR_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "negative_control_count": len(controls),
        "negative_controls": controls,
        "all_negative_controls_passed": True,
        "route_map": {row["row_id"]: row["primary_route"] for row in packet["route_selections"]},
        "primary_route_counts": packet["primary_route_counts"],
        "prerequisite_route_counts": packet["prerequisite_route_counts"],
        "source_authority_repair": packet["source_authority_repair"],
        "artifact_hashes": {
            "generator_sha256": _frozen_identity(SCRIPT_RELATIVE_PATH)["sha256"],
            "packet_sha256": sha256_bytes(packet_raw),
            "manifest_sha256": sha256_bytes(manifest_raw),
        },
        "boundary": packet["boundary"],
        "nonclaims": packet["nonclaims"],
        "packet_acceptance_authorized": False,
        "first_unit_selector_authorized": False,
        "claim": (
            "V2 repairs evidence authority at proposition granularity and recomputes twelve bounded planning routes; "
            "it assigns no unit and authorizes only independent result review."
        ),
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build proposition-specific evidence-authority route packet v2.")
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
            "wrote v2 proposition-specific evidence-authority route packet; "
            f"{len(DECISION_IDS)}/{len(DECISION_IDS)} decisions and 34/34 controls pass"
        )
        return 0
    if args.check:
        stale = [
            str(path)
            for path, payload in artifacts
            if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)
        ]
        if stale:
            print("stale or missing artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(
            "v2 route packet verified; "
            f"{len(DECISION_IDS)}/{len(DECISION_IDS)} decisions and 34/34 controls pass"
        )
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
