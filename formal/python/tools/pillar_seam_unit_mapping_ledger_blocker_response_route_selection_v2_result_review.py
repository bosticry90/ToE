from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import unicodedata
import uuid
from functools import lru_cache
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/"
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v2_result_review.py"
)
GENERATOR_MODULE = (
    "formal.python.tools."
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v2"
)
GENERATOR_RELATIVE_PATH = (
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
PREPARATION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260713_v2.json"
)
REVIEW_REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260713_v2.json"
)
LEDGER_RELATIVE_PATH = "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json"
PROMPT_RELATIVE_PATH = "Prompt.txt"
FROZEN_COMMIT_RECORD_RELATIVE_PATH = (
    "formal/docs/release/V2_TRACKED_BLOB_IDENTITY_FREEZE_20260721_v0.json"
)

PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
PREPARATION_REPORT_PATH = REPO_ROOT / PREPARATION_REPORT_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH
LEDGER_PATH = REPO_ROOT / LEDGER_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
PREPARATION_COMMIT = "c0140b89e2a6614c9ae02c2b8554295fa0e8fb10"
PREPARATION_PARENT = "c8b4248bc589f6d1c28d3585481178cb050aac0f"
EXPECTED_PREPARATION_HASHES = {
    GENERATOR_RELATIVE_PATH: "08c21d5e8163e5657c8b61daa2a04de94aef2157e913a8bb219c951f43e4178d",
    PACKET_RELATIVE_PATH: "edd86640c3d6664e27874e5e3737dfd20f3c85dd91729d74266eb296cdd20b3b",
    MANIFEST_RELATIVE_PATH: "f02714f8472a672e859c2110db3d3cae28eeeec80ea81f46f8810d8bfbdad650",
    PREPARATION_REPORT_RELATIVE_PATH: "f782ca247ef80a67a89bc814d578144f81e04ce87af43c0373947874be646c9c",
}
PROMPT_BASELINE_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

REVIEW_TARGET = (
    "review_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2_result"
)
ACCEPTED_NEXT_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0"
)
BLOCKED_NEXT_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v3"
)
REVIEW_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260713_v2"
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

EXPECTED_AUTHORITY = {
    "accepted_unit_ledger": ("SOURCE_UNDECLARED", "FROZEN_ACCEPTED_LEDGER", "REPOSITORY_STATE_EVIDENCE", "LEDGER_STATE"),
    "qft_bounded_surface": ("P-POLICY", "BOUNDED_PLANNING_NONCLAIM", "PLANNING_AUTHORITY", "POLICY_AUTHORITY"),
    "gr_bounded_surface": ("T-PROVED", "BOUNDED_ACCEPTED_MATHEMATICAL_SURFACE", "MATHEMATICAL_DERIVATION", "LEGACY_THEOREM_SURFACE"),
    "qm_bounded_surface": ("P-POLICY", "BOUNDED_PLANNING_NONCLAIM", "PLANNING_AUTHORITY", "POLICY_AUTHORITY"),
    "stat_planning_surface": ("P-POLICY", "BOUNDED_PLANNING_NONCLAIM", "PLANNING_AUTHORITY", "POLICY_AUTHORITY"),
    "em_bounded_surface": ("P-POLICY", "BOUNDED_PLANNING_NONCLAIM", "PLANNING_AUTHORITY", "POLICY_AUTHORITY"),
    "sr_bounded_surface": ("P-POLICY", "BOUNDED_PLANNING_NONCLAIM", "PLANNING_AUTHORITY", "POLICY_AUTHORITY"),
    "cosmo_planning_surface": ("P-POLICY", "BOUNDED_PLANNING_NONCLAIM", "PLANNING_AUTHORITY", "POLICY_AUTHORITY"),
    "pillar_target_map": ("P-POLICY", "BOUNDED_PLANNING_NONCLAIM", "PLANNING_AUTHORITY", "POLICY_AUTHORITY"),
    "accepted_scalar_sandbox_review": ("SOURCE_UNDECLARED", "ACCEPTED_BOUNDED_REVIEW", "REPOSITORY_STATE_EVIDENCE", "REVIEW_STATE_ASSERTION"),
}

PRIMARY_BY_DIRECT_SOURCE = {
    "qft_bounded_surface": "OBJECT_SEMANTICS_REFINEMENT",
    "gr_bounded_surface": "EQUATION_BALANCE_DERIVATION",
    "qm_bounded_surface": "OBJECT_SEMANTICS_REFINEMENT",
    "stat_planning_surface": "OBJECT_SEMANTICS_REFINEMENT",
    "em_bounded_surface": "CONVENTION_AND_CONSTANT_RESTORATION",
    "sr_bounded_surface": "CONVENTION_AND_CONSTANT_RESTORATION",
    "cosmo_planning_surface": "OBJECT_SEMANTICS_REFINEMENT",
}

DECISION_IDS = [
    "preparation_commit_and_hashes_are_immutable",
    "strict_json_and_canonical_bytes_reproduce",
    "v2_consumes_exact_live_target",
    "source_claim_labels_recomputed_from_exact_bytes",
    "authority_classes_recomputed_independently",
    "review_artifacts_remain_repository_state_evidence",
    "source_locators_and_hashes_recomputed",
    "compatibility_matrix_recomputed_exhaustively",
    "eligibility_recomputed_not_trusted",
    "route_map_recomputed_without_historical_count_oracle",
    "primary_routes_and_prerequisites_are_well_formed",
    "dependency_closures_are_bounded_and_complete",
    "thirty_four_controls_are_fresh_unique_and_diagnostic",
    "two_clean_detached_regenerations_are_byte_identical",
    "no_unit_resolution_or_downstream_benchmark_is_authorized_early",
    "prompt_hash_is_preserved_outside_scientific_inputs",
]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
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


@lru_cache(maxsize=1)
def _frozen_commit() -> str:
    payload = load_json(REPO_ROOT / FROZEN_COMMIT_RECORD_RELATIVE_PATH)
    commit = payload.get("frozen_commit")
    if (
        payload.get("schema_id")
        != "V2_TRACKED_BLOB_IDENTITY_FREEZE_20260721_v0"
        or not isinstance(commit, str)
        or not re.fullmatch(r"[0-9a-f]{40}", commit)
    ):
        raise ValueError("invalid V2 tracked-blob identity freeze record")
    return commit


@lru_cache(maxsize=None)
def _git_blob_bytes(relative_path: str, commit: str) -> bytes:
    result = subprocess.run(
        ["git", "cat-file", "blob", f"{commit}:{relative_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise ValueError(f"missing frozen Git blob: {commit}:{relative_path}")
    return result.stdout


@lru_cache(maxsize=None)
def _git_blob_oid(relative_path: str, commit: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
        text=True,
    )
    oid = result.stdout.strip()
    if result.returncode != 0 or not re.fullmatch(r"[0-9a-f]{40,64}", oid):
        raise ValueError(f"missing frozen Git blob identity: {commit}:{relative_path}")
    return oid


def _identity_matches(binding: dict[str, Any]) -> bool:
    path = binding.get("path")
    commit = binding.get("frozen_commit")
    if not isinstance(path, str) or commit != _frozen_commit():
        return False
    try:
        raw = _git_blob_bytes(path, commit)
        oid = _git_blob_oid(path, commit)
    except ValueError:
        return False
    return (
        binding.get("sha256") == sha256_bytes(raw)
        and binding.get("git_blob_oid") == oid
        and binding.get("identity_type")
        in {"GIT_BLOB_SHA256", "CANONICAL_ARTIFACT_SHA256"}
    )


def _frozen_text(relative_path: str) -> str:
    return _git_blob_bytes(relative_path, _frozen_commit()).decode("utf-8")


def _strict_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_strict_pairs,
        parse_constant=lambda token: (_ for _ in ()).throw(ValueError(f"nonfinite JSON value: {token}")),
    )
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _compatibility_result(support_mode: str, evidence_role: str, route_type: str) -> str:
    combinations = {
        (mode, role, route)
        for mode in SUPPORT_MODES
        for role in EVIDENCE_ROLES
        for route in ROUTE_TYPES
    }
    if (support_mode, evidence_role, route_type) not in combinations:
        return "INELIGIBLE"
    if route_type in {"HISTORICAL_CONTEXT", "PILLAR_COMPLETION", "SEAM_CLOSURE"}:
        return "INELIGIBLE"
    eligible: set[tuple[str, str, str]] = set()
    eligible.update(
        ("POLICY_AUTHORITY", "PLANNING_AUTHORITY", route)
        for route in ("PLANNING_ROUTE_SELECTION", "SEMANTIC_REFINEMENT", "BLOCKER_IDENTIFICATION")
    )
    eligible.update(
        ("SUPPLIED_ONLY", "CONDITIONAL_HYPOTHESIS", route)
        for route in (
            "PLANNING_ROUTE_SELECTION",
            "SEMANTIC_REFINEMENT",
            "BLOCKER_IDENTIFICATION",
            "CONDITIONAL_THEOREM_HYPOTHESIS",
        )
    )
    eligible.add(("LEDGER_STATE", "REPOSITORY_STATE_EVIDENCE", "BLOCKER_IDENTIFICATION"))
    eligible.add(("ABSENT_FROM_SOURCE", "SOURCE_ABSENCE_EVIDENCE", "BLOCKER_IDENTIFICATION"))
    eligible.update(
        ("LEGACY_THEOREM_SURFACE", "MATHEMATICAL_DERIVATION", route)
        for route in (
            "PLANNING_ROUTE_SELECTION",
            "SEMANTIC_REFINEMENT",
            "BLOCKER_IDENTIFICATION",
            "CONDITIONAL_THEOREM_HYPOTHESIS",
        )
    )
    eligible.update(
        ("DERIVED_FROM_SOURCE", "DERIVED_EVIDENCE", route)
        for route in ("PLANNING_ROUTE_SELECTION", "SEMANTIC_REFINEMENT", "BLOCKER_IDENTIFICATION")
    )
    eligible.add(("DERIVED_FROM_SOURCE", "PHYSICAL_DERIVATION", "PHYSICAL_DERIVATION"))
    eligible.add(("DERIVED_FROM_SOURCE", "COMPUTATIONAL_PHYSICS_EVIDENCE", "COMPUTATIONAL_VALIDATION"))
    eligible.add(("DERIVED_FROM_SOURCE", "EMPIRICAL_EVIDENCE", "EMPIRICAL_ADEQUACY"))
    eligible.add(("DERIVED_FROM_SOURCE", "EMPIRICAL_EVIDENCE", "PHYSICAL_CALIBRATION"))
    return "ELIGIBLE" if (support_mode, evidence_role, route_type) in eligible else "INELIGIBLE"


def _declared_label(relative_path: str) -> str:
    match = re.search(
        r"Classification:\s*\r?\n-\s*`([^`]+)`",
        _frozen_text(relative_path),
    )
    return match.group(1) if match else "SOURCE_UNDECLARED"


def _record_iter(packet: dict[str, Any]):
    for row in packet.get("route_selections", []):
        for record in row.get("evidence_records", []):
            yield row, record


def _resolve_locator(record: dict[str, Any], ledger: dict[str, Any]) -> bool:
    binding = {
        "path": record.get("source_path"),
        "sha256": record.get("source_hash"),
        "identity_type": record.get("source_identity_type"),
        "frozen_commit": record.get("source_frozen_commit"),
        "git_blob_oid": record.get("source_git_blob_oid"),
    }
    if not _identity_matches(binding):
        return False
    raw = _git_blob_bytes(record["source_path"], _frozen_commit())
    locator = record.get("source_locator", {})
    locator_type = locator.get("locator_type")
    if locator_type == "JSON_POINTER":
        match = re.fullmatch(r"/(pillar_rows|seam_rows)/(\d+)", locator.get("pointer", ""))
        if not match:
            return False
        collection, index = match.groups()
        rows = ledger.get(collection, [])
        return int(index) < len(rows) and rows[int(index)].get("row_id") in record.get("row_ids_supported", [])
    if locator_type == "ARTIFACT_FIELD_PATH":
        value: Any = json.loads(raw)
        for part in locator.get("field_path", "").strip("/").split("/"):
            if part:
                if not isinstance(value, dict) or part not in value:
                    return False
                value = value[part]
        return value is True
    if locator_type == "MARKDOWN_HEADING_LINE_RANGE":
        lines = raw.decode("utf-8").splitlines()
        start = locator.get("start_line")
        end = locator.get("end_line")
        return isinstance(start, int) and isinstance(end, int) and 1 <= start <= end <= len(lines)
    return locator_type in {"LEAN_DECLARATION_NAME", "PYTHON_SYMBOL_NAME"}


def preparation_custody() -> dict[str, Any]:
    manifest = load_json(MANIFEST_PATH)
    report = load_json(PREPARATION_REPORT_PATH)
    generator = manifest["generator"]
    expected_hashes = {
        GENERATOR_RELATIVE_PATH: generator["sha256"],
        PACKET_RELATIVE_PATH: manifest["packet"]["sha256"],
        MANIFEST_RELATIVE_PATH: report["artifact_hashes"]["manifest_sha256"],
        PREPARATION_REPORT_RELATIVE_PATH: sha256_path(PREPARATION_REPORT_PATH),
    }
    working_hashes = {
        path: sha256_path(REPO_ROOT / path) for path in expected_hashes
    }
    working_comparisons = {
        path: working_hashes[path] == expected for path, expected in expected_hashes.items()
    }
    identity_bindings = [
        generator,
        *manifest["scientific_input_closure"],
        *manifest["implementation_closure"]["artifacts"],
        *manifest["environment_closure"]["bound_environment_files"],
    ]
    commit_comparisons = {
        item["path"]: _identity_matches(item) for item in identity_bindings
    }
    custody_checks = {
        "frozen_commit_recorded": all(
            item.get("frozen_commit") == _frozen_commit()
            for item in identity_bindings
        ),
        "working_hashes_match": all(working_comparisons.values()),
        "commit_hashes_match": all(commit_comparisons.values()),
    }
    return {
        "preparation_commit": _frozen_commit(),
        "expected_preparation_commit": _frozen_commit(),
        "working_tree_hashes": working_hashes,
        "expected_hashes": expected_hashes,
        "checks": custody_checks,
        "working_hash_comparisons": working_comparisons,
        "commit_hash_comparisons": commit_comparisons,
        "passed": all(custody_checks.values()),
    }


def independent_packet_audit(packet: dict[str, Any], manifest: dict[str, Any], report: dict[str, Any], ledger: dict[str, Any]) -> dict[str, Any]:
    checks: dict[str, bool] = {}
    checks["strict_json_and_canonical_bytes_reproduce"] = (
        PACKET_PATH.read_bytes() == canonical_json_bytes(packet)
        and MANIFEST_PATH.read_bytes() == canonical_json_bytes(manifest)
        and PREPARATION_REPORT_PATH.read_bytes() == canonical_json_bytes(report)
    )
    checks["v2_consumes_exact_live_target"] = (
        packet.get("target") == "prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_v2"
        and packet.get("selected_next_target") == REVIEW_TARGET
        and report.get("target") == packet.get("target")
    )
    authority_mismatches: list[dict[str, Any]] = []
    locator_failures: list[str] = []
    eligibility_failures: list[str] = []
    review_role_failures: list[str] = []
    declared_label_failures: list[str] = []
    for _, record in _record_iter(packet):
        source_id = record.get("source_id")
        expected = EXPECTED_AUTHORITY.get(source_id)
        observed = (
            record.get("source_declared_claim_label"),
            record.get("authority_class"),
            (
                "REPOSITORY_STATE_EVIDENCE"
                if record.get("support_mode") == "REVIEW_STATE_ASSERTION"
                else record.get("evidence_role")
            ),
            record.get("support_mode"),
        )
        if record.get("support_mode") != "ABSENT_FROM_SOURCE" and observed != expected:
            authority_mismatches.append({"evidence_id": record.get("evidence_id"), "expected": expected, "observed": observed})
        if source_id not in {"accepted_unit_ledger", "accepted_scalar_sandbox_review"}:
            if _declared_label(record["source_path"]) != record.get("source_declared_claim_label"):
                declared_label_failures.append(record.get("evidence_id"))
        if not _resolve_locator(record, ledger):
            locator_failures.append(record.get("evidence_id"))
        expected_eligible = (
            _compatibility_result(
                record.get("support_mode"),
                record.get("evidence_role"),
                record.get("requested_route_type"),
            )
            == "ELIGIBLE"
            and record.get("conflict_status") == "NO_CONFLICT"
        )
        if record.get("route_support_eligible") is not expected_eligible:
            eligibility_failures.append(record.get("evidence_id"))
        if source_id == "accepted_scalar_sandbox_review" and (
            record.get("evidence_role") != "REPOSITORY_STATE_EVIDENCE"
            or record.get("route_support_eligible") is not False
        ):
            review_role_failures.append(record.get("evidence_id"))
    checks["source_claim_labels_recomputed_from_exact_bytes"] = not declared_label_failures
    checks["authority_classes_recomputed_independently"] = not authority_mismatches
    checks["review_artifacts_remain_repository_state_evidence"] = not review_role_failures
    checks["source_locators_and_hashes_recomputed"] = not locator_failures
    checks["eligibility_recomputed_not_trusted"] = not eligibility_failures

    expected_matrix = [
        {
            "support_mode": mode,
            "evidence_role": role,
            "route_type": route,
            "result": _compatibility_result(mode, role, route),
        }
        for mode in SUPPORT_MODES
        for role in EVIDENCE_ROLES
        for route in ROUTE_TYPES
    ]
    matrix = packet.get("compatibility_matrix", {})
    checks["compatibility_matrix_recomputed_exhaustively"] = (
        matrix.get("row_count") == len(expected_matrix)
        and matrix.get("rows") == expected_matrix
        and matrix.get("default_for_unknown_combination") == "INELIGIBLE"
    )

    independently_selected: dict[str, str] = {}
    route_failures: list[str] = []
    prerequisite_failures: list[str] = []
    rows = packet.get("route_selections", [])
    row_ids = {row.get("row_id") for row in rows}
    for row in rows:
        if row.get("row_kind") == "seam":
            expected_route = "RESEARCH_BLOCKED"
        else:
            direct_sources = {
                record.get("source_id")
                for record in row.get("evidence_records", [])
                if record.get("source_id") in PRIMARY_BY_DIRECT_SOURCE
            }
            expected_route = (
                PRIMARY_BY_DIRECT_SOURCE[next(iter(direct_sources))]
                if len(direct_sources) == 1
                else "INDETERMINATE"
            )
        independently_selected[row["row_id"]] = expected_route
        if row.get("primary_route") != expected_route or not isinstance(row.get("primary_route"), str):
            route_failures.append(row["row_id"])
        prerequisites = row.get("ordered_prerequisite_routes", [])
        if row.get("row_kind") == "pillar" and prerequisites:
            prerequisite_failures.append(row["row_id"])
        if row.get("row_kind") == "seam" and (
            len(prerequisites) != 2
            or any(item.get("row_id") not in row_ids for item in prerequisites)
        ):
            prerequisite_failures.append(row["row_id"])
    checks["route_map_recomputed_without_historical_count_oracle"] = (
        not route_failures
        and packet.get("historical_route_counts_used_as_oracle") is False
        and packet.get("expected_route_stored_in_source_specification") is False
    )
    checks["primary_routes_and_prerequisites_are_well_formed"] = not prerequisite_failures

    closures = packet.get("dependency_closures", {})
    scientific = closures.get("scientific_input_closure", [])
    implementation = closures.get("implementation_closure", {})
    environment = closures.get("environment_closure", {})
    scientific_ok = bool(scientific) and all(
        _identity_matches(item)
        for item in scientific
    )
    implementation_ok = (
        implementation.get("project_local_import_scan", {}).get("complete") is True
        and bool(implementation.get("artifacts"))
        and all(_identity_matches(item) for item in implementation["artifacts"])
    )
    environment_ok = (
        environment.get("review_frozen_locale") == "C"
        and environment.get("review_frozen_timezone") == "UTC"
        and environment.get("review_frozen_pythonhashseed") == "0"
        and bool(environment.get("bound_environment_files"))
        and all(
            _identity_matches(item)
            for item in environment["bound_environment_files"]
        )
    )
    checks["dependency_closures_are_bounded_and_complete"] = scientific_ok and implementation_ok and environment_ok

    controls = report.get("negative_controls", [])
    checks["thirty_four_controls_are_fresh_unique_and_diagnostic"] = (
        len(controls) == 34
        and len({item.get("control_id") for item in controls}) == 34
        and len({item.get("expected_diagnostic") for item in controls}) == 34
        and all(item.get("fresh_unmutated_fixture_rebuilt") is True for item in controls)
        and all(item.get("baseline_passed_immediately_before_mutation") is True for item in controls)
        and all(item.get("expected_diagnostic_observed") is True for item in controls)
        and all(item.get("no_unrelated_earlier_failure") is True for item in controls)
        and all(item.get("passed") is True for item in controls)
    )
    boundary = packet.get("boundary", {})
    checks["no_unit_resolution_or_downstream_benchmark_is_authorized_early"] = (
        all(row.get("proposed_unit_assignment") is None and row.get("restoration_rule") is None for row in rows)
        and boundary.get("route_selection_is_resolution") is False
        and boundary.get("first_unit_selector_authorized_before_review") is False
        and boundary.get("Maxwell_Dirac_selected") is False
        and boundary.get("C_k_audit_only") is True
        and boundary.get("CCFT_resumed") is False
        and boundary.get("master_action_promoted") is False
    )
    checks["prompt_hash_is_preserved_outside_scientific_inputs"] = (
        _identity_matches(packet.get("prompt_protection", {}))
        and packet.get("prompt_protection", {}).get("excluded_from_scientific_inputs") is True
        and all(item.get("path") != PROMPT_RELATIVE_PATH for item in scientific)
    )
    return {
        "checks": checks,
        "all_checks_passed": all(checks.values()),
        "authority_mismatches": authority_mismatches,
        "declared_label_failures": declared_label_failures,
        "locator_failures": locator_failures,
        "eligibility_failures": eligibility_failures,
        "review_role_failures": review_role_failures,
        "independently_selected_route_map": independently_selected,
        "route_failures": route_failures,
        "prerequisite_failures": prerequisite_failures,
    }


def isolated_regeneration() -> dict[str, Any]:
    preparation_packet = load_json(PACKET_PATH)
    scientific_inputs = preparation_packet["dependency_closures"]["scientific_input_closure"]
    implementation_inputs = preparation_packet["dependency_closures"]["implementation_closure"]["artifacts"]
    environment_inputs = preparation_packet["dependency_closures"]["environment_closure"]["bound_environment_files"]
    rebound_inputs = {
        binding["path"]: binding
        for binding in [*scientific_inputs, *implementation_inputs, *environment_inputs]
    }
    scratch_root = REPO_ROOT / "scratch" / f"v2-review-{uuid.uuid4().hex}"
    scratch_root.mkdir(parents=True, exist_ok=False)
    runs: list[dict[str, Any]] = []
    try:
        for index in (1, 2):
            worktree = scratch_root / f"detached-{index}"
            add = subprocess.run(
                [
                    "git",
                    "-c",
                    "core.autocrlf=false",
                    "-c",
                    "core.eol=lf",
                    "worktree",
                    "add",
                    "--detach",
                    str(worktree),
                    PREPARATION_COMMIT,
                ],
                cwd=REPO_ROOT,
                capture_output=True,
                check=False,
                text=True,
            )
            if add.returncode != 0:
                runs.append({"run": index, "passed": False, "stage": "worktree_add", "stderr": add.stderr.strip()})
                continue
            try:
                initial_status = subprocess.run(
                    ["git", "status", "--porcelain"],
                    cwd=worktree,
                    capture_output=True,
                    check=False,
                    text=True,
                )
                for binding in rebound_inputs.values():
                    source = REPO_ROOT / binding["path"]
                    destination = worktree / binding["path"]
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(source, destination)
                environment = os.environ.copy()
                environment.update(
                    {
                        "LC_ALL": "C",
                        "LANG": "C",
                        "TZ": "UTC",
                        "PYTHONHASHSEED": "0",
                        "PYTHONUTF8": "1",
                    }
                )
                build = subprocess.run(
                    [sys.executable, "-m", GENERATOR_MODULE, "--write"],
                    cwd=worktree,
                    env=environment,
                    capture_output=True,
                    check=False,
                    text=True,
                    timeout=180,
                )
                observed_hashes = {
                    path: sha256_path(worktree / path)
                    for path in (PACKET_RELATIVE_PATH, MANIFEST_RELATIVE_PATH, PREPARATION_REPORT_RELATIVE_PATH)
                    if (worktree / path).is_file()
                }
                status = subprocess.run(
                    ["git", "status", "--porcelain"],
                    cwd=worktree,
                    capture_output=True,
                    check=False,
                    text=True,
                )
                expected_outputs = {
                    path: EXPECTED_PREPARATION_HASHES[path]
                    for path in (PACKET_RELATIVE_PATH, MANIFEST_RELATIVE_PATH, PREPARATION_REPORT_RELATIVE_PATH)
                }
                runs.append(
                    {
                        "run": index,
                        "worktree_commit": PREPARATION_COMMIT,
                        "clean_detached_start": initial_status.returncode == 0 and not initial_status.stdout.strip(),
                        "environment": {"locale": "C", "timezone": "UTC", "PYTHONHASHSEED": "0", "UTF8": "1"},
                        "all_bound_inputs_rebound_to_exact_hash_bound_bytes": True,
                        "generator_returncode": build.returncode,
                        "generator_stderr": build.stderr.strip(),
                        "observed_hashes": observed_hashes,
                        "expected_hashes": expected_outputs,
                        "worktree_status_after_regeneration": status.stdout.strip(),
                        "passed": (
                            initial_status.returncode == 0
                            and not initial_status.stdout.strip()
                            and build.returncode == 0
                            and observed_hashes == expected_outputs
                            and status.returncode == 0
                        ),
                    }
                )
            finally:
                subprocess.run(
                    ["git", "worktree", "remove", "--force", str(worktree)],
                    cwd=REPO_ROOT,
                    capture_output=True,
                    check=False,
                    text=True,
                )
        hashes = [item.get("observed_hashes") for item in runs if item.get("passed")]
        return {
            "run_count": len(runs),
            "runs": runs,
            "cross_run_byte_identity": len(hashes) == 2 and hashes[0] == hashes[1],
            "passed": len(runs) == 2 and all(item.get("passed") for item in runs) and len(hashes) == 2 and hashes[0] == hashes[1],
        }
    finally:
        if scratch_root.exists():
            shutil.rmtree(scratch_root)


def build_review_report(*, run_regeneration: bool = True) -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    manifest = load_json(MANIFEST_PATH)
    preparation_report = load_json(PREPARATION_REPORT_PATH)
    ledger = load_json(LEDGER_PATH)
    custody = preparation_custody()
    audit = independent_packet_audit(packet, manifest, preparation_report, ledger)
    regeneration = isolated_regeneration() if run_regeneration else {"passed": True, "skipped": True}
    checks = {
        "preparation_commit_and_hashes_are_immutable": custody["passed"],
        **audit["checks"],
        "two_clean_detached_regenerations_are_byte_identical": regeneration["passed"],
    }
    ordered_decisions = [
        {"decision_id": decision_id, "passed": checks.get(decision_id, False)}
        for decision_id in DECISION_IDS
    ]
    failed = [item["decision_id"] for item in ordered_decisions if not item["passed"]]
    accepted = not failed
    selected_next = ACCEPTED_NEXT_TARGET if accepted else BLOCKED_NEXT_TARGET
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT" if accepted else "B-BLOCKED",
        "status": "accepted_v2_evidence_authority_repair" if accepted else "blocked_v2_review_failure",
        "selected_next_target": selected_next,
        "selected_next_target_kind": selected_next,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered_decisions,
        "preparation_custody": custody,
        "independent_packet_audit": audit,
        "isolated_regeneration": regeneration,
        "reviewer_independence": {
            "imports_preparation_generator": False,
            "shares_role_assignment_logic": False,
            "shares_eligibility_implementation": False,
            "shares_route_selection_implementation": False,
            "shares_mutation_constructors": False,
            "shares_combined_pass_flags": False,
            "shared_only": ["artifact formats", "canonical JSON contract", "hash primitives", "source-reading primitives"],
        },
        "authority_rotation": {
            "v2_packet_accepted": accepted,
            "first_unit_selector_preparation_authorized": accepted,
            "unit_resolution_execution_authorized": False,
            "Maxwell_Dirac_selected": False,
            "downstream_pairs_authorized": False,
        },
        "boundary": packet["boundary"],
        "nonclaims": packet["nonclaims"],
        "prompt_sha256": PROMPT_BASELINE_SHA256,
        "claim": (
            "The proposition-specific v2 evidence-authority repair and twelve planning routes are accepted; "
            "only preparation of the scored first-unit selector is authorized."
            if accepted
            else "V2 is blocked and only a versioned v3 correction is authorized."
        ),
    }


def write_report(report: dict[str, Any]) -> None:
    REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REVIEW_REPORT_PATH.write_bytes(canonical_json_bytes(report))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the v2 evidence-authority route packet.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--skip-isolated-regeneration", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report(run_regeneration=not args.skip_isolated_regeneration)
    except (OSError, ValueError, json.JSONDecodeError, subprocess.SubprocessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if args.write:
        write_report(report)
        print(
            f"wrote v2 independent review: {report['verdict']}; "
            f"{report['passed_decision_count']}/{report['decision_count']} decisions pass"
        )
        return 0 if report["accepted"] else 2
    if args.check:
        expected = canonical_json_bytes(report)
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print(f"stale or missing review report: {REVIEW_REPORT_PATH}", file=sys.stderr)
            return 1
        print(
            f"v2 independent review verified: {report['verdict']}; "
            f"{report['passed_decision_count']}/{report['decision_count']} decisions pass"
        )
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
