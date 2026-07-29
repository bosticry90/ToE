"""Bounded scientific-program governance with immutable OPEN/CLOSE events.

The module deliberately implements only the I-JSON value domain required by
the governance records.  JSON numbers are restricted to exactly representable
IEEE-754 safe integers; quantities requiring decimal precision must use typed
strings.  This keeps the local JCS implementation small, deterministic, and
portable without silently approximating scientific values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
)


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
)
EVENT_ROOT = (
    REPO_ROOT / "formal" / "docs" / "release" / "bounded_program_events"
)

GOVERNANCE_SCHEMA_ID = "TOE_BOUNDED_PROGRAM_GOVERNANCE_v1"
REGISTRY_EXTENSION_KEY = "bounded_program_governance_v1"
PROGRAMS_KEY = "bounded_programs_v1"

SET_LIKE_ARRAY_FIELDS = (
    "authorized_inputs",
    "required_outputs",
    "prohibited_claims",
    "dependency_artifact_ids",
    "terminal_outcome_vocabulary",
)
ORDERED_ARRAY_FIELDS = (
    "rewrite_precedence",
    "substitution_order",
    "variable_ordering",
    "dependency_execution_sequence",
    "Jordan_chain_member_order",
)
SCOPE_FIELDS = (
    "semantic_stage_id",
    "normalized_scientific_question",
    *SET_LIKE_ARRAY_FIELDS,
)
NATIVE_HYPOTHESIS_SENTINELS = (
    "NONE_DIRECTLY_CONTROL_MODEL",
    "NONE_GOVERNANCE_ONLY",
)
NATIVE_RELEVANCE_KINDS = (
    "DIRECT_NATIVE_TEST",
    "CONTROL_MODEL_CRITERION",
    "GOVERNANCE_INFRASTRUCTURE",
    "MAINTENANCE_ONLY",
)
TERMINAL_RESULTS = ("PASSED", "BLOCKED", "FAILED")
PROGRAM_STATES = ("UNOPENED", "OPEN", "CLOSED")
MAX_SAFE_INTEGER = (1 << 53) - 1

QUADRATIC_PROGRAM_ID = "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
QUADRATIC_MANDATORY_EXIT = (
    "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"
)
QUADRATIC_STAGE_DEFINITIONS = (
    {
        "semantic_stage_id": "STRICT_HARMONIC_GAUGE_JET_CONTRACT",
        "target": (
            "prepare_qft_gr_quadratic_generic_background_linearization_"
            "gauge_and_jet_contract_v0"
        ),
        "normalized_scientific_question": (
            "Freeze the strict-harmonic generic-background gauge, trace atlas, "
            "finite-jet, regularity, and confluent-rewrite contract."
        ),
        "authorized_inputs": [
            "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_LINEARIZATION_RESULT_REVIEW_20260728_v0",
            "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_REDUCED_SYSTEM_V0",
        ],
        "required_outputs": [
            "strict_harmonic_gauge_contract",
            "tracefree_atlas_and_regular_strata",
            "reduced_variable_regularity_ledger",
            "original_metric_equivalence_regularity_ledger",
            "rewrite_termination_and_confluence_certificate",
            "Minkowski_regression",
        ],
        "prohibited_claims": [
            "generic_all_gauges_result",
            "finite_loss_established",
            "local_well_posedness",
            "quadratic_gravity_native_toe_status",
        ],
        "dependency_artifact_ids": [
            "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_LINEARIZATION_RESULT_REVIEW_20260728_v0",
        ],
        "terminal_outcome_vocabulary": [
            "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_COMPLETE",
            "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "COMPONENT_EXPANDED_LINEARIZATION",
        "target": (
            "derive_qft_gr_quadratic_component_expanded_generic_background_"
            "linearization_v1"
        ),
        "normalized_scientific_question": (
            "Derive the complete strict-harmonic component-expanded generic-"
            "background linearization and independently verify its inventory."
        ),
        "authorized_inputs": [
            "STRICT_HARMONIC_GAUGE_JET_CONTRACT",
            "accepted_64_equation_reduced_system",
            "accepted_Minkowski_128_state_224_entry_control",
        ],
        "required_outputs": [
            "off_shell_component_form",
            "on_shell_component_form",
            "gauge_compatible_component_form",
            "independent_equation_inventory",
            "exact_Minkowski_specialization",
        ],
        "prohibited_claims": [
            "generic_frozen_spectrum",
            "finite_loss_established",
            "local_well_posedness",
        ],
        "dependency_artifact_ids": ["STRICT_HARMONIC_GAUGE_JET_CONTRACT"],
        "terminal_outcome_vocabulary": [
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE",
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "EXACT_FROZEN_COMPANION_OPERATOR",
        "target": "derive_qft_gr_quadratic_exact_generic_frozen_companion_operator_v1",
        "normalized_scientific_question": (
            "Construct the exact frozen first-order companion operator including "
            "principal, weighted-principal, and subprincipal entries."
        ),
        "authorized_inputs": ["COMPONENT_EXPANDED_LINEARIZATION"],
        "required_outputs": [
            "exact_frozen_companion_matrix",
            "background_stratum_contract",
            "chart_transition_certificates",
            "Minkowski_operator_regression",
        ],
        "prohibited_claims": [
            "finite_loss_established",
            "constraint_quotient_completed",
            "local_well_posedness",
        ],
        "dependency_artifact_ids": ["COMPONENT_EXPANDED_LINEARIZATION"],
        "terminal_outcome_vocabulary": [
            "GENERIC_FROZEN_COMPANION_OPERATOR_EXACTLY_DERIVED",
            "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED",
        ],
    },
    {
        "semantic_stage_id": "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
        "target": (
            "derive_qft_gr_quadratic_constraint_tangent_and_physical_"
            "quotient_v0"
        ),
        "normalized_scientific_question": (
            "Construct the exact constraint tangent projector, residual-gauge "
            "quotient, and locally uniform quotient norm."
        ),
        "authorized_inputs": [
            "EXACT_FROZEN_COMPANION_OPERATOR",
            "accepted_constraint_propagation_system",
        ],
        "required_outputs": [
            "independent_constraint_row_basis",
            "row_space_equivalence_witnesses",
            "constraint_tangent_projector",
            "strict_harmonic_residual_gauge_Cauchy_map",
            "physical_quotient_norm",
            "complement_independence_certificate",
            "zero_frequency_control",
        ],
        "prohibited_claims": [
            "positive_physical_energy",
            "finite_loss_established",
            "local_well_posedness",
        ],
        "dependency_artifact_ids": ["EXACT_FROZEN_COMPANION_OPERATOR"],
        "terminal_outcome_vocabulary": [
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT_COMPLETE",
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "SUBPRINCIPAL_PROPAGATOR_GROWTH",
        "target": (
            "compute_qft_gr_quadratic_subprincipal_weighted_propagator_"
            "growth_v0"
        ),
        "normalized_scientific_question": (
            "Determine the exact locally uniform weighted propagator growth on "
            "unrestricted, constraint-tangent, and physical-quotient sectors."
        ),
        "authorized_inputs": [
            "EXACT_FROZEN_COMPANION_OPERATOR",
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
        ],
        "required_outputs": [
            "weighted_propagator_bounds",
            "nonnormal_growth_analysis",
            "directional_uniformity_certificate",
            "saturating_lower_bound_data",
            "sector_loss_classification",
        ],
        "prohibited_claims": [
            "variable_coefficient_estimate",
            "nonlinear_local_well_posedness",
            "quadratic_gravity_native_toe_status",
        ],
        "dependency_artifact_ids": [
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
            "EXACT_FROZEN_COMPANION_OPERATOR",
        ],
        "terminal_outcome_vocabulary": [
            "FINITE_LOSS_ESTABLISHED_ON_REGULAR_STRATA",
            "FINITE_LOSS_REFUTED",
            "FINITE_LOSS_ONLY_ON_SPECIAL_BACKGROUNDS",
            "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        ],
    },
)

NATIVE_PROGRAM_TEMPLATE = {
    "program_id": "TOE_NATIVE_SURROGATE_V0",
    "authorized_stage_count": 5,
    "repair_attempt_count": 0,
    "no_subsidiary_scientific_targets": True,
    "status": "TEMPLATE_NOT_AUTHORIZED",
    "semantic_stage_ids": [
        "COHERENCE_REPRESENTATION",
        "MINIMAL_ACTION_SELECTION",
        "INTERNAL_VIABILITY",
        "SEAM_AUDIT",
        "OBSERVABLE_AND_UNIQUENESS",
    ],
}


class BoundedProgramError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise BoundedProgramError(f"duplicate JSON property name: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise BoundedProgramError(f"non-I-JSON numeric value: {value}")


def strict_json_loads(text: str) -> Any:
    return json.loads(
        text,
        object_pairs_hook=_strict_object,
        parse_constant=_reject_constant,
    )


def strict_json_load(path: Path) -> Any:
    return strict_json_loads(path.read_text(encoding="utf-8"))


def _validate_string(value: str, *, path: str) -> None:
    try:
        value.encode("utf-8", errors="strict")
        value.encode("utf-16-be", errors="strict")
    except UnicodeError as error:
        raise BoundedProgramError(f"invalid Unicode at {path}") from error


def validate_ijson(value: Any, *, path: str = "$") -> None:
    if value is None or isinstance(value, bool):
        return
    if isinstance(value, str):
        _validate_string(value, path=path)
        return
    if isinstance(value, int):
        if abs(value) > MAX_SAFE_INTEGER:
            raise BoundedProgramError(
                f"integer outside exactly representable I-JSON range at {path}"
            )
        return
    if isinstance(value, float):
        if not math.isfinite(value):
            raise BoundedProgramError(f"non-finite number at {path}")
        raise BoundedProgramError(
            f"floating JSON numbers are prohibited in governance records at {path}; "
            "use a typed decimal string"
        )
    if isinstance(value, list):
        for index, item in enumerate(value):
            validate_ijson(item, path=f"{path}[{index}]")
        return
    if isinstance(value, dict):
        for key, item in value.items():
            if not isinstance(key, str):
                raise BoundedProgramError(f"non-string object key at {path}")
            _validate_string(key, path=f"{path}.<key>")
            validate_ijson(item, path=f"{path}.{key}")
        return
    raise BoundedProgramError(f"unsupported I-JSON value at {path}: {type(value)!r}")


def _jcs_string(value: str) -> bytes:
    _validate_string(value, path="$")
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def _utf16_sort_key(value: str) -> bytes:
    return value.encode("utf-16-be", errors="strict")


def jcs_bytes(value: Any) -> bytes:
    """Return RFC-8785-compatible bytes for the bounded I-JSON subset."""
    validate_ijson(value)
    if value is None:
        return b"null"
    if value is True:
        return b"true"
    if value is False:
        return b"false"
    if isinstance(value, int):
        return str(value).encode("ascii")
    if isinstance(value, str):
        return _jcs_string(value)
    if isinstance(value, list):
        return b"[" + b",".join(jcs_bytes(item) for item in value) + b"]"
    if isinstance(value, dict):
        rows = []
        for key in sorted(value, key=_utf16_sort_key):
            rows.append(_jcs_string(key) + b":" + jcs_bytes(value[key]))
        return b"{" + b",".join(rows) + b"}"
    raise AssertionError("validate_ijson accepted an unsupported value")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def normalize_scope(scope: dict[str, Any]) -> dict[str, Any]:
    if set(scope) != set(SCOPE_FIELDS):
        missing = sorted(set(SCOPE_FIELDS) - set(scope))
        extra = sorted(set(scope) - set(SCOPE_FIELDS))
        raise BoundedProgramError(
            f"scope fields do not match contract; missing={missing}, extra={extra}"
        )

    normalized: dict[str, Any] = {}
    for field in SCOPE_FIELDS:
        value = scope[field]
        if field not in SET_LIKE_ARRAY_FIELDS:
            normalized[field] = value
            continue
        if not isinstance(value, list):
            raise BoundedProgramError(f"{field} must be a set-like array")
        keyed: list[tuple[bytes, Any]] = [(jcs_bytes(item), item) for item in value]
        canonical_items = [item[0] for item in keyed]
        if len(canonical_items) != len(set(canonical_items)):
            raise BoundedProgramError(f"duplicate semantic element in {field}")
        normalized[field] = [item for _, item in sorted(keyed, key=lambda row: row[0])]

    validate_ijson(normalized)
    return normalized


def scope_hash(scope: dict[str, Any]) -> str:
    return sha256_bytes(jcs_bytes(normalize_scope(scope)))


def _stage_scope(stage: dict[str, Any]) -> dict[str, Any]:
    return {field: stage[field] for field in SCOPE_FIELDS}


def _event_hash(event: dict[str, Any]) -> str:
    payload = {key: value for key, value in event.items() if key != "event_hash"}
    return sha256_bytes(jcs_bytes(payload))


def _pretty_json_bytes(value: Any) -> bytes:
    validate_ijson(value)
    return (
        json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    ).encode("utf-8")


def _registry_json_bytes(value: Any) -> bytes:
    """Preserve the legacy registry's broader numeric domain during migration."""
    return (
        json.dumps(value, indent=2, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def _git_output(*args: str, cwd: Path = REPO_ROOT) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def git_blob_oid(path: Path) -> str:
    return _git_output("hash-object", str(path))


def _quadratic_program_record() -> dict[str, Any]:
    stages = []
    for index, definition in enumerate(QUADRATIC_STAGE_DEFINITIONS, start=1):
        stage = dict(definition)
        stage["stage_number"] = index
        stage["scope_hash"] = scope_hash(_stage_scope(stage))
        stages.append(stage)
    return {
        "program_id": QUADRATIC_PROGRAM_ID,
        "authorized_stage_count": 5,
        "current_stage_number": 0,
        "attempted_stage_ids": [],
        "blocked_stage_id": None,
        "repair_attempt_count": 0,
        "mandatory_exit_target": QUADRATIC_MANDATORY_EXIT,
        "no_subsidiary_scientific_targets": True,
        "event_chain_tip_hash": None,
        "last_closed_attempt_number": 0,
        "state": "UNOPENED",
        "open_attempt_number": None,
        "events": [],
        "stage_definitions": stages,
    }


def governance_contract() -> dict[str, Any]:
    return {
        "schema_id": GOVERNANCE_SCHEMA_ID,
        "schema_version": 1,
        "status": "INSTALLED_GOVERNANCE_ONLY_NO_SCIENTIFIC_ROTATION",
        "set_like_array_fields": list(SET_LIKE_ARRAY_FIELDS),
        "ordered_array_fields": list(ORDERED_ARRAY_FIELDS),
        "native_hypothesis_sentinels": list(NATIVE_HYPOTHESIS_SENTINELS),
        "native_relevance_kinds": list(NATIVE_RELEVANCE_KINDS),
        "prerequisite_scope": "AUTHORIZED_PROGRAM_ONLY",
        "event_state_machine": [
            "UNOPENED",
            "OPEN",
            "PASSED_OR_BLOCKED_OR_FAILED",
            "CLOSED",
        ],
        "event_hash_algorithm": "SHA-256 over bounded I-JSON JCS bytes",
        "scope_hash_algorithm": (
            "project set normalization followed by RFC 8785 JCS and SHA-256"
        ),
        "number_policy": (
            "safe integers only; scientific decimal values use typed strings"
        ),
        "native_program_template": NATIVE_PROGRAM_TEMPLATE,
    }


def install_registry_extension(registry: dict[str, Any]) -> dict[str, Any]:
    if REGISTRY_EXTENSION_KEY in registry or PROGRAMS_KEY in registry:
        raise BoundedProgramError("bounded-program registry extension already installed")
    migrated = dict(registry)
    migrated["schema_version"] = 1
    envelope = dict(migrated.get("registry_envelope_v0", {}))
    envelope["schema_version"] = 1
    migrated["registry_envelope_v0"] = envelope
    migrated[REGISTRY_EXTENSION_KEY] = governance_contract()
    migrated[PROGRAMS_KEY] = {
        QUADRATIC_PROGRAM_ID: _quadratic_program_record(),
    }
    return migrated


def _program(registry: dict[str, Any], program_id: str) -> dict[str, Any]:
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict) or program_id not in programs:
        raise BoundedProgramError(f"unknown or unauthorized bounded program: {program_id}")
    program = programs[program_id]
    if not isinstance(program, dict):
        raise BoundedProgramError(f"invalid program record: {program_id}")
    return program


def _stage(program: dict[str, Any], semantic_stage_id: str) -> dict[str, Any]:
    matches = [
        stage
        for stage in program.get("stage_definitions", [])
        if stage.get("semantic_stage_id") == semantic_stage_id
    ]
    if len(matches) != 1:
        raise BoundedProgramError(
            f"expected one stage {semantic_stage_id!r}, found {len(matches)}"
        )
    return matches[0]


def _event_relative_path(
    program_id: str, attempt_sequence_number: int, event_type: str
) -> str:
    suffix = "OPEN" if event_type == "ATTEMPT_OPEN" else "CLOSE"
    return (
        "formal/docs/release/bounded_program_events/"
        f"{program_id}_ATTEMPT_{attempt_sequence_number:02d}_{suffix}_v0.json"
    )


def open_attempt(
    registry: dict[str, Any],
    *,
    registry_bytes: bytes,
    program_id: str,
    semantic_stage_id: str,
    target: str,
    opened_from_commit: str,
) -> tuple[dict[str, Any], str, dict[str, Any]]:
    program = _program(registry, program_id)
    if program["state"] == "OPEN":
        raise BoundedProgramError("cannot open a second attempt while one is open")
    if program["blocked_stage_id"] is not None:
        raise BoundedProgramError("blocked program must take its mandatory exit")
    stage = _stage(program, semantic_stage_id)
    expected_stage_number = program["last_closed_attempt_number"] + 1
    if stage["stage_number"] != expected_stage_number:
        raise BoundedProgramError(
            f"stage order violation: expected {expected_stage_number}, "
            f"got {stage['stage_number']}"
        )
    if target != stage["target"]:
        raise BoundedProgramError("target does not match the canonical stage target")
    if semantic_stage_id in program["attempted_stage_ids"]:
        raise BoundedProgramError("semantic stage has already been attempted")
    if expected_stage_number > program["authorized_stage_count"]:
        raise BoundedProgramError("authorized stage count exhausted")
    if scope_hash(_stage_scope(stage)) != stage["scope_hash"]:
        raise BoundedProgramError("stage scope hash drift")

    previous_event_hash = program["event_chain_tip_hash"]
    event_sequence_number = len(program["events"]) + 1
    event = {
        "event_type": "ATTEMPT_OPEN",
        "event_sequence_number": event_sequence_number,
        "attempt_sequence_number": expected_stage_number,
        "program_id": program_id,
        "semantic_stage_id": semantic_stage_id,
        "target": target,
        "scope_hash": stage["scope_hash"],
        "registry_snapshot_hash": sha256_bytes(registry_bytes),
        "previous_event_hash": previous_event_hash,
        "opened_from_commit": opened_from_commit,
    }
    event["event_hash"] = _event_hash(event)
    relative_path = _event_relative_path(
        program_id, expected_stage_number, "ATTEMPT_OPEN"
    )

    migrated = json.loads(json.dumps(registry))
    migrated_program = _program(migrated, program_id)
    migrated_program["current_stage_number"] = stage["stage_number"]
    migrated_program["attempted_stage_ids"].append(semantic_stage_id)
    migrated_program["state"] = "OPEN"
    migrated_program["open_attempt_number"] = expected_stage_number
    migrated_program["event_chain_tip_hash"] = event["event_hash"]
    migrated_program["events"].append(
        {
            "event_type": "ATTEMPT_OPEN",
            "attempt_sequence_number": expected_stage_number,
            "path": relative_path,
            "event_hash": event["event_hash"],
            "sha256": sha256_bytes(_pretty_json_bytes(event)),
        }
    )
    return migrated, relative_path, event


def close_attempt(
    registry: dict[str, Any],
    *,
    program_id: str,
    result_artifact_path: str,
    review_artifact_path: str,
    terminal_result: str,
    closed_from_commit: str,
) -> tuple[dict[str, Any], str, dict[str, Any]]:
    if terminal_result not in TERMINAL_RESULTS:
        raise BoundedProgramError(f"invalid terminal result: {terminal_result}")
    program = _program(registry, program_id)
    if program["state"] != "OPEN":
        raise BoundedProgramError("no open attempt to close")
    attempt_number = program["open_attempt_number"]
    if not isinstance(attempt_number, int):
        raise BoundedProgramError("open attempt number is missing")
    if not program["events"] or program["events"][-1]["event_type"] != "ATTEMPT_OPEN":
        raise BoundedProgramError("latest event is not an OPEN event")

    result_path = REPO_ROOT / result_artifact_path
    review_path = REPO_ROOT / review_artifact_path
    if not result_path.is_file() or not review_path.is_file():
        raise BoundedProgramError("result and review artifacts must exist before CLOSE")

    open_event_hash = program["events"][-1]["event_hash"]
    event = {
        "event_type": "ATTEMPT_CLOSE",
        "event_sequence_number": len(program["events"]) + 1,
        "attempt_sequence_number": attempt_number,
        "program_id": program_id,
        "open_event_hash": open_event_hash,
        "result_artifact_path": result_artifact_path,
        "result_artifact_hash": sha256_path(result_path),
        "review_artifact_path": review_artifact_path,
        "review_artifact_hash": sha256_path(review_path),
        "terminal_result": terminal_result,
        "previous_event_hash": program["event_chain_tip_hash"],
        "closed_from_commit": closed_from_commit,
    }
    event["event_hash"] = _event_hash(event)
    relative_path = _event_relative_path(
        program_id, attempt_number, "ATTEMPT_CLOSE"
    )

    migrated = json.loads(json.dumps(registry))
    migrated_program = _program(migrated, program_id)
    semantic_stage_id = migrated_program["attempted_stage_ids"][-1]
    migrated_program["state"] = "CLOSED"
    migrated_program["open_attempt_number"] = None
    migrated_program["last_closed_attempt_number"] = attempt_number
    migrated_program["event_chain_tip_hash"] = event["event_hash"]
    if terminal_result in {"BLOCKED", "FAILED"}:
        migrated_program["blocked_stage_id"] = semantic_stage_id
    migrated_program["events"].append(
        {
            "event_type": "ATTEMPT_CLOSE",
            "attempt_sequence_number": attempt_number,
            "path": relative_path,
            "event_hash": event["event_hash"],
            "sha256": sha256_bytes(_pretty_json_bytes(event)),
        }
    )
    return migrated, relative_path, event


def _validate_stage_definitions(program: dict[str, Any]) -> None:
    stages = program.get("stage_definitions")
    if not isinstance(stages, list):
        raise BoundedProgramError("stage_definitions must be an array")
    if len(stages) != program.get("authorized_stage_count"):
        raise BoundedProgramError("stage definition count does not match authorization")
    seen_ids: set[str] = set()
    seen_targets: set[str] = set()
    for expected_number, stage in enumerate(stages, start=1):
        if stage.get("stage_number") != expected_number:
            raise BoundedProgramError("stage numbers are not contiguous")
        semantic_id = stage.get("semantic_stage_id")
        target = stage.get("target")
        if semantic_id in seen_ids or target in seen_targets:
            raise BoundedProgramError("stage IDs and targets must be one-to-one")
        seen_ids.add(semantic_id)
        seen_targets.add(target)
        if stage.get("scope_hash") != scope_hash(_stage_scope(stage)):
            raise BoundedProgramError(f"scope hash mismatch for {semantic_id}")


def validate_event_chain(
    registry: dict[str, Any],
    *,
    repo_root: Path = REPO_ROOT,
    verify_git_history: bool = False,
) -> None:
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded programs are missing")
    for program_id, program in programs.items():
        _validate_stage_definitions(program)
        events = program.get("events")
        if not isinstance(events, list):
            raise BoundedProgramError("events must be an array")
        previous_hash: str | None = None
        open_attempt: int | None = None
        closed_attempts = 0
        attempted_stage_ids = program.get("attempted_stage_ids")
        if not isinstance(attempted_stage_ids, list):
            raise BoundedProgramError("attempted_stage_ids must be an array")
        if len(attempted_stage_ids) != len(set(attempted_stage_ids)):
            raise BoundedProgramError("attempted semantic stages are not unique")

        for event_number, reference in enumerate(events, start=1):
            relative_path = reference.get("path")
            path = repo_root / relative_path
            if not path.is_file():
                raise BoundedProgramError(f"missing event artifact: {relative_path}")
            raw = path.read_bytes()
            if sha256_bytes(raw) != reference.get("sha256"):
                raise BoundedProgramError(f"event byte hash mismatch: {relative_path}")
            event = strict_json_loads(raw.decode("utf-8"))
            if event.get("event_sequence_number") != event_number:
                raise BoundedProgramError("event sequence numbers are not contiguous")
            if event.get("previous_event_hash") != previous_hash:
                raise BoundedProgramError("event hash chain is broken")
            if event.get("event_hash") != _event_hash(event):
                raise BoundedProgramError("event self-hash is invalid")
            if event.get("event_hash") != reference.get("event_hash"):
                raise BoundedProgramError("event reference hash mismatch")
            if event.get("program_id") != program_id:
                raise BoundedProgramError("event belongs to another program")

            attempt_number = event.get("attempt_sequence_number")
            if event.get("event_type") == "ATTEMPT_OPEN":
                if open_attempt is not None:
                    raise BoundedProgramError("attempt opened before prior CLOSE")
                if attempt_number != closed_attempts + 1:
                    raise BoundedProgramError("attempt numbers are not contiguous")
                open_attempt = attempt_number
            elif event.get("event_type") == "ATTEMPT_CLOSE":
                if open_attempt != attempt_number:
                    raise BoundedProgramError("CLOSE does not match the open attempt")
                if event.get("open_event_hash") != previous_hash:
                    raise BoundedProgramError("CLOSE does not reference its OPEN event")
                if event.get("terminal_result") not in TERMINAL_RESULTS:
                    raise BoundedProgramError("CLOSE has an invalid terminal result")
                for key in ("result_artifact_path", "review_artifact_path"):
                    artifact_path = repo_root / event[key]
                    if not artifact_path.is_file():
                        raise BoundedProgramError(f"missing CLOSE artifact: {event[key]}")
                if sha256_path(repo_root / event["result_artifact_path"]) != event.get(
                    "result_artifact_hash"
                ):
                    raise BoundedProgramError("CLOSE result hash mismatch")
                if sha256_path(repo_root / event["review_artifact_path"]) != event.get(
                    "review_artifact_hash"
                ):
                    raise BoundedProgramError("CLOSE review hash mismatch")
                open_attempt = None
                closed_attempts += 1
            else:
                raise BoundedProgramError("unknown event type")

            if verify_git_history:
                additions = _git_output(
                    "log",
                    "--diff-filter=A",
                    "--format=%H",
                    "--",
                    relative_path,
                    cwd=repo_root,
                ).splitlines()
                if additions:
                    introduction = additions[-1]
                    introduced_bytes = subprocess.run(
                        ["git", "show", f"{introduction}:{relative_path}"],
                        cwd=repo_root,
                        check=True,
                        capture_output=True,
                    ).stdout
                    if introduced_bytes != raw:
                        raise BoundedProgramError(
                            f"historical event bytes changed: {relative_path}"
                        )
            previous_hash = event["event_hash"]

        if program.get("event_chain_tip_hash") != previous_hash:
            raise BoundedProgramError("program event-chain tip is stale")
        expected_state = "OPEN" if open_attempt is not None else (
            "CLOSED" if events else "UNOPENED"
        )
        if program.get("state") != expected_state:
            raise BoundedProgramError("program state does not match event history")
        if program.get("last_closed_attempt_number") != closed_attempts:
            raise BoundedProgramError("last closed attempt number is inconsistent")
        if program.get("repair_attempt_count") != 0:
            raise BoundedProgramError("repair attempts are prohibited")


def validate_registry_extension(registry: dict[str, Any]) -> None:
    contract = registry.get(REGISTRY_EXTENSION_KEY)
    if contract != governance_contract():
        raise BoundedProgramError("bounded-program governance contract drift")
    if registry.get("schema_version") != 1:
        raise BoundedProgramError("registry schema version is not 1")
    validate_event_chain(registry)


def write_event(path: Path, event: dict[str, Any]) -> None:
    if path.exists():
        raise BoundedProgramError(f"immutable event already exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_pretty_json_bytes(event))


def _load_registry_bytes(path: Path) -> tuple[bytes, dict[str, Any]]:
    raw = path.read_bytes()
    registry = strict_json_loads(raw.decode("utf-8"))
    if not isinstance(registry, dict):
        raise BoundedProgramError("registry root must be an object")
    return raw, registry


def _command_install(registry_path: Path) -> None:
    _, registry = _load_registry_bytes(registry_path)
    migrated = install_registry_extension(registry)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_reinstall_from_head(registry_path: Path) -> None:
    relative_path = registry_path.resolve().relative_to(REPO_ROOT).as_posix()
    original_bytes = subprocess.run(
        ["git", "show", f"HEAD:{relative_path}"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout
    original = strict_json_loads(original_bytes.decode("utf-8"))
    if not isinstance(original, dict):
        raise BoundedProgramError("HEAD registry root must be an object")
    migrated = install_registry_extension(original)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_validate(registry_path: Path, verify_git_history: bool) -> None:
    _, registry = _load_registry_bytes(registry_path)
    validate_registry_extension(registry)
    if verify_git_history:
        validate_event_chain(registry, verify_git_history=True)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=("install", "reinstall-from-head", "validate"),
    )
    parser.add_argument("--registry", type=Path, default=REGISTRY_PATH)
    parser.add_argument("--verify-git-history", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.command == "install":
        _command_install(args.registry)
    elif args.command == "reinstall-from-head":
        _command_reinstall_from_head(args.registry)
    else:
        _command_validate(args.registry, args.verify_git_history)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
