from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
)

REGISTRY_SCHEMA_ID = "LOOP_CONTROL_REGISTRY_v0"
REGISTRY_SCHEMA_VERSION = 1
REGISTRY_STATUS = "ACTIVE_NONLIVE_NONCLAIM"
CURRENT_PROJECTION_SCHEMA_ID = "LOOP_CONTROL_CURRENT_PROJECTION_v0"
CURRENT_STATE_AUTHORITY_CONTRACT_SCHEMA_ID = (
    "LOOP_CONTROL_CURRENT_TARGET_STATE_AUTHORITY_CONTRACT_v0"
)

CURRENT_STATE_AUTHORITY_KEYS = [
    "schema_id",
    "live_next_target",
    "previous_live_next_target",
    "live_next_target_kind",
    "live_next_target_evidence",
    "live_next_target_report",
    "live_next_target_outcome",
    "live_next_target_strict_outcome",
]

# Registry keys follow Python/JSON snake_case. Case-fold collisions not listed
# here are rejected so harmless object reordering cannot silently select a new
# consumer-facing spelling.
CANONICAL_CASEFOLD_KEYS = {
    "a_source_ck_rule_candidate": "A_source_ck_rule_candidate",
    "bianchi_compatibility_claimed": "Bianchi_compatibility_claimed",
    "ccft_validated": "ccft_validated",
    "full_maxwell_closure_claimed": "full_maxwell_closure_claimed",
    "full_scalar_qft_closure_claimed": "full_scalar_qft_closure_claimed",
    "selected_a_ck_constraint_family": "selected_A_ck_constraint_family",
}

DEPRECATED_FLAT_PACKET_KEYS = [
    "artifact_id",
    "captured_at_utc",
    "packet_id",
    "result_token",
    "workstream_id",
]


class RegistryIntegrityError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RegistryIntegrityError(f"duplicate exact JSON key: {key}")
        result[key] = value
    return result


def load_registry(path: Path = DEFAULT_REGISTRY_PATH) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object)


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def atomic_write_registry(path: Path, payload: bytes) -> None:
    """Durably validate and atomically replace the registry in one directory."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="wb",
            dir=path.parent,
            prefix=f".{path.name}.",
            suffix=".tmp",
            delete=False,
        ) as handle:
            temporary_path = Path(handle.name)
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())

        reread = temporary_path.read_bytes()
        if reread != payload:
            raise RegistryIntegrityError("temporary registry bytes changed before replace")
        parsed = json.loads(reread, object_pairs_hook=_strict_object)
        if not isinstance(parsed, dict):
            raise RegistryIntegrityError("temporary registry root must be a JSON object")
        os.replace(temporary_path, path)
        temporary_path = None
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


def _value_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _canonicalize_casefold_keys(
    value: Any,
    *,
    path: str,
    aliases: list[dict[str, str]],
) -> Any:
    if isinstance(value, list):
        return [
            _canonicalize_casefold_keys(item, path=f"{path}[{index}]", aliases=aliases)
            for index, item in enumerate(value)
        ]

    if not isinstance(value, dict):
        return value

    groups: dict[str, list[str]] = {}
    for key in value:
        groups.setdefault(key.casefold(), []).append(key)

    collision_info: dict[str, tuple[str, list[str]]] = {}
    for folded, keys in groups.items():
        if len(keys) == 1:
            continue
        first_value = value[keys[0]]
        if any(value[key] != first_value for key in keys[1:]):
            raise RegistryIntegrityError(
                f"case-fold collision with unequal values at {path}: {keys}"
            )
        canonical = CANONICAL_CASEFOLD_KEYS.get(folded)
        if canonical is None:
            raise RegistryIntegrityError(
                f"case-fold collision has no explicit canonical spelling at {path}: {keys}"
            )
        if canonical not in keys:
            raise RegistryIntegrityError(
                f"canonical spelling {canonical!r} is absent from collision {keys!r}"
            )
        collision_info[folded] = (canonical, keys)

    rebuilt: dict[str, Any] = {}
    emitted: set[str] = set()
    for key, child in value.items():
        folded = key.casefold()
        if folded not in collision_info:
            rebuilt[key] = _canonicalize_casefold_keys(
                child,
                path=f"{path}.{key}",
                aliases=aliases,
            )
            continue

        canonical, keys = collision_info[folded]
        if folded in emitted:
            continue
        emitted.add(folded)
        rebuilt[canonical] = _canonicalize_casefold_keys(
            value[canonical],
            path=f"{path}.{canonical}",
            aliases=aliases,
        )
        for original in keys:
            if original == canonical:
                continue
            aliases.append(
                {
                    "object_path": path,
                    "deprecated_key": original,
                    "canonical_key": canonical,
                    "value_sha256": _value_sha256(value[original]),
                }
            )

    return rebuilt


def casefold_collisions(value: Any, path: str = "$") -> list[tuple[str, list[str]]]:
    collisions: list[tuple[str, list[str]]] = []
    if isinstance(value, dict):
        groups: dict[str, list[str]] = {}
        for key in value:
            groups.setdefault(key.casefold(), []).append(key)
        collisions.extend((path, keys) for keys in groups.values() if len(keys) > 1)
        for key, child in value.items():
            collisions.extend(casefold_collisions(child, f"{path}.{key}"))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            collisions.extend(casefold_collisions(child, f"{path}[{index}]"))
    return collisions


def _current_workstream(registry: dict[str, Any], target: str) -> dict[str, Any]:
    matches = [
        item
        for item in registry.get("workstreams", [])
        if item.get("workstream_id") == target
    ]
    if len(matches) != 1:
        raise RegistryIntegrityError(
            f"expected one workstream for current target {target!r}, found {len(matches)}"
        )
    current = matches[0]
    if current.get("status") != "active":
        raise RegistryIntegrityError(
            f"current workstream {target!r} is not active: {current.get('status')!r}"
        )
    return current


def _duplicate_workstream_quarantine(
    registry: dict[str, Any], current_target: str
) -> dict[str, Any]:
    grouped: dict[str, list[tuple[int, dict[str, Any]]]] = {}
    for index, row in enumerate(registry.get("workstreams", [])):
        workstream_id = row.get("workstream_id")
        if not isinstance(workstream_id, str) or not workstream_id:
            raise RegistryIntegrityError(f"workstreams[{index}] has no workstream_id")
        grouped.setdefault(workstream_id, []).append((index, row))

    collisions: list[dict[str, Any]] = []
    for workstream_id, occurrences in sorted(grouped.items()):
        if len(occurrences) < 2:
            continue
        if workstream_id == current_target:
            raise RegistryIntegrityError(
                f"current workstream id is ambiguous: {current_target!r}"
            )
        records = []
        for index, row in occurrences:
            row_sha256 = _value_sha256(row)
            records.append(
                {
                    "source_index": index,
                    "stable_record_id": f"{workstream_id}@{row_sha256[:16]}",
                    "row_sha256": row_sha256,
                    "report": row.get("report"),
                    "consumed_target": row.get("consumed_target"),
                    "selected_next_target": row.get("selected_next_target"),
                }
            )
        collisions.append(
            {
                "legacy_workstream_id": workstream_id,
                "occurrence_count": len(records),
                "records": records,
            }
        )
    return {
        "schema_id": "LOOP_CONTROL_DUPLICATE_WORKSTREAM_ID_QUARANTINE_v0",
        "status": "DOCUMENTED_HISTORICAL_IDENTIFIER_COLLISION_NONCURRENT",
        "collision_count": len(collisions),
        "collisions": collisions,
        "authority_rule": (
            "Duplicate historical workstream_id values are not unique record keys. "
            "Use stable_record_id for those rows; no duplicate may be the current target."
        ),
    }


def repair_registry(registry: dict[str, Any]) -> dict[str, Any]:
    # The migration writer mutates its in-memory parse. The normal --check path
    # never calls this function, avoiding a second 52 MB object graph.
    repaired = registry
    retained_aliases = repaired.pop("casefold_key_aliases_v0", [])
    if not isinstance(retained_aliases, list):
        raise RegistryIntegrityError("casefold_key_aliases_v0 must be a list")
    repaired.pop("current_projection_v0", None)
    repaired.pop("current_target_state_authority_contract_v0", None)
    repaired.pop("registry_envelope_v0", None)
    repaired.pop("legacy_flattened_packet_metadata_v0", None)
    repaired.pop("duplicate_workstream_id_quarantine_v0", None)

    state = repaired.get("current_target_state")
    if not isinstance(state, dict) or state.get("schema_id") != "CURRENT_TARGET_STATE_v0":
        raise RegistryIntegrityError("missing or invalid current_target_state")

    target = state.get("live_next_target")
    previous = state.get("previous_live_next_target")
    if not isinstance(target, str) or not target:
        raise RegistryIntegrityError("current_target_state.live_next_target is missing")
    for source_key in ("CURRENT_LIVE_NEXT_TARGET_v0", "ACTIVE_LANE_v0"):
        if repaired.get(source_key) != target:
            raise RegistryIntegrityError(
                f"pre-repair authority disagreement: {source_key}="
                f"{repaired.get(source_key)!r}, current_target_state.live_next_target="
                f"{target!r}"
            )
    current = _current_workstream(repaired, target)

    repaired["schema_id"] = REGISTRY_SCHEMA_ID
    repaired["schema_version"] = REGISTRY_SCHEMA_VERSION
    repaired["status"] = REGISTRY_STATUS

    repaired["ACTIVE_LANE_v0"] = target
    repaired["CURRENT_LIVE_NEXT_TARGET_v0"] = target
    repaired["PREVIOUS_LIVE_NEXT_TARGET_v0"] = previous
    repaired["CURRENT_LIVE_TARGET_KIND_v0"] = state["live_next_target_kind"]
    repaired["CURRENT_LIVE_TARGET_EVIDENCE_v0"] = state["live_next_target_evidence"]
    repaired["CURRENT_LIVE_TARGET_REPORT_v0"] = state["live_next_target_report"]
    repaired["CURRENT_LIVE_TARGET_OUTCOME_v0"] = state["live_next_target_outcome"]
    repaired["CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0"] = state[
        "live_next_target_strict_outcome"
    ]

    repaired["active_lane"] = target
    repaired["active_lane_count"] = 1
    repaired["active_lanes"] = [target]
    repaired["active_workstream"] = target
    repaired["active_workstream_count"] = 1
    repaired["active_workstreams"] = [current]

    repaired["current_target"] = target
    repaired["current_target_kind"] = state["live_next_target_kind"]
    repaired["current_target_evidence"] = state["live_next_target_evidence"]
    repaired["current_target_report"] = state["live_next_target_report"]
    repaired["current_target_outcome"] = state["live_next_target_outcome"]
    repaired["current_target_strict_outcome"] = state["live_next_target_strict_outcome"]

    # Normalize older root aliases that otherwise look authoritative but had
    # retained values from unrelated flattened packets.
    repaired["live_next_target"] = target
    repaired["live_next_target_kind"] = state["live_next_target_kind"]
    repaired["live_next_target_evidence"] = state["live_next_target_evidence"]
    repaired["live_next_target_report"] = state["live_next_target_report"]
    repaired["live_next_target_outcome"] = state["live_next_target_outcome"]
    repaired["live_next_target_strict_outcome"] = state[
        "live_next_target_strict_outcome"
    ]
    repaired["previous_live_next_target"] = previous
    if "previous_live_next_target_kind" in state:
        repaired["previous_live_next_target_kind"] = state[
            "previous_live_next_target_kind"
        ]

    repaired["current_live_next_target"] = target
    repaired["current_live_target"] = target
    repaired["current_live_target_kind"] = state["live_next_target_kind"]
    repaired["current_live_target_evidence"] = state["live_next_target_evidence"]
    repaired["current_live_target_report"] = state["live_next_target_report"]
    repaired["current_live_target_outcome"] = state["live_next_target_outcome"]
    repaired["current_live_target_strict_outcome"] = state[
        "live_next_target_strict_outcome"
    ]

    repaired["registry_envelope_v0"] = {
        "schema_id": REGISTRY_SCHEMA_ID,
        "schema_version": REGISTRY_SCHEMA_VERSION,
        "status": REGISTRY_STATUS,
        "authority_role": "nonclaim_loop_control_history_and_current_projection",
    }
    repaired["current_projection_v0"] = {
        "schema_id": CURRENT_PROJECTION_SCHEMA_ID,
        "active_lane": target,
        "active_workstream_count": 1,
        "current_target": target,
        "current_target_kind": state["live_next_target_kind"],
        "current_target_evidence": state["live_next_target_evidence"],
        "current_target_report": state["live_next_target_report"],
        "current_target_outcome": state["live_next_target_outcome"],
        "current_target_strict_outcome": state["live_next_target_strict_outcome"],
        "previous_target": previous,
        "workstream_id": current["workstream_id"],
    }
    repaired["legacy_flattened_packet_metadata_v0"] = {
        "status": "deprecated_non_authorizing_retained_for_compatibility",
        "keys": DEPRECATED_FLAT_PACKET_KEYS,
        "authority_rule": (
            "These legacy flattened packet fields are historical compatibility data. "
            "They do not override registry_envelope_v0, current_projection_v0, "
            "CURRENT_LIVE_NEXT_TARGET_v0, or current_target_state."
        ),
    }

    aliases: list[dict[str, str]] = [dict(row) for row in retained_aliases]
    repaired = _canonicalize_casefold_keys(repaired, path="$", aliases=aliases)

    canonical_state = repaired["current_target_state"]
    missing_authority_keys = [
        key for key in CURRENT_STATE_AUTHORITY_KEYS if key not in canonical_state
    ]
    if missing_authority_keys:
        raise RegistryIntegrityError(
            f"current_target_state is missing authority keys: {missing_authority_keys}"
        )
    compatibility_fields = {
        key: value
        for key, value in canonical_state.items()
        if key not in CURRENT_STATE_AUTHORITY_KEYS
    }
    repaired["current_target_state_authority_contract_v0"] = {
        "schema_id": CURRENT_STATE_AUTHORITY_CONTRACT_SCHEMA_ID,
        "authoritative_keys": CURRENT_STATE_AUTHORITY_KEYS,
        "flattened_compatibility_key_count": len(compatibility_fields),
        "flattened_compatibility_sha256": _value_sha256(compatibility_fields),
        "authority_rule": (
            "Only the listed current_target_state keys are authoritative. All other "
            "keys in that object are historical flattened compatibility data and must "
            "not override current_projection_v0 or CURRENT_LIVE_NEXT_TARGET_v0."
        ),
    }
    repaired["duplicate_workstream_id_quarantine_v0"] = (
        _duplicate_workstream_quarantine(repaired, target)
    )
    aliases_by_identity = {
        (
            row["object_path"],
            row["deprecated_key"],
            row["canonical_key"],
            row["value_sha256"],
        ): row
        for row in aliases
    }
    aliases = list(aliases_by_identity.values())
    aliases.sort(
        key=lambda row: (
            row["object_path"],
            row["canonical_key"],
            row["deprecated_key"],
        )
    )
    repaired["casefold_key_aliases_v0"] = aliases

    collisions = casefold_collisions(repaired)
    if collisions:
        raise RegistryIntegrityError(f"case-fold collisions remain: {collisions[:5]}")
    return repaired


def validate_registry(registry: dict[str, Any]) -> None:
    """Validate the current projection without rebuilding the full registry."""
    if registry.get("schema_id") != REGISTRY_SCHEMA_ID:
        raise RegistryIntegrityError("registry schema_id is not canonical")
    if registry.get("schema_version") != REGISTRY_SCHEMA_VERSION:
        raise RegistryIntegrityError("registry schema_version is not canonical")
    if registry.get("status") != REGISTRY_STATUS:
        raise RegistryIntegrityError("registry status is not canonical")
    expected_envelope = {
        "schema_id": REGISTRY_SCHEMA_ID,
        "schema_version": REGISTRY_SCHEMA_VERSION,
        "status": REGISTRY_STATUS,
        "authority_role": "nonclaim_loop_control_history_and_current_projection",
    }
    if registry.get("registry_envelope_v0") != expected_envelope:
        raise RegistryIntegrityError("registry_envelope_v0 is not canonical")

    state = registry.get("current_target_state")
    if not isinstance(state, dict) or state.get("schema_id") != "CURRENT_TARGET_STATE_v0":
        raise RegistryIntegrityError("missing or invalid current_target_state")
    target = state.get("live_next_target")
    previous = state.get("previous_live_next_target")
    current = _current_workstream(registry, target)

    expected_aliases = {
        "ACTIVE_LANE_v0": target,
        "CURRENT_LIVE_NEXT_TARGET_v0": target,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": previous,
        "CURRENT_LIVE_TARGET_KIND_v0": state["live_next_target_kind"],
        "CURRENT_LIVE_TARGET_EVIDENCE_v0": state["live_next_target_evidence"],
        "CURRENT_LIVE_TARGET_REPORT_v0": state["live_next_target_report"],
        "CURRENT_LIVE_TARGET_OUTCOME_v0": state["live_next_target_outcome"],
        "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": state[
            "live_next_target_strict_outcome"
        ],
        "active_lane": target,
        "active_workstream": target,
        "current_target": target,
        "live_next_target": target,
        "current_live_next_target": target,
        "current_live_target": target,
        "current_target_kind": state["live_next_target_kind"],
        "live_next_target_kind": state["live_next_target_kind"],
        "current_live_target_kind": state["live_next_target_kind"],
        "current_target_evidence": state["live_next_target_evidence"],
        "live_next_target_evidence": state["live_next_target_evidence"],
        "current_live_target_evidence": state["live_next_target_evidence"],
        "current_target_report": state["live_next_target_report"],
        "live_next_target_report": state["live_next_target_report"],
        "current_live_target_report": state["live_next_target_report"],
        "current_target_outcome": state["live_next_target_outcome"],
        "live_next_target_outcome": state["live_next_target_outcome"],
        "current_live_target_outcome": state["live_next_target_outcome"],
        "current_target_strict_outcome": state["live_next_target_strict_outcome"],
        "live_next_target_strict_outcome": state["live_next_target_strict_outcome"],
        "current_live_target_strict_outcome": state[
            "live_next_target_strict_outcome"
        ],
    }
    drift = {
        key: (registry.get(key), expected)
        for key, expected in expected_aliases.items()
        if registry.get(key) != expected
    }
    if drift:
        raise RegistryIntegrityError(f"current projection alias drift: {drift}")
    if registry.get("active_lanes") != [target]:
        raise RegistryIntegrityError("active_lanes is not the singleton current target")
    if registry.get("active_workstream_count") != 1:
        raise RegistryIntegrityError("active_workstream_count is not one")
    active_workstreams = registry.get("active_workstreams")
    if active_workstreams != [current]:
        raise RegistryIntegrityError("active_workstreams is not the canonical current row")

    projection = registry.get("current_projection_v0")
    expected_projection = {
        "schema_id": CURRENT_PROJECTION_SCHEMA_ID,
        "active_lane": target,
        "active_workstream_count": 1,
        "current_target": target,
        "current_target_kind": state["live_next_target_kind"],
        "current_target_evidence": state["live_next_target_evidence"],
        "current_target_report": state["live_next_target_report"],
        "current_target_outcome": state["live_next_target_outcome"],
        "current_target_strict_outcome": state["live_next_target_strict_outcome"],
        "previous_target": previous,
        "workstream_id": current["workstream_id"],
    }
    if projection != expected_projection:
        raise RegistryIntegrityError("current_projection_v0 is not canonical")

    contract = registry.get("current_target_state_authority_contract_v0")
    compatibility_fields = {
        key: value
        for key, value in state.items()
        if key not in CURRENT_STATE_AUTHORITY_KEYS
    }
    expected_contract = {
        "schema_id": CURRENT_STATE_AUTHORITY_CONTRACT_SCHEMA_ID,
        "authoritative_keys": CURRENT_STATE_AUTHORITY_KEYS,
        "flattened_compatibility_key_count": len(compatibility_fields),
        "flattened_compatibility_sha256": _value_sha256(compatibility_fields),
        "authority_rule": (
            "Only the listed current_target_state keys are authoritative. All other "
            "keys in that object are historical flattened compatibility data and must "
            "not override current_projection_v0 or CURRENT_LIVE_NEXT_TARGET_v0."
        ),
    }
    if contract != expected_contract:
        raise RegistryIntegrityError(
            "current_target_state_authority_contract_v0 is not canonical"
        )
    duplicate_quarantine = registry.get("duplicate_workstream_id_quarantine_v0")
    expected_duplicate_quarantine = _duplicate_workstream_quarantine(registry, target)
    if duplicate_quarantine != expected_duplicate_quarantine:
        raise RegistryIntegrityError(
            "duplicate_workstream_id_quarantine_v0 is not canonical"
        )
    collisions = casefold_collisions(registry)
    if collisions:
        raise RegistryIntegrityError(f"case-fold collisions remain: {collisions[:5]}")
    aliases = registry.get("casefold_key_aliases_v0")
    if not isinstance(aliases, list) or not aliases:
        raise RegistryIntegrityError("casefold_key_aliases_v0 is missing")
    identities: set[tuple[str, str, str, str]] = set()
    for row in aliases:
        folded = row["canonical_key"].casefold()
        expected_spelling = CANONICAL_CASEFOLD_KEYS.get(folded)
        if expected_spelling != row["canonical_key"]:
            raise RegistryIntegrityError(
                f"noncanonical case-fold alias spelling: {row}"
            )
        if row["deprecated_key"].casefold() != folded:
            raise RegistryIntegrityError(f"invalid case-fold alias row: {row}")
        identity = (
            row["object_path"],
            row["deprecated_key"],
            row["canonical_key"],
            row["value_sha256"],
        )
        if identity in identities:
            raise RegistryIntegrityError(f"duplicate case-fold alias custody row: {row}")
        identities.add(identity)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate or repair invariant loop-control registry metadata."
    )
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="Fail on integrity drift (default).")
    mode.add_argument("--write", action="store_true", help="Write the deterministic repair.")
    args = parser.parse_args()

    if args.write:
        original = load_registry(args.registry)
        repaired = repair_registry(original)
        original_bytes = args.registry.read_bytes()
        repaired_bytes = canonical_json_bytes(repaired)
        if original_bytes != repaired_bytes:
            atomic_write_registry(args.registry, repaired_bytes)
            print(
                "loop_control_registry_integrity: repaired "
                f"aliases={len(repaired['casefold_key_aliases_v0'])}"
            )
        else:
            print("loop_control_registry_integrity: already canonical")
        return 0

    original = load_registry(args.registry)
    try:
        validate_registry(original)
    except RegistryIntegrityError as error:
        print(f"loop_control_registry_integrity: FAILED {error}")
        return 1
    print(
        "loop_control_registry_integrity: OK "
        f"aliases={len(original['casefold_key_aliases_v0'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
