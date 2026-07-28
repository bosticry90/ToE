from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_POINTER_PATH = (
    REPO_ROOT
    / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json"
)
LEAN_ROOT = REPO_ROOT / "formal/toe_formal"
WITNESS_PATH = "ToeFormal/Release/CurrentScientificAuthorityWitness.lean"
TARGET_PREFIX = "TOE_CURRENT_TARGET="
AUTHORITY_PREFIX = "TOE_CURRENT_AUTHORITY="
TARGET_GRAMMAR = re.compile(r"[a-z][a-z0-9_]*\Z")
SCIENTIFIC_TARGET_VERBS = frozenset(
    {
        "analyze",
        "authorize",
        "calculate",
        "claim",
        "close",
        "compute",
        "conduct",
        "construct",
        "derive",
        "execute",
        "prepare",
        "prove",
        "return",
        "review",
        "select",
    }
)


class AuthorityConsistencyError(RuntimeError):
    pass


def _validate_target_identifier(value: str, *, surface: str) -> None:
    if not value:
        raise AuthorityConsistencyError(f"{surface} target is empty")
    if TARGET_GRAMMAR.fullmatch(value) is None:
        raise AuthorityConsistencyError(
            f"{surface} target violates target grammar: {value!r}"
        )
    verb = value.split("_", 1)[0]
    if verb not in SCIENTIFIC_TARGET_VERBS:
        raise AuthorityConsistencyError(
            f"{surface} target has unknown target grammar verb: {verb!r}"
        )


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise AuthorityConsistencyError(f"expected JSON object: {path}")
    return value


def _exact_prefixed_value(output: str, prefix: str) -> str:
    values = [
        line[len(prefix) :].strip()
        for line in output.splitlines()
        if line.startswith(prefix)
    ]
    if not values:
        raise AuthorityConsistencyError(f"missing evaluated Lean value: {prefix}")
    if len(values) != 1:
        raise AuthorityConsistencyError(f"multiple evaluated Lean values: {prefix}")
    value = values[0]
    if not value:
        raise AuthorityConsistencyError(f"empty evaluated Lean value: {prefix}")
    _validate_target_identifier(value, surface="evaluated Lean")
    return value


def parse_witness_output(output: str) -> dict[str, str]:
    return {
        "lean_current_target": _exact_prefixed_value(output, TARGET_PREFIX),
        "lean_current_authority": _exact_prefixed_value(output, AUTHORITY_PREFIX),
    }


def evaluate_lean_witness() -> dict[str, str]:
    build = subprocess.run(
        [
            "lake",
            "--quiet",
            "--no-ansi",
            "build",
            "ToeFormal.Release.CurrentAuthority",
        ],
        cwd=LEAN_ROOT,
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if build.returncode != 0:
        raise AuthorityConsistencyError(
            "Lean current-authority build failed:\n" + build.stdout + build.stderr
        )
    completed = subprocess.run(
        ["lake", "env", "lean", "--run", WITNESS_PATH],
        cwd=LEAN_ROOT,
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if completed.returncode != 0:
        raise AuthorityConsistencyError(
            "Lean authority witness failed:\n"
            + completed.stdout
            + completed.stderr
        )
    return parse_witness_output(completed.stdout)


def build_report(*, witness: dict[str, str] | None = None) -> dict[str, Any]:
    registry = _read_json(REGISTRY_PATH)
    pointer = _read_json(MAINTENANCE_POINTER_PATH)
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise AuthorityConsistencyError("registry current projection missing")
    registry_target = projection.get("current_target")
    registry_kind = projection.get("current_target_kind")
    if not isinstance(registry_target, str) or not registry_target:
        raise AuthorityConsistencyError("registry target missing or empty")
    _validate_target_identifier(registry_target, surface="registry")
    if not isinstance(registry_kind, str) or not registry_kind:
        raise AuthorityConsistencyError("registry target kind missing or empty")

    observed = witness if witness is not None else evaluate_lean_witness()
    lean_target = observed.get("lean_current_target")
    lean_authority = observed.get("lean_current_authority")
    if not isinstance(lean_target, str) or not isinstance(lean_authority, str):
        raise AuthorityConsistencyError("evaluated Lean witness is incomplete")
    _validate_target_identifier(lean_target, surface="CurrentTarget")
    _validate_target_identifier(lean_authority, surface="CurrentAuthority")

    maintenance_target = pointer.get("current_maintenance_target")
    if not isinstance(maintenance_target, str) or not maintenance_target:
        raise AuthorityConsistencyError("maintenance target pointer is missing")
    if registry_target == maintenance_target:
        raise AuthorityConsistencyError(
            "maintenance target appears in scientific target field"
        )
    if not (registry_target == lean_target == lean_authority):
        raise AuthorityConsistencyError(
            "scientific authority mismatch: "
            f"registry={registry_target!r} "
            f"current_target={lean_target!r} "
            f"current_authority={lean_authority!r}"
        )

    return {
        "schema_id": "TOE_CURRENT_SCIENTIFIC_AUTHORITY_CONSISTENCY_REPORT_v0",
        "status": "PASS",
        "registry_target": registry_target,
        "registry_target_kind": registry_kind,
        "lean_current_target": lean_target,
        "lean_current_authority": lean_authority,
        "maintenance_target": maintenance_target,
        "all_scientific_values_equal": True,
        "maintenance_target_separate": True,
        "authority_discovery": "EVALUATED_NAMED_LEAN_VALUES_NOT_PREFIX_SOURCE_SCAN",
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compare canonical registry and evaluated Lean authority values."
    )
    parser.add_argument("--check", action="store_true")
    parser.parse_args()
    try:
        report = build_report()
    except AuthorityConsistencyError as exc:
        print(f"current scientific authority consistency FAIL: {exc}")
        return 1
    print(
        "current scientific authority consistency OK "
        f"target={report['registry_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
