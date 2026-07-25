from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))


class InventoryError(ValueError):
    """Raised when pytest collection cannot produce one frozen node-id universe."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def collect_nodeids() -> list[str]:
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "pytest",
            "formal/python/tests",
            "--collect-only",
            "-q",
            "-p",
            "no:cacheprovider",
        ],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if completed.returncode != 0:
        raise InventoryError(
            "pytest collection failed:\n"
            + completed.stdout[-4000:]
            + completed.stderr[-4000:]
        )
    nodeids = [
        line.strip().replace("\\", "/")
        for line in completed.stdout.splitlines()
        if line.strip().startswith("formal/python/tests/") and "::" in line
    ]
    if not nodeids:
        raise InventoryError("pytest collection returned no node IDs")
    if len(nodeids) != len(set(nodeids)):
        raise InventoryError("pytest collection returned duplicate node IDs")
    return nodeids


def read_nodeids(path: Path) -> list[str]:
    rows = [line for line in path.read_text(encoding="utf-8").splitlines() if line]
    if not rows or len(rows) != len(set(rows)):
        raise InventoryError(f"invalid node-id inventory: {path}")
    return rows


def build_manifest(
    *,
    nodeids: list[str],
    frozen_nodeids: list[str],
    current_relative_to_commit: str,
    custody_path: str,
) -> tuple[dict[str, Any], bytes]:
    raw = ("\n".join(nodeids) + "\n").encode("utf-8")
    current = set(nodeids)
    frozen = set(frozen_nodeids)
    if not frozen <= current:
        missing = sorted(frozen - current)
        raise InventoryError(
            f"frozen comparability inventory is not a subset; missing={missing[:10]}"
        )
    manifest = {
        "schema_id": "CURRENT_ACCEPTANCE_INVENTORY_20260725_v2",
        "purpose": "COMPLETE_CURRENT_NON_LEAN_ACCEPTANCE_UNIVERSE",
        "current_relative_to_commit": current_relative_to_commit,
        "inventory_kind": "NON_LEAN_PYTEST_NODE_IDS",
        "count": len(nodeids),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "custody_path": custody_path,
        "collection": {
            "complete": True,
            "exit_code": 0,
            "duplicate_node_ids": 0,
            "frozen_comparability_common": len(frozen),
            "added_over_frozen_comparability": len(current - frozen),
            "removed_from_frozen_comparability": 0,
            "excluded_current_critical_guards": 0,
        },
        "lean_build_gate_files_excluded_for_separate_lean_profile": 9,
        "profile_status": "FROZEN_INPUT_TO_OBLIGATION_AND_EXECUTION_PROFILES",
        "acceptance_boundary": {
            "new_current_critical_guards_included": True,
            "membership_frozen_before_execution": True,
            "dynamic_demotion_permitted": False,
            "test_failure_may_change_profile": False,
            "every_exclusion_requires_review": True,
        },
    }
    return manifest, raw


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--frozen-inventory", type=Path, required=True)
    parser.add_argument("--custody-output", type=Path, required=True)
    parser.add_argument("--manifest-output", type=Path, required=True)
    parser.add_argument("--custody-path", required=True)
    parser.add_argument("--current-relative-to-commit", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    nodeids = collect_nodeids()
    frozen = read_nodeids(args.frozen_inventory.resolve())
    manifest, raw = build_manifest(
        nodeids=nodeids,
        frozen_nodeids=frozen,
        current_relative_to_commit=args.current_relative_to_commit,
        custody_path=args.custody_path,
    )
    manifest_raw = canonical_json_bytes(manifest)
    custody_output = args.custody_output.resolve()
    manifest_output = args.manifest_output.resolve()
    if args.check:
        if custody_output.read_bytes() != raw:
            raise InventoryError("current acceptance custody inventory drifted")
        if manifest_output.read_bytes() != manifest_raw:
            raise InventoryError("current acceptance manifest drifted")
    else:
        custody_output.parent.mkdir(parents=True, exist_ok=True)
        manifest_output.parent.mkdir(parents=True, exist_ok=True)
        custody_output.write_bytes(raw)
        manifest_output.write_bytes(manifest_raw)
    print(
        json.dumps(
            {
                "count": len(nodeids),
                "sha256": hashlib.sha256(raw).hexdigest(),
                "added_over_frozen": len(set(nodeids) - set(frozen)),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
