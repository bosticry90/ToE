"""Execute the single authorized duplicate-selector deletion exactly once."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from governance_json import (
    forensic_historical_parse_bytes,
    strict_current_authority_loads,
)


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BOOTSTRAP = (
    ROOT
    / "formal"
    / "docs"
    / "release"
    / "MAINTENANCE_AUTHORITY_DUPLICATE_SELECTOR_KEY_REPAIR_BOOTSTRAP_20260725_v0.json"
)


class BootstrapRepairError(RuntimeError):
    """The one-time authority repair does not match its frozen authorization."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        .encode("utf-8")
        + b"\n"
    )


def load_bootstrap(path: Path = DEFAULT_BOOTSTRAP) -> dict[str, Any]:
    payload = strict_current_authority_loads(path.read_bytes())
    if payload.get("schema_id") != (
        "MAINTENANCE_AUTHORITY_DUPLICATE_SELECTOR_KEY_REPAIR_BOOTSTRAP_20260725_v0"
    ):
        raise BootstrapRepairError("unexpected bootstrap schema")
    return payload


def validate_repair_bytes(
    raw: bytes,
    bootstrap: dict[str, Any],
    *,
    tool_bytes: bytes,
) -> tuple[bytes, dict[str, Any]]:
    target = bootstrap["target"]
    tool = bootstrap["authorized_implementation_tool"]
    if bootstrap.get("execution_counter") != 1:
        raise BootstrapRepairError("bootstrap execution counter is not exactly one")
    if bootstrap.get("expiration_condition") != (
        "EXPIRES_IMMEDIATELY_AFTER_ONE_SUCCESSFUL_EXECUTION"
    ):
        raise BootstrapRepairError("bootstrap expiration condition is invalid")
    if sha256_bytes(tool_bytes) != tool["sha256"]:
        raise BootstrapRepairError("authorized implementation tool hash mismatch")
    if sha256_bytes(raw) != target["before_sha256"]:
        raise BootstrapRepairError("authority document before-hash mismatch")

    forensic = forensic_historical_parse_bytes(raw)
    duplicates = [
        item
        for item in forensic.duplicates
        if item["json_path"] == "$" and item["key"] == "selector"
    ]
    if len(duplicates) != 1 or duplicates[0]["occurrences"] != 2:
        raise BootstrapRepairError("expected exactly two top-level selector members")

    deletion = target["permitted_deletion"]
    start = deletion["start_byte"]
    end = deletion["end_byte_exclusive"]
    removed = raw[start:end]
    if sha256_bytes(removed) != deletion["sha256"]:
        raise BootstrapRepairError("permitted deletion bytes do not match bootstrap")
    repaired = raw[:start] + raw[end:]
    if sha256_bytes(repaired) != target["expected_after_sha256"]:
        raise BootstrapRepairError("repaired authority hash does not match bootstrap")
    if len(repaired) != target["expected_after_bytes"]:
        raise BootstrapRepairError("repaired authority size does not match bootstrap")

    parsed = strict_current_authority_loads(repaired)
    if parsed.get("selector") != bootstrap["authorized_second_selector_value"]:
        raise BootstrapRepairError("surviving selector is not the authorized value")
    if repaired[:start] != raw[:start] or repaired[start:] != raw[end:]:
        raise BootstrapRepairError("repair changed bytes outside the deletion range")
    return repaired, {
        "before_sha256": sha256_bytes(raw),
        "after_sha256": sha256_bytes(repaired),
        "removed_sha256": sha256_bytes(removed),
        "removed_bytes": len(removed),
        "strict_parse": "PASS",
        "top_level_selector_members_after": 1,
    }


def _git(*args: str, repo_root: Path) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if completed.returncode != 0:
        raise BootstrapRepairError(
            f"git {' '.join(args)} failed: {completed.stderr.strip()}"
        )
    return completed.stdout.strip()


def execute_once(
    *,
    repo_root: Path = ROOT,
    bootstrap_path: Path = DEFAULT_BOOTSTRAP,
) -> dict[str, Any]:
    bootstrap = load_bootstrap(bootstrap_path)
    parent = bootstrap["parent_recovery_state"]
    if _git("rev-parse", "HEAD", repo_root=repo_root) != parent["commit"]:
        raise BootstrapRepairError("HEAD is not the authorized parent commit")
    if _git("show", "-s", "--format=%T", "HEAD", repo_root=repo_root) != parent["tree"]:
        raise BootstrapRepairError("HEAD tree is not the authorized parent tree")

    target_path = repo_root / bootstrap["target"]["path"]
    tool_path = repo_root / bootstrap["authorized_implementation_tool"]["path"]
    consumption_path = repo_root / bootstrap["consumption_record"]["path"]
    if consumption_path.exists():
        raise BootstrapRepairError("bootstrap authority has already been consumed")

    bootstrap_raw = bootstrap_path.read_bytes()
    repaired, evidence = validate_repair_bytes(
        target_path.read_bytes(),
        bootstrap,
        tool_bytes=tool_path.read_bytes(),
    )
    target_path.write_bytes(repaired)
    consumption = {
        "schema_id": (
            "MAINTENANCE_AUTHORITY_DUPLICATE_SELECTOR_KEY_REPAIR_"
            "BOOTSTRAP_CONSUMPTION_20260725_v0"
        ),
        "captured_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "bootstrap": {
            "path": str(bootstrap_path.relative_to(repo_root)).replace("\\", "/"),
            "sha256": sha256_bytes(bootstrap_raw),
        },
        "authorized_parent": parent,
        "execution_counter_consumed": 1,
        "execution": evidence,
        "exceptional_bootstrap_authority_after_execution": "PERMANENTLY_EXPIRED",
        "scientific_posture": "B-BLOCKED",
        "v2_enrollment": "NOT_AUTHORIZED",
        "scientific_resumption": "NOT_AUTHORIZED",
    }
    consumption_path.write_bytes(canonical_json_bytes(consumption))
    return consumption


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--bootstrap", type=Path, default=DEFAULT_BOOTSTRAP)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--execute", action="store_true")
    args = parser.parse_args()
    if args.check == args.execute:
        raise BootstrapRepairError("choose exactly one of --check or --execute")
    bootstrap = load_bootstrap(args.bootstrap)
    target_path = args.repo_root / bootstrap["target"]["path"]
    tool_path = args.repo_root / bootstrap["authorized_implementation_tool"]["path"]
    if args.check:
        _, evidence = validate_repair_bytes(
            target_path.read_bytes(),
            bootstrap,
            tool_bytes=tool_path.read_bytes(),
        )
        print(json.dumps(evidence, indent=2, sort_keys=True))
        return 0
    consumption = execute_once(
        repo_root=args.repo_root.resolve(),
        bootstrap_path=args.bootstrap.resolve(),
    )
    print(json.dumps(consumption, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
