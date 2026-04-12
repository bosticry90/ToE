from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_CROSS_PLATFORM_PARITY_20260411_v0"
CI_PATH = REPO_ROOT / ".github" / "workflows" / "ci.yml"
MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
OBJECTIVE_MIN_PARITY_TESTS = 10


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    ci_text = _read(CI_PATH)
    manifest = _read_json(MANIFEST_PATH)
    groups = manifest.get("groups", {})

    critical_tests = groups.get("critical_gates", {}).get("tests", [])
    integrity_tests = groups.get("integrity_gates", {}).get("tests", [])
    parity_tests = list(critical_tests) + [t for t in integrity_tests if t not in set(critical_tests)]
    parity_scope_sha256 = hashlib.sha256("\n".join(parity_tests).encode("utf-8")).hexdigest()

    criteria = {
        "linux_parity_lane_present": "python-governance-linux-parity" in ci_text,
        "linux_lane_uses_ubuntu": "runs-on: ubuntu-latest" in ci_text,
        "linux_lane_resolves_critical_group": "governance_manifest_select --manifest formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json --group critical_gates" in ci_text,
        "linux_lane_resolves_integrity_group": "governance_manifest_select --manifest formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json --group integrity_gates" in ci_text,
        "linux_lane_executes_group_files": "xargs -a" in ci_text,
    }
    all_satisfied = all(criteria.values())

    objective_criteria = {
        "minimum_parity_test_surface_satisfied": len(parity_tests) >= OBJECTIVE_MIN_PARITY_TESTS,
        "manifest_group_uniqueness_satisfied": len(parity_tests) == len(set(parity_tests)),
        "parity_scope_hash_materialized": bool(parity_scope_sha256),
    }
    objective_all_satisfied = all(objective_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "critical_gates_count": len(critical_tests),
                "integrity_gates_count": len(integrity_tests),
                "parity_scope_count": len(parity_tests),
                "minimum_parity_tests_required": OBJECTIVE_MIN_PARITY_TESTS,
                "parity_scope_sha256": parity_scope_sha256,
            },
            "summary": {
                "all_criteria_satisfied": objective_all_satisfied,
                "phase_status": "COMPLETE" if objective_all_satisfied else "INCOMPLETE",
                "next_action": (
                    "PHASE_G_CLOSEOUT_AND_AUTHORITY_SYNC"
                    if objective_all_satisfied
                    else "EXPAND_LINUX_PARITY_SCOPE"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "phase_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": "PHASE_G_CLOSEOUT_AND_AUTHORITY_SYNC" if all_satisfied else "RESTORE_LINUX_PARITY_LANE",
        },
        "source_bundle": {
            "ci": _ptr(CI_PATH),
            "manifest": _ptr(MANIFEST_PATH),
        },
        "non_claim_boundary": "Repository-local cross-platform parity artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate governance cross-platform parity report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_cross_platform_parity_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"governance_cross_platform_parity_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
