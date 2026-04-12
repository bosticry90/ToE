from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import governance_manifest_select as selector


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION_20260411_v0"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"
MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"


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


def _sha256_joined(items: list[str]) -> str:
    return hashlib.sha256("\n".join(items).encode("utf-8")).hexdigest()


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    suite_text = _read(SUITE_PATH)
    manifest = _read_json(MANIFEST_PATH)

    tests, expected_count, expected_sha, _ = selector.load_manifest_tests(
        MANIFEST_PATH, "governance_pytests"
    )
    observed_count = len(tests)
    observed_sha = _sha256_joined(tests)
    manifest_group_tests = list(manifest.get("groups", {}).get("governance_pytests", {}).get("tests", []))

    criteria = {
        "legacy_text_registry_removed": "$governanceGateTokenRegistry" not in suite_text,
        "suite_declares_manifest_authority": "manifest-authoritative only" in suite_text,
        "suite_uses_manifest_selector": "governance_manifest_select" in suite_text,
        "suite_resolves_required_manifest_groups": (
            'Resolve-GovernanceManifestGroup -Group $governanceManifestGroup -EnforceExpected' in suite_text
            and 'Resolve-GovernanceManifestGroup -Group "critical_gates"' in suite_text
            and 'Resolve-GovernanceManifestGroup -Group "integrity_gates"' in suite_text
        ),
    }
    all_satisfied = all(criteria.values())

    objective_criteria = {
        "selector_count_matches_manifest_expected": expected_count is not None and observed_count == expected_count,
        "selector_hash_matches_manifest_expected": expected_sha is not None and observed_sha == expected_sha,
        "manifest_group_equals_selector_output": manifest_group_tests == tests,
        "selector_output_has_no_duplicates": observed_count == len(set(tests)),
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
                "expected_count": expected_count,
                "observed_count": observed_count,
                "expected_sha256": expected_sha,
                "observed_sha256": observed_sha,
            },
            "summary": {
                "all_criteria_satisfied": objective_all_satisfied,
                "phase_status": "COMPLETE" if objective_all_satisfied else "INCOMPLETE",
                "next_action": (
                    "PHASE_E_SCALE_OBSERVABILITY_AND_COST_CONTROL"
                    if objective_all_satisfied
                    else "RESTORE_MANIFEST_SINGLE_SOURCE_PARITY"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "phase_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": "PHASE_E_SCALE_OBSERVABILITY_AND_COST_CONTROL" if all_satisfied else "REMOVE_SECONDARY_TEST_REGISTRY",
        },
        "source_bundle": {
            "governance_suite": _ptr(SUITE_PATH),
            "manifest": _ptr(MANIFEST_PATH),
        },
        "non_claim_boundary": "Repository-local governance single-source consolidation artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate governance single-source consolidation report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_single_source_consolidation_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"governance_single_source_consolidation_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
