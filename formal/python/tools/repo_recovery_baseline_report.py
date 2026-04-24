from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "REPO_RECOVERY_BASELINE_REPORT_20260423_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "repo_recovery_baseline_20260423_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
BLOCKER_DASHBOARD_PATH = REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json"
SEAM_LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json"
ARCHITECTURE_SCHEMA_PATH = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"
PYTEST_LASTFAILED_PATH = REPO_ROOT / ".pytest_cache" / "v" / "cache" / "lastfailed"

AUDITED_FULL_PYTEST = {
    "date": "2026-04-23",
    "command": "./py.ps1 -m pytest formal/python/tests -q",
    "failures": 84,
    "passes": 6113,
    "skips": 202,
    "status": "RED",
}


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _governance_doc_count(schema: dict[str, Any]) -> int:
    inventory = schema.get("governance_surface_inventory", {}).get("governance_docs")
    docs: set[str] = set()
    if isinstance(inventory, dict):
        for rel_path in inventory.get("fixed_files", []):
            path = REPO_ROOT / rel_path
            if path.exists():
                docs.add(str(path.relative_to(REPO_ROOT)))
        for pattern in inventory.get("glob_patterns", []):
            for path in REPO_ROOT.glob(pattern):
                if path.is_file():
                    docs.add(str(path.relative_to(REPO_ROOT)))
    return len(docs)


def _latest_governance_lock_path() -> Path:
    versioned: list[tuple[int, Path]] = []
    for path in REPO_ROOT.glob("GOVERNANCE_VERSION_v*.lock"):
        match = re.fullmatch(r"GOVERNANCE_VERSION_v(\d+)\.lock", path.name)
        if match is None:
            continue
        versioned.append((int(match.group(1)), path))
    if not versioned:
        raise FileNotFoundError("Missing governance lock file (expected GOVERNANCE_VERSION_v*.lock).")
    versioned.sort()
    return versioned[-1][1]


def _current_cycle_from_state() -> int:
    matches = re.findall(r"\bCYCLE[-_]?(\d+)\b", _read_text(STATE_PATH), flags=re.IGNORECASE)
    if not matches:
        return 0
    return max(int(value) for value in matches)


def _governance_growth_status(schema: dict[str, Any]) -> dict[str, Any]:
    lock = _read_json(_latest_governance_lock_path())
    growth_policy = schema["growth_policy"]
    baseline_cycle = int(growth_policy["baseline_cycle"])
    max_delta_per_cycle = growth_policy["max_delta_per_cycle"]
    baseline_counts = lock["baseline"]["governance_surface_counts"]
    current_cycle = _current_cycle_from_state()
    cycles_elapsed = max(0, current_cycle - baseline_cycle)

    observed_docs = _governance_doc_count(schema)
    baseline_docs = int(baseline_counts["governance_docs"])
    allowed_docs = baseline_docs + int(max_delta_per_cycle["governance_docs"]) * cycles_elapsed
    growth_breach = observed_docs > allowed_docs

    return {
        "baseline_cycle": baseline_cycle,
        "current_cycle": current_cycle,
        "cycles_elapsed": cycles_elapsed,
        "governance_docs_observed": observed_docs,
        "governance_docs_allowed": allowed_docs,
        "governance_docs_baseline": baseline_docs,
        "breach_detected": growth_breach,
        "breach_amount": max(0, observed_docs - allowed_docs),
        "policy_reference": _ptr(ARCHITECTURE_SCHEMA_PATH),
    }


def _lastfailed_snapshot() -> dict[str, Any]:
    if not PYTEST_LASTFAILED_PATH.exists():
        return {
            "path": _ptr(PYTEST_LASTFAILED_PATH),
            "entry_count": 0,
            "top_prefixes": {},
            "sample": [],
        }

    payload = json.loads(_read_text(PYTEST_LASTFAILED_PATH))
    nodeids = sorted(payload.keys())
    prefixes = Counter()
    for nodeid in nodeids:
        stem = Path(nodeid.split("::", 1)[0]).stem
        parts = stem.split("_")
        prefix = parts[1] if len(parts) > 1 else stem
        prefixes[prefix] += 1
    return {
        "path": _ptr(PYTEST_LASTFAILED_PATH),
        "entry_count": len(nodeids),
        "top_prefixes": dict(prefixes.most_common(10)),
        "sample": nodeids[:25],
    }


def _forbidden_nested_active_paths() -> list[str]:
    nested_root = REPO_ROOT / "formal" / "formal"
    if not nested_root.exists():
        return []
    return [
        _ptr(path)
        for path in sorted(nested_root.rglob("*"))
        if path.is_file()
    ]


def build_report(
    *,
    captured_at_utc: str | None = None,
    lastfailed_snapshot: dict[str, Any] | None = None,
) -> dict[str, Any]:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    manifest = _read_json(MANIFEST_PATH)
    blocker_dashboard = _read_json(BLOCKER_DASHBOARD_PATH)
    seam_ledger = _read_json(SEAM_LEDGER_PATH)
    blocker_current = blocker_dashboard.get("blocker_scoreboard", {}).get("current", {})
    seam_summary = seam_ledger.get("summary", {})
    lastfailed = lastfailed_snapshot or _lastfailed_snapshot()
    forbidden_nested = _forbidden_nested_active_paths()
    growth = _governance_growth_status(schema)

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "repo_recovery_baseline_20260423_v0",
        "status": "ACTIVE_STABILIZATION_AND_THROUGHPUT_RESET_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "canonical_authority_surfaces": [
            "State_of_the_Theory.md",
            "ARCHITECTURE_SCHEMA_v1.json",
            "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json",
            "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        ],
        "baseline_metrics": {
            "governed_pytests_expected_count": int(
                manifest.get("groups", {}).get("governance_pytests", {}).get("expected_count", 0)
            ),
            "governance_manifest_listed_count": len(
                manifest.get("groups", {}).get("governance_pytests", {}).get("tests", [])
            ),
            "active_theorem_gap_count": int(blocker_current.get("THEOREM_GAP", 0)),
            "active_seam_gap_count": int(blocker_current.get("SEAM_INTEGRATION_GAP", 0)),
            "active_parity_drift_count": int(blocker_current.get("PARITY_DRIFT", 0)),
            "blocker_net_delta": int(blocker_dashboard.get("blocker_scoreboard", {}).get("net_delta", 0)),
            "blocker_movement_status": blocker_dashboard.get("blocker_scoreboard", {}).get("movement_status", "UNKNOWN"),
            "seam_rows_total": int(seam_summary.get("seam_rows_total", 0)),
            "active_review_rows": int(seam_summary.get("active_review_rows", 0)),
            "external_hold_rows": int(seam_summary.get("external_hold_rows", 0)),
            "forbidden_nested_active_path_count": len(forbidden_nested),
        },
        "branch_health_baseline": {
            **AUDITED_FULL_PYTEST,
            "lastfailed_snapshot": lastfailed,
        },
        "governance_growth_budget": growth,
        "freeze_contract": {
            "release_surface_growth_rule": "NO_NEW_RELEASE_FAMILY_DOCS_UNTIL_FULL_SUITE_GREEN_OR_EQUAL_RETIREMENT",
            "governed_pytest_growth_rule": "NO_NEW_GOVERNED_PYTESTS_UNTIL_FULL_SUITE_GREEN_OR_EQUAL_RETIREMENT",
            "duplicated_status_surface_rule": "NO_NEW_DUPLICATED_STATUS_SURFACES_OR_MANUAL_PARITY_COPIES",
            "active_lane_rule": "ONLY_ONE_ACTIVE_SEAM_CAMPAIGN_PLUS_ONE_THEOREM_GAP_FAMILY_AT_A_TIME",
            "advancement_contract": "ADVANCEMENT_REQUIRES_BLOCKER_REDUCTION_WITH_GREEN_FULL_SUITE_AND_NO_GOVERNANCE_GROWTH",
        },
        "active_lane_order": {
            "primary_executable_seam": "SEAM-COSMO-SR",
            "primary_theorem_gap_family": "ONE_ACTIVE_THEOREM_GAP_FAMILY_ONLY",
            "blocked_seam": "SEAM-QM-STAT",
            "external_hold_seam": "SEAM-QFT-GR",
        },
        "acceptance_gates": {
            "governance_lane": "pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1",
            "branch_health_lane": "./py.ps1 -m pytest formal/python/tests -q",
            "lean_lane": "cd formal/toe_formal && lake build",
            "rust_lane": "cargo run --manifest-path formal/rust/toe_trust_core/Cargo.toml",
        },
        "source_bundle": {
            "state_surface": _ptr(STATE_PATH),
            "roadmap_surface": _ptr(ROADMAP_PATH),
            "governance_manifest": _ptr(MANIFEST_PATH),
            "blocker_dashboard": _ptr(BLOCKER_DASHBOARD_PATH),
            "seam_resolution_sla_ledger": _ptr(SEAM_LEDGER_PATH),
            "architecture_schema": _ptr(ARCHITECTURE_SCHEMA_PATH),
        },
        "forbidden_nested_active_paths": forbidden_nested,
        "non_claim_boundary": "This baseline captures repository recovery posture only. It does not assert physics completion, theorem discharge, or promotion readiness.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate the repo recovery baseline report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    ns = parser.parse_args(argv)

    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        "repo_recovery_baseline_report: "
        f"status={payload['status']} "
        f"theorem_gap={payload['baseline_metrics']['active_theorem_gap_count']} "
        f"seam_gap={payload['baseline_metrics']['active_seam_gap_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
