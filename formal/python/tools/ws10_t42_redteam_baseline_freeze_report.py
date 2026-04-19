from __future__ import annotations

import argparse
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T42_REDTEAM_BASELINE_FREEZE_REPORT_20260418_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json"
BLOCKER_DASHBOARD_PATH = REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json"
SEAM_LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json"
MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
ARCHITECTURE_SCHEMA_PATH = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
FROZEN_T42_RELEASE_SURFACE_FILE_COUNT = 910


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


def _git_short_head() -> str:
    try:
        result = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "rev-parse", "--short", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        )
        return result.stdout.strip() or "UNKNOWN"
    except Exception:
        return "UNKNOWN"


def _release_surface_file_count() -> int:
    return FROZEN_T42_RELEASE_SURFACE_FILE_COUNT


def _governance_surface_file_count() -> int:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
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
    return 0


def build_report(*, captured_at_utc: str | None = None, anchored_commit: str | None = None) -> dict[str, Any]:
    blocker_dashboard = _read_json(BLOCKER_DASHBOARD_PATH)
    seam_ledger = _read_json(SEAM_LEDGER_PATH)
    manifest = _read_json(MANIFEST_PATH)

    blocker_current = dict(blocker_dashboard.get("blocker_scoreboard", {}).get("current", {}))
    seam_summary = dict(seam_ledger.get("summary", {}))

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0",
        "status": "ACTIVE_REDTEAM_BASELINE_FREEZE_NONLIVE_v0",
        "anchored_commit": anchored_commit or _git_short_head(),
        "captured_at_utc": _ts(captured_at_utc),
        "baseline_metrics": {
            "release_surface_file_count": _release_surface_file_count(),
            "governance_surface_file_count": _governance_surface_file_count(),
            "governed_pytests_expected_count": int(
                manifest.get("groups", {}).get("governance_pytests", {}).get("expected_count", 0)
            ),
            "active_theorem_gap_count": int(blocker_current.get("THEOREM_GAP", 0)),
            "active_seam_gap_count": int(blocker_current.get("SEAM_INTEGRATION_GAP", 0)),
            "active_parity_drift_count": int(blocker_current.get("PARITY_DRIFT", 0)),
            "blocker_net_delta": int(blocker_dashboard.get("blocker_scoreboard", {}).get("net_delta", 0)),
            "blocker_movement_status": str(
                blocker_dashboard.get("blocker_scoreboard", {}).get("movement_status", "UNKNOWN")
            ),
            "seam_rows_total": int(seam_summary.get("seam_rows_total", 0)),
            "active_review_rows": int(seam_summary.get("active_review_rows", 0)),
            "external_hold_rows": int(seam_summary.get("external_hold_rows", 0)),
            "held_review_rows": int(seam_summary.get("held_review_rows", 0)),
        },
        "freeze_contract": {
            "primary_metrics": [
                "active_theorem_gap_count",
                "active_seam_gap_count",
                "blocker_net_delta",
            ],
            "release_surface_growth_rule": "NO_NEW_RELEASE_FAMILY_GROWTH_WITHOUT_RETIREMENT_OR_CANONICAL_BLOCKER_CLOSURE",
            "governed_pytest_growth_rule": "NO_NEW_GOVERNED_PYTEST_GROWTH_WITHOUT_MANIFEST_JUSTIFIED_RETIREMENT_OR_CANONICAL_BLOCKER_CLOSURE",
            "authority_residency_rule": "NO_NEW_DUPLICATED_AUTHORITY_RESIDENCY_WITHOUT_EXPLICIT_DECISION_ARTIFACT",
            "active_lane_rule": "ONLY_ONE_ACTIVE_SEAM_CAMPAIGN_PLUS_ONE_THEOREM_GAP_FAMILY_AT_A_TIME",
            "operator_pack_rule": "EXECUTION_REVIEW_MUST_READ_MATRIX_DASHBOARD_SEAM_SLA_ROADMAP_AND_INVENTORY_ONLY",
        },
        "invariance": {
            "release_gate_truth_invariance": "ENFORCED",
            "packet42_policy_invariance": "ENFORCED",
            "nonclaim_boundary_invariance": "ENFORCED",
            "scalar_freeze_policy_invariance": "ENFORCED",
        },
        "source_pointers": {
            "blocker_burn_dashboard": _ptr(BLOCKER_DASHBOARD_PATH),
            "seam_resolution_sla_ledger": _ptr(SEAM_LEDGER_PATH),
            "governance_manifest": _ptr(MANIFEST_PATH),
            "completion_matrix": _ptr(COMPLETION_MATRIX_PATH),
            "compact_state": _ptr(STATE_PATH),
            "roadmap": _ptr(ROADMAP_PATH),
            "inventory": _ptr(INVENTORY_PATH),
            "architecture_schema": _ptr(ARCHITECTURE_SCHEMA_PATH),
        },
        "summary": {
            "terminal_outcome": "REDTEAM_BASELINE_FREEZE_MATERIALIZED",
            "next_action": "START_PHASE2_CONSOLIDATION_WITH_ONE_GATE_FAMILY_AND_ONE_RELEASE_FAMILY_BASELINE",
            "single_executable_seam_reference": "SEAM-COSMO-SR",
            "blocked_seam_reference": "SEAM-QM-STAT",
            "external_hold_seam_reference": "SEAM-QFT-GR",
        },
        "non_claim_boundary": "This checkpoint is a repository-local remediation baseline and freeze artifact. It does not assert scientific adequacy, row promotion, or physics completion by itself.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T42 red-team baseline freeze checkpoint.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    args = parser.parse_args()

    report = build_report()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()