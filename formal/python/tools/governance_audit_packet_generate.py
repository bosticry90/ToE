from __future__ import annotations

import argparse
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_AUDIT_PACKET_20260410_v0"

CONVERGENCE_BASELINE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "convergence_baseline_pack_20260409_v0.json"
GLOBAL_COMPLETION_BASELINE_PATH = REPO_ROOT / "formal" / "output" / "ws10_global_completion_baseline_snapshot_20260408_v0.json"
BLOCKER_BURN_REVIEW_PATH = REPO_ROOT / "formal" / "output" / "ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json"
COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
SEAM_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
ARTIFACT_LIFECYCLE_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "ARTIFACT_LIFECYCLE_POLICY_20260410_v0.json"
ARTIFACT_LIFECYCLE_POLICY_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "ARTIFACT_LIFECYCLE_POLICY_20260410_v0.md"
CLOSURE_OWNER_MAP_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json"
BLOCKER_CLOSURE_MAP_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_BLOCKER_CLOSURE_MAP_20260410_v0.md"
BLOCKER_CLOSURE_MAP_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
PROMOTION_READINESS_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0.md"
PROMOTION_READINESS_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_promotion_readiness_score_20260410_v0.json"
PROMOTION_ACTION_POLICY_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_PROMOTION_READINESS_ACTION_20260410_v0.md"
PROMOTION_ACTION_POLICY_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_promotion_readiness_action_20260410_v0.json"
GOVERNANCE_RUNTIME_BASELINE_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_RUNTIME_BASELINE_20260410_v0.md"
GOVERNANCE_RUNTIME_BASELINE_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_runtime_baseline_20260410_v0.json"
GOVERNANCE_ARTIFACT_GROWTH_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_ARTIFACT_GROWTH_BASELINE_20260410_v0.md"
GOVERNANCE_ARTIFACT_GROWTH_BASELINE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_artifact_growth_baseline_20260410_v0.json"
GOVERNANCE_ARTIFACT_GROWTH_SNAPSHOT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_artifact_growth_snapshot_20260410_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _count_json_files(path: Path) -> int:
    if not path.exists():
        return 0
    return sum(1 for candidate in path.rglob("*.json") if candidate.is_file())


def _parse_completion_rows(matrix_path: Path) -> list[dict[str, str]]:
    if not matrix_path.exists():
        raise FileNotFoundError(f"Missing required file: {matrix_path}")

    rows: list[dict[str, str]] = []
    for line in matrix_path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| ROW-"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) < 8:
            continue
        rows.append(
            {
                "row_id": cells[0],
                "domain": cells[1],
                "lane": cells[2],
                "current_status": cells[3],
                "blocker_class": cells[4],
                "primary_target": cells[5],
                "primary_artifact": cells[6],
                "primary_gate": cells[7],
            }
        )
    return rows


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _owner_rows_by_id(owner_map: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = owner_map.get("rows", [])
    if not isinstance(rows, list):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for entry in rows:
        if not isinstance(entry, dict):
            continue
        row_id = str(entry.get("row_id", "")).strip()
        if not row_id:
            continue
        out[row_id] = entry
    return out


def build_packet(
    *,
    output_path: Path,
    captured_at_utc: str | None,
    branch_health_runtime_seconds: float | None,
    governance_budget_warn_seconds: float,
    governance_budget_hard_seconds: float,
    branch_budget_warn_seconds: float,
    branch_budget_hard_seconds: float,
) -> dict[str, Any]:
    convergence = _read_json(CONVERGENCE_BASELINE_PATH)
    completion_baseline = _read_json(GLOBAL_COMPLETION_BASELINE_PATH)
    blocker_review = _read_json(BLOCKER_BURN_REVIEW_PATH)
    completion_rows = _parse_completion_rows(COMPLETION_MATRIX_PATH)
    lifecycle_policy = _read_json(ARTIFACT_LIFECYCLE_POLICY_PATH)
    closure_owner_map = _read_json(CLOSURE_OWNER_MAP_PATH)
    blocker_closure_map = _read_json(BLOCKER_CLOSURE_MAP_REPORT_PATH)
    promotion_readiness = _read_json(PROMOTION_READINESS_REPORT_PATH)
    promotion_action_policy = _read_json(PROMOTION_ACTION_POLICY_REPORT_PATH)
    runtime_baseline = _read_json(GOVERNANCE_RUNTIME_BASELINE_REPORT_PATH)
    artifact_growth_baseline = _read_json(GOVERNANCE_ARTIFACT_GROWTH_BASELINE_PATH)
    artifact_growth_snapshot = _read_json(GOVERNANCE_ARTIFACT_GROWTH_SNAPSHOT_PATH)

    blocker_current = (
        blocker_review.get("blocker_counts", {}).get("current", {})
        if isinstance(blocker_review.get("blocker_counts", {}), dict)
        else {}
    )

    row_blockers = Counter(row["blocker_class"] for row in completion_rows)
    unresolved_classes = [k for k, v in blocker_current.items() if isinstance(v, int) and v > 0]
    owner_rows = _owner_rows_by_id(closure_owner_map)
    missing_owner_rows = sorted(
        [row["row_id"] for row in completion_rows if row["row_id"] not in owner_rows]
    )
    owner_assignments = []
    for row in completion_rows:
        owner_row = owner_rows.get(row["row_id"], {})
        owner_assignments.append(
            {
                "row_id": row["row_id"],
                "blocker_class": row["blocker_class"],
                "primary_owner": owner_row.get("primary_owner"),
                "secondary_owner": owner_row.get("secondary_owner"),
                "required_evidence_surface": owner_row.get("required_evidence_surface"),
                "exit_criterion": owner_row.get("exit_criterion"),
            }
        )

    blocker_closure_rows = blocker_closure_map.get("mappings", [])
    if not isinstance(blocker_closure_rows, list):
        blocker_closure_rows = []

    runtime_governance = (
        completion_baseline.get("governance_prerequisite", {}).get("duration_seconds")
        if isinstance(completion_baseline.get("governance_prerequisite", {}), dict)
        else None
    )
    runtime_seconds = runtime_baseline.get("runtime_seconds", {})
    if not isinstance(runtime_seconds, dict):
        runtime_seconds = {}
    governance_suite_runtime = runtime_seconds.get("governance_suite", runtime_governance)
    branch_health_runtime = runtime_seconds.get("branch_health_full_pytest", branch_health_runtime_seconds)
    checkpoint_ladder_runtime = runtime_seconds.get("checkpoint_ladder")

    family_rules = lifecycle_policy.get("family_rules", [])
    if not isinstance(family_rules, list):
        family_rules = []
    family_rules_missing_archive = 0
    for rule in family_rules:
        if not isinstance(rule, dict):
            family_rules_missing_archive += 1
            continue
        archive_destination = str(rule.get("archive_destination", "")).strip()
        if not archive_destination:
            family_rules_missing_archive += 1

    growth_current = artifact_growth_snapshot.get("current_counts", {})
    if not isinstance(growth_current, dict):
        growth_current = {}
    growth_delta = artifact_growth_snapshot.get("delta_vs_baseline", {})
    if not isinstance(growth_delta, dict):
        growth_delta = {}
    growth_baseline = artifact_growth_baseline.get("baseline_counts", {})
    if not isinstance(growth_baseline, dict):
        growth_baseline = {}

    current_output_count = int(growth_current.get("json_files_under_formal_output", _count_json_files(REPO_ROOT / "formal" / "output")))
    current_reports_count = int(growth_current.get("json_files_under_formal_output_reports", _count_json_files(REPO_ROOT / "formal" / "output" / "reports")))

    packet = {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "throughput_dimensions": {
            "artifact_growth": {
                "assessment": "HIGH_ACTIVITY_SURFACE",
                "governance_decision_role": "CONTEXT_ONLY",
            },
            "evidence_growth": {
                "assessment": "MIXED",
                "governance_decision_role": "SECONDARY_GATE",
            },
            "closure_growth": {
                "assessment": "MIXED_BLOCKER_CONSTRAINED",
                "governance_decision_role": "PRIMARY_GATE",
            },
        },
        "runtime_baselines": {
            "declaration_pointer": str(GOVERNANCE_RUNTIME_BASELINE_DECLARATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "report_pointer": str(GOVERNANCE_RUNTIME_BASELINE_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "governance_suite_seconds_baseline": governance_suite_runtime,
            "branch_health_full_pytest_seconds_baseline": branch_health_runtime,
            "branch_health_pytest_seconds_baseline": branch_health_runtime,
            "checkpoint_ladder_seconds_baseline": checkpoint_ladder_runtime,
            "budget_policy": {
                "governance_warn_seconds": governance_budget_warn_seconds,
                "governance_hard_seconds": governance_budget_hard_seconds,
                "branch_health_warn_seconds": branch_budget_warn_seconds,
                "branch_health_hard_seconds": branch_budget_hard_seconds,
            },
        },
        "artifact_snapshot": {
            "json_files_under_formal_output": current_output_count,
            "json_files_under_formal_output_reports": current_reports_count,
            "baseline_checkpoint_count": convergence.get("required_metrics", {})
            .get("checkpoint_count", {})
            .get("value"),
        },
        "artifact_growth_tracking": {
            "declaration_pointer": str(GOVERNANCE_ARTIFACT_GROWTH_DECLARATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "baseline_report_pointer": str(GOVERNANCE_ARTIFACT_GROWTH_BASELINE_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "snapshot_report_pointer": str(GOVERNANCE_ARTIFACT_GROWTH_SNAPSHOT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "baseline_counts": {
                "json_files_under_formal_output": int(growth_baseline.get("json_files_under_formal_output", 0)),
                "json_files_under_formal_output_reports": int(growth_baseline.get("json_files_under_formal_output_reports", 0)),
            },
            "current_counts": {
                "json_files_under_formal_output": current_output_count,
                "json_files_under_formal_output_reports": current_reports_count,
            },
            "delta_vs_baseline": {
                "json_files_under_formal_output": int(growth_delta.get("json_files_under_formal_output", 0)),
                "json_files_under_formal_output_reports": int(growth_delta.get("json_files_under_formal_output_reports", 0)),
            },
        },
        "artifact_lifecycle_policy": {
            "declaration_pointer": str(ARTIFACT_LIFECYCLE_POLICY_DECLARATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "policy_pointer": str(ARTIFACT_LIFECYCLE_POLICY_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "retention_policy": lifecycle_policy.get("retention_policy", {}),
            "family_rules_count": len(family_rules),
            "family_rules_missing_archive_destination_count": family_rules_missing_archive,
            "exemption_classes": lifecycle_policy.get("exemption_classes", []),
        },
        "closure_map": {
            "blocker_count_by_class": blocker_current,
            "rows_total": len(completion_rows),
            "rows_by_blocker_class": dict(sorted(row_blockers.items())),
            "unresolved_blocker_classes": sorted(unresolved_classes),
            "blocker_to_closure_map": {
                "declaration_pointer": str(BLOCKER_CLOSURE_MAP_DECLARATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
                "report_pointer": str(BLOCKER_CLOSURE_MAP_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
                "rows_total": int(blocker_closure_map.get("rows_total", len(blocker_closure_rows))),
                "missing_owner_rows": blocker_closure_map.get("missing_owner_rows", []),
                "mappings": blocker_closure_rows,
            },
            "row_owner_assignments": owner_assignments,
            "owner_assignment_coverage": {
                "mapped_rows": len(completion_rows) - len(missing_owner_rows),
                "missing_rows": missing_owner_rows,
                "coverage_ratio": round((len(completion_rows) - len(missing_owner_rows)) / len(completion_rows), 6)
                if completion_rows
                else 0.0,
                "owner_map_pointer": str(CLOSURE_OWNER_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            },
            "source_matrix": str(COMPLETION_MATRIX_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "seam_inventory_pointer": str(SEAM_INVENTORY_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "promotion_readiness": {
            "declaration_pointer": str(PROMOTION_READINESS_DECLARATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "report_pointer": str(PROMOTION_READINESS_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "readiness_score_0_to_100": promotion_readiness.get("score", {}).get("readiness_score_0_to_100"),
            "readiness_status": promotion_readiness.get("score", {}).get("readiness_status"),
            "status_rule": promotion_readiness.get("score", {}).get("status_rule"),
            "components": promotion_readiness.get("components", {}),
        },
        "promotion_action_policy": {
            "declaration_pointer": str(PROMOTION_ACTION_POLICY_DECLARATION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "report_pointer": str(PROMOTION_ACTION_POLICY_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "readiness_input": promotion_action_policy.get("readiness_input", {}),
            "current_action": promotion_action_policy.get("current_action", {}),
            "status_action_rules": promotion_action_policy.get("status_action_rules", {}),
        },
        "risk_delta_rubric": {
            "required_axes": [
                "runtime_budget_delta",
                "artifact_growth_delta",
                "evidence_growth_delta",
                "closure_growth_delta",
            ],
            "rule": "NO_PHASE_LEVEL_IMPROVEMENT_CLAIM_WITHOUT_EXPLICIT_CLOSURE_GROWTH_DELTA",
        },
        "source_bundle": {
            "convergence_baseline_pack": str(CONVERGENCE_BASELINE_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "global_completion_baseline": str(GLOBAL_COMPLETION_BASELINE_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "blocker_burn_review": str(BLOCKER_BURN_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "non_claim_boundary": "This packet is a repository-local governance control artifact and does not assert scientific adequacy.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate governance audit packet with runtime and closure-map baselines.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_audit_packet_20260410_v0.json",
        help="Output path for the governance audit packet JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override (e.g. 2026-04-10T00:00:00Z).",
    )
    parser.add_argument(
        "--branch-health-runtime-seconds",
        type=float,
        default=None,
        help="Optional branch-health pytest runtime baseline in seconds.",
    )
    parser.add_argument("--governance-budget-warn-seconds", type=float, default=300.0)
    parser.add_argument("--governance-budget-hard-seconds", type=float, default=600.0)
    parser.add_argument("--branch-health-budget-warn-seconds", type=float, default=900.0)
    parser.add_argument("--branch-health-budget-hard-seconds", type=float, default=1800.0)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    packet = build_packet(
        output_path=output_path,
        captured_at_utc=ns.captured_at_utc,
        branch_health_runtime_seconds=ns.branch_health_runtime_seconds,
        governance_budget_warn_seconds=ns.governance_budget_warn_seconds,
        governance_budget_hard_seconds=ns.governance_budget_hard_seconds,
        branch_budget_warn_seconds=ns.branch_health_budget_warn_seconds,
        branch_budget_hard_seconds=ns.branch_health_budget_hard_seconds,
    )

    print(
        "governance_audit_packet_generate: "
        f"rows_total={packet['closure_map']['rows_total']} "
        f"json_formal_output={packet['artifact_snapshot']['json_files_under_formal_output']} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
