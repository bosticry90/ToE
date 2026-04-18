from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_SEAM_REROUTE_REASSESSMENT_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_SEAM_REROUTE_REASSESSMENT_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_seam_reroute_reassessment_20260418_v0.json"
)


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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("reroute_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    target_map_path = REPO_ROOT / str(required_inputs.get("post_plan_target_map_report", "")).strip()
    phase2_path = REPO_ROOT / str(required_inputs.get("post_plan_cosmo_sr_tranche_report", "")).strip()
    phase3_path = REPO_ROOT / str(required_inputs.get("post_plan_qm_theorem_gap_tranche_report", "")).strip()
    sla_path = REPO_ROOT / str(required_inputs.get("seam_resolution_sla_ledger_report", "")).strip()
    normalization_path = REPO_ROOT / str(required_inputs.get("seam_executable_path_normalization_report", "")).strip()

    target_map = _read_json(target_map_path)
    phase2 = _read_json(phase2_path)
    phase3 = _read_json(phase3_path)
    sla = _read_json(sla_path)
    normalization = _read_json(normalization_path)
    route_map = {row["row_id"]: row for row in target_map.get("routed_rows", [])}

    executable_ok = target_map.get("summary", {}).get("executable_now_rows") == [str(policy.get("required_single_executable_row", "")).strip()]
    blocked_ok = str(policy.get("required_blocked_row", "")).strip() in target_map.get("summary", {}).get("blocked_pending_authority_rows", [])
    held_ok = str(policy.get("required_external_hold_row", "")).strip() in target_map.get("summary", {}).get("external_hold_rows", [])
    monitoring_ok = str(policy.get("required_closed_monitoring_row", "")).strip() in target_map.get("summary", {}).get("closed_monitoring_rows", [])
    upstream_movement_detected = bool(phase2.get("summary", {}).get("row_truth_change_detected")) or bool(phase3.get("summary", {}).get("row_truth_change_detected"))
    normalization_ok = any(row.get("path_class") == "SINGLE_AUTHORIZED_NONLIVE_EXECUTABLE_PATH" and row.get("seam_id") == "SEAM-COSMO-SR" for row in normalization.get("normalized_rows", []))
    sla_ok = any(entry.get("row_id") == "ROW-SEAM-QM-STAT-001" for entry in sla.get("entries", [])) and any(entry.get("row_id") == "ROW-SEAM-QFT-GR-001" for entry in sla.get("entries", []))

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_SEAM_REROUTE_REASSESSMENT_EVIDENCE_INCOMPLETE")).strip()

    if not route_map:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_SEAM_REROUTE_REPAIR"
        next_action = "RESTORE_POST_PLAN_SEAM_REROUTE_INPUT_SHAPE_AND_RERUN"
    elif all([executable_ok, blocked_ok, held_ok, monitoring_ok, normalization_ok, sla_ok]) and not upstream_movement_detected:
        terminal_outcome = "POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT"
        next_action = "PRESERVE_CURRENT_SEAM_CLASSES_AND_SKIP_REROUTE"
    elif all([executable_ok, blocked_ok, held_ok, monitoring_ok, normalization_ok, sla_ok]) and upstream_movement_detected:
        terminal_outcome = "POST_PLAN_SEAM_REROUTE_REASSESSMENT_MATERIALIZED"
        next_action = "APPLY_CHANGED_SEAM_ROUTE_SET_AND_REEVALUATE_MASTER_ACTION"
    else:
        terminal_outcome = "POST_PLAN_SEAM_REROUTE_REASSESSMENT_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_SEAM_REROUTE_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "single_executable_row_preserved": executable_ok,
            "blocked_row_preserved": blocked_ok,
            "external_hold_row_preserved": held_ok,
            "closed_monitoring_row_preserved": monitoring_ok,
            "normalization_surface_matches": normalization_ok,
            "sla_surface_matches": sla_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_SEAM_REROUTE_REASSESSMENT_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_SEAM_REROUTE_REASSESSMENT_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "reroute_only_after_upstream_movement": (terminal_outcome != "POST_PLAN_SEAM_REROUTE_REASSESSMENT_MATERIALIZED") or upstream_movement_detected,
            },
            "inputs": {
                "phase2_row_truth_change_detected": phase2.get("summary", {}).get("row_truth_change_detected"),
                "phase3_row_truth_change_detected": phase3.get("summary", {}).get("row_truth_change_detected"),
                "upstream_movement_detected": upstream_movement_detected,
                "qm_stat_sla_state": next((entry.get("decision_state") for entry in sla.get("entries", []) if entry.get("row_id") == "ROW-SEAM-QM-STAT-001"), None),
                "cosmo_sr_path_class": next((row.get("path_class") for row in normalization.get("normalized_rows", []) if row.get("seam_id") == "SEAM-COSMO-SR"), None),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "upstream_movement_detected": upstream_movement_detected,
            "single_executable_row": str(policy.get("required_single_executable_row", "")).strip(),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "post_plan_cosmo_sr_tranche_report": _ptr(phase2_path),
            "post_plan_qm_theorem_gap_tranche_report": _ptr(phase3_path),
            "seam_resolution_sla_ledger_report": _ptr(sla_path),
            "seam_executable_path_normalization_report": _ptr(normalization_path),
        },
        "non_claim_boundary": "Repository-local post-plan seam reroute reassessment only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan seam reroute reassessment report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"post_plan_seam_reroute_reassessment_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())