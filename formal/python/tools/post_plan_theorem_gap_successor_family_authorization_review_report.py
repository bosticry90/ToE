from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_successor_family_authorization_review_20260419_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("authorization_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    qualification_path = REPO_ROOT / _text(required_inputs.get("fresh_movement_qualification_report"))
    qualification_report = _read_json(qualification_path)
    dossier_paths = {key: REPO_ROOT / _text(value) for key, value in required_inputs.items() if key.endswith("_dossier_report")}
    dossiers = {key: _read_json(path) for key, path in dossier_paths.items()}
    dossiers_by_row = {payload.get("summary", {}).get("row_id"): payload for payload in dossiers.values()}

    default_row = _text(policy.get("default_selected_row"))
    alternate_row = _text(policy.get("alternate_selected_row"))
    selected_row = qualification_report.get("summary", {}).get("selected_row") or "NONE"
    selected_dossier = dossiers_by_row.get(selected_row, {})
    selected_summary = selected_dossier.get("summary", {})

    tie_rule_ok = True
    stat_count = dossiers_by_row.get(default_row, {}).get("summary", {}).get("historical_no_change_count", 999)
    cosmo_count = dossiers_by_row.get(alternate_row, {}).get("summary", {}).get("historical_no_change_count", 999)
    if selected_row == default_row:
        tie_rule_ok = int(stat_count) <= int(cosmo_count)
    elif selected_row == alternate_row:
        tie_rule_ok = bool(qualification_report.get("summary", {}).get("cosmo_override_condition_met"))

    selected_fresh = bool(selected_summary.get("fresh_movement_machine_pinned"))
    selected_admissible = bool(selected_summary.get("admissible_if_authorized"))
    non_qm_requirement_ok = bool(selected_summary.get("non_qm_movement_required_satisfied", True))
    reserve_blocked = bool(selected_summary.get("reserve_until_first_selected_family_resolution", False))
    bounded_surface_decl = _text(selected_summary.get("bounded_execution_surface_declaration"))
    bounded_surface_gate = _text(selected_summary.get("bounded_execution_surface_gate"))

    if not dossiers_by_row:
        terminal_outcome = "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_REACTIVATION_AUTHORIZATION_INPUTS_AND_RERUN"
        selected_execution_surface_declaration = None
    elif selected_row == "NONE":
        terminal_outcome = "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_NO_ROW_AUTHORIZED"
        next_action = "KEEP_TERMINAL_HOLD_UNTIL_FRESH_MOVEMENT_IS_MACHINE_PINNED_AND_RERUN_AUTHORIZATION_REVIEW"
        selected_execution_surface_declaration = None
    elif not all([selected_dossier, selected_fresh, selected_admissible, non_qm_requirement_ok, tie_rule_ok, not reserve_blocked, bounded_surface_decl, bounded_surface_gate]):
        terminal_outcome = "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_CONTRACT_VIOLATION"
        next_action = "REPAIR_DOSSIER_POLICY_OR_QUALIFICATION_SELECTION_BEFORE_AUTHORIZATION"
        selected_execution_surface_declaration = bounded_surface_decl or None
    else:
        terminal_outcome = "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED"
        next_action = "EXECUTE_DECLARED_THEOREM_GAP_REACTIVATION_TRANCHE_ONCE"
        selected_execution_surface_declaration = bounded_surface_decl

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(contract.get("default_outcome"))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "qualification_surface_visible": bool(qualification_report),
            "selected_row_present_in_dossiers": selected_row == "NONE" or bool(selected_dossier),
            "selected_row_fresh_movement_machine_pinned": selected_row == "NONE" or selected_fresh,
            "selected_row_admissible_if_authorized": selected_row == "NONE" or selected_admissible,
            "qm_non_qm_movement_requirement_satisfied": selected_row != "ROW-PILLAR-QM-001" or non_qm_requirement_ok,
            "tie_rule_satisfied": tie_rule_ok,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorization_requires_selected_fresh_evidence": (
                    terminal_outcome != "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED"
                )
                or selected_fresh,
                "authorization_requires_single_row_only": terminal_outcome in allowed_outcomes,
            },
            "inputs": {
                "default_selected_row": default_row,
                "alternate_selected_row": alternate_row,
                "selected_row": selected_row,
                "selected_row_historical_no_change_count": selected_summary.get("historical_no_change_count"),
                "stat_historical_no_change_count": stat_count,
                "cosmo_historical_no_change_count": cosmo_count,
                "cosmo_override_condition_met": qualification_report.get("summary", {}).get("cosmo_override_condition_met"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "default_selected_row": default_row,
            "alternate_selected_row": alternate_row,
            "selected_row": selected_row,
            "selected_execution_surface_declaration": selected_execution_surface_declaration,
            "selected_execution_surface_gate": bounded_surface_gate or None,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "fresh_movement_qualification_report": _ptr(qualification_path),
            **{key: _ptr(path) for key, path in dossier_paths.items()},
        },
        "non_claim_boundary": "Repository-local theorem-gap successor-family authorization only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan theorem-gap successor-family authorization review report.")
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
    print(
        "post_plan_theorem_gap_successor_family_authorization_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
