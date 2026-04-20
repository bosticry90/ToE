from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_THEOREM_GAP_RERANKING_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_RERANKING_20260419_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_reranking_20260419_v0.json"


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
    policy = dict(declaration.get("reranking_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    qualification_path = REPO_ROOT / _text(required_inputs.get("fresh_movement_qualification_report"))
    auth_path = REPO_ROOT / _text(required_inputs.get("successor_family_authorization_review_report"))
    dashboard_path = REPO_ROOT / _text(required_inputs.get("blocker_burn_dashboard_report"))
    qualification_report = _read_json(qualification_path)
    auth_report = _read_json(auth_path)
    dashboard_report = _read_json(dashboard_path)

    dossier_reports = {}
    reactivation_reports = {}
    for key, rel in required_inputs.items():
        if key.endswith("_dossier_report"):
            dossier_reports[key] = _read_json(REPO_ROOT / _text(rel))
        elif key.endswith("_reactivation_tranche_report"):
            reactivation_reports[key] = _read_json(REPO_ROOT / _text(rel))

    default_order = [str(v).strip() for v in policy.get("default_order", [])]
    qm_last_row = _text(policy.get("qm_last_row"))
    authorized_row = auth_report.get("summary", {}).get("selected_row") or "NONE"
    authorized = auth_report.get("summary", {}).get("terminal_outcome") == "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED"

    resolved_rows = set()
    for report in reactivation_reports.values():
        outcome = _text(report.get("summary", {}).get("terminal_outcome"))
        if outcome.endswith("EXECUTED_AND_PROMOTED") or outcome.endswith("EXPLICITLY_EXHAUSTED"):
            row_id = report.get("summary", {}).get("target_row_id")
            if row_id:
                resolved_rows.add(row_id)

    theorem_gap_delta = int(dashboard_report.get("blocker_scoreboard", {}).get("delta_by_class", {}).get("THEOREM_GAP", 0) or 0)
    update_trigger = theorem_gap_delta < 0 or bool(resolved_rows)

    ranking = [row for row in default_order if row not in resolved_rows]
    if authorized and authorized_row in ranking:
        ranking.remove(authorized_row)
        ranking.insert(0, authorized_row)
    if qm_last_row in ranking:
        ranking = [row for row in ranking if row != qm_last_row] + [qm_last_row]

    row_states = {
        report.get("summary", {}).get("row_id"): {
            "policy_class": report.get("summary", {}).get("policy_class"),
            "admissible_if_authorized": report.get("summary", {}).get("admissible_if_authorized"),
        }
        for report in dossier_reports.values()
    }

    if not ranking:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_THEOREM_GAP_RERANKING_REPAIR"
        next_action = "RESTORE_RERANKING_INPUTS_AND_RERUN"
    elif update_trigger:
        terminal_outcome = "POST_PLAN_THEOREM_GAP_RERANKING_UPDATED"
        next_action = f"REVIEW_{ranking[0]}_DOSSIER_FOR_NEXT_SINGLE_ROW_AUTHORIZATION"
    else:
        terminal_outcome = "POST_PLAN_THEOREM_GAP_RERANKING_RETAINED"
        next_action = "MAINTAIN_TERMINAL_HOLD_UNTIL_FRESH_MOVEMENT_OR_EXPLICIT_EXHAUSTION_UPDATES_RANKING"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(contract.get("default_outcome"))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "qualification_surface_visible": bool(qualification_report),
            "authorization_surface_visible": bool(auth_report),
            "default_order_materialized": bool(default_order),
            "qm_last_row_preserved": not ranking or ranking[-1] == qm_last_row,
            "reranking_updates_only_after_declared_triggers": (terminal_outcome != "POST_PLAN_THEOREM_GAP_RERANKING_UPDATED") or update_trigger,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_RERANKING_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule")) == "ONE_POST_PLAN_THEOREM_GAP_RERANKING_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorized_row_moves_to_front_only_when_authorized": (not authorized) or ranking[0] == authorized_row,
                "resolved_rows_removed_from_ranking": all(row not in ranking for row in resolved_rows),
            },
            "inputs": {
                "authorized_row": authorized_row,
                "authorized": authorized,
                "theorem_gap_delta": theorem_gap_delta,
                "resolved_rows": sorted(resolved_rows),
                "default_order": default_order,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_row": authorized_row,
            "resolved_rows": sorted(resolved_rows),
            "ranking": ranking,
            "top_row": ranking[0] if ranking else None,
            "row_states": row_states,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "fresh_movement_qualification_report": _ptr(qualification_path),
            "successor_family_authorization_review_report": _ptr(auth_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            **{key: _ptr(REPO_ROOT / _text(value)) for key, value in required_inputs.items() if key.endswith("_dossier_report") or key.endswith("_reactivation_tranche_report")},
        },
        "non_claim_boundary": "Repository-local theorem-gap reranking only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan theorem-gap reranking report.")
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
        "post_plan_theorem_gap_reranking_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
