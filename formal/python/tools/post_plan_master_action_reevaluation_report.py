from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_MASTER_ACTION_REEVALUATION_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_MASTER_ACTION_REEVALUATION_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_master_action_reevaluation_20260418_v0.json"
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
    policy = dict(declaration.get("reevaluation_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    phase3_path = REPO_ROOT / str(required_inputs.get("post_plan_qm_theorem_gap_tranche_report", "")).strip()
    phase4_path = REPO_ROOT / str(required_inputs.get("post_plan_seam_reroute_reassessment_report", "")).strip()
    recovery_path = REPO_ROOT / str(required_inputs.get("master_action_packet01_transport_binding_recovery_report", "")).strip()
    standardization_path = REPO_ROOT / str(required_inputs.get("derivation_chain_transport_standardization_report", "")).strip()
    target_map_path = REPO_ROOT / str(required_inputs.get("post_plan_target_map_report", "")).strip()

    phase3 = _read_json(phase3_path)
    phase4 = _read_json(phase4_path)
    recovery = _read_json(recovery_path)
    standardization = _read_json(standardization_path)
    target_map = _read_json(target_map_path)

    upstream_movement_detected = bool(phase3.get("summary", {}).get("row_truth_change_detected")) or phase4.get("summary", {}).get("terminal_outcome") == "POST_PLAN_SEAM_REROUTE_REASSESSMENT_MATERIALIZED"
    support_only_read_ok = recovery.get("summary", {}).get("canonical_transport_read_token") == str(policy.get("required_support_only_read", "")).strip()
    one_recompute_limit_ok = "ONE_RECOMPUTE_LIMIT_PRESERVED" == str(policy.get("required_one_recompute_limit_rule", "")).strip()
    standardization_ok = standardization.get("summary", {}).get("terminal_outcome") == "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_MATERIALIZED"
    target_map_ok = target_map.get("summary", {}).get("terminal_outcome") == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_MASTER_ACTION_REEVALUATION_EVIDENCE_INCOMPLETE")).strip()

    if not target_map_ok:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_MASTER_ACTION_REEVALUATION_REPAIR"
        next_action = "RESTORE_POST_PLAN_MASTER_ACTION_INPUT_SHAPE_AND_RERUN"
    elif all([support_only_read_ok, one_recompute_limit_ok, standardization_ok]) and not upstream_movement_detected:
        terminal_outcome = "POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT"
        next_action = "KEEP_MASTER_ACTION_FROZEN_AS_SUPPORT_ONLY"
    elif all([support_only_read_ok, one_recompute_limit_ok, standardization_ok]) and upstream_movement_detected:
        terminal_outcome = "POST_PLAN_MASTER_ACTION_REEVALUATION_MATERIALIZED"
        next_action = "APPLY_BOUNDED_MASTER_ACTION_REEVALUATION_RESULT"
    else:
        terminal_outcome = "POST_PLAN_MASTER_ACTION_REEVALUATION_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_MASTER_ACTION_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "canonical_transport_recovery_present": support_only_read_ok,
            "derivation_chain_standardization_present": standardization_ok,
            "target_map_materialized": target_map_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_MASTER_ACTION_REEVALUATION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_MASTER_ACTION_REEVALUATION_LAYER_ONLY",
            "one_recompute_limit_rule_preserved": one_recompute_limit_ok,
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "reevaluation_only_after_upstream_movement": (terminal_outcome != "POST_PLAN_MASTER_ACTION_REEVALUATION_MATERIALIZED") or upstream_movement_detected,
            },
            "inputs": {
                "upstream_movement_detected": upstream_movement_detected,
                "canonical_transport_read_token": recovery.get("summary", {}).get("canonical_transport_read_token"),
                "recovery_terminal_outcome": recovery.get("summary", {}).get("terminal_outcome"),
                "standardization_terminal_outcome": standardization.get("summary", {}).get("terminal_outcome"),
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
            "canonical_transport_read_token": recovery.get("summary", {}).get("canonical_transport_read_token"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_qm_theorem_gap_tranche_report": _ptr(phase3_path),
            "post_plan_seam_reroute_reassessment_report": _ptr(phase4_path),
            "master_action_packet01_transport_binding_recovery_report": _ptr(recovery_path),
            "derivation_chain_transport_standardization_report": _ptr(standardization_path),
            "post_plan_target_map_report": _ptr(target_map_path),
        },
        "non_claim_boundary": "Repository-local post-plan master-action reevaluation only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan master-action reevaluation report.")
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
    print(f"post_plan_master_action_reevaluation_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())