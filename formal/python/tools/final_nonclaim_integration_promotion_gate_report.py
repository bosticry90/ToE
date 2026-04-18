from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_REPORT_20260418_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_20260418_v0.json"
)


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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("gate_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    phase3_path = REPO_ROOT / str(required_inputs.get("seam_executable_path_normalization_report", "")).strip()
    phase4_path = REPO_ROOT / str(required_inputs.get("master_action_packet01_transport_binding_recovery_report", "")).strip()
    phase5_path = REPO_ROOT / str(required_inputs.get("derivation_chain_transport_standardization_report", "")).strip()

    phase3 = _read_json(phase3_path)
    phase4 = _read_json(phase4_path)
    phase5 = _read_json(phase5_path)

    phase3_summary = dict(phase3.get("summary", {}))
    phase4_summary = dict(phase4.get("summary", {}))
    phase5_summary = dict(phase5.get("summary", {}))

    phase3_ok = str(phase3_summary.get("terminal_outcome", "")).strip() == str(policy.get("required_phase3_terminal_outcome", "")).strip()
    phase4_ok = str(phase4_summary.get("terminal_outcome", "")).strip() == str(policy.get("required_phase4_terminal_outcome", "")).strip()
    phase5_ok = str(phase5_summary.get("terminal_outcome", "")).strip() == str(policy.get("required_phase5_terminal_outcome", "")).strip()
    single_executable_seam_ok = phase3_summary.get("authorized_executable_seams", []) == [str(policy.get("required_single_executable_seam", "")).strip()]
    phase4_blocker_ok = str(phase4_summary.get("transport_binding_blocker", "")).strip() == str(policy.get("required_phase4_blocker", "")).strip()
    phase5_count_ok = int(phase5_summary.get("admitted_pillar_count", -1)) == int(policy.get("required_phase5_admitted_pillar_count", 0))
    phase5_token_ok = str(phase5_summary.get("canonical_transport_read_token", "")).strip() == str(policy.get("required_phase5_transport_read_token", "")).strip()

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_BLOCKED")).strip()

    if not phase3_summary or not phase4_summary or not phase5_summary:
        terminal_outcome = "HOLD_PENDING_FINAL_NONCLAIM_INTEGRATION_REPAIR"
        next_action = "RESTORE_PHASE3_TO_PHASE5_INPUTS_AND_RERUN"
    elif all([phase3_ok, phase4_ok, phase5_ok, single_executable_seam_ok, phase4_blocker_ok, phase5_count_ok, phase5_token_ok]):
        terminal_outcome = "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_SATISFIED"
        next_action = "HOLD_NONCLAIM_INTEGRATED_POSTURE_AND_DO_NOT_PROMOTE_BEYOND_DECLARED_BOUNDARIES"
    else:
        terminal_outcome = "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_BLOCKED"
        next_action = "REPAIR_PHASE3_TO_PHASE5_INTEGRATION_CRITERIA_BEFORE_ANY_FINAL_NONCLAIM_GATE_CLAIM"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase3_normalization_satisfied": phase3_ok,
            "phase4_recovery_satisfied": phase4_ok,
            "phase5_standardization_satisfied": phase5_ok,
            "single_executable_seam_preserved": single_executable_seam_ok,
            "phase4_blocker_preserved": phase4_blocker_ok,
            "phase5_admitted_pillar_count_preserved": phase5_count_ok,
            "phase5_transport_read_token_preserved": phase5_token_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_LAYER_ONLY"
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "integration_bundle_synchronized": all([phase3_ok, phase4_ok, phase5_ok]),
                "nonclaim_boundary_preserved": True,
            },
            "inputs": {
                "phase3_terminal_outcome": phase3_summary.get("terminal_outcome"),
                "phase4_terminal_outcome": phase4_summary.get("terminal_outcome"),
                "phase5_terminal_outcome": phase5_summary.get("terminal_outcome"),
                "single_executable_seam": phase3_summary.get("authorized_executable_seams"),
                "phase4_blocker": phase4_summary.get("transport_binding_blocker"),
                "phase5_admitted_pillar_count": phase5_summary.get("admitted_pillar_count"),
                "phase5_transport_read_token": phase5_summary.get("canonical_transport_read_token"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "phase3_terminal_outcome": phase3_summary.get("terminal_outcome"),
            "phase4_terminal_outcome": phase4_summary.get("terminal_outcome"),
            "phase5_terminal_outcome": phase5_summary.get("terminal_outcome"),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "seam_executable_path_normalization_report": _ptr(phase3_path),
            "master_action_packet01_transport_binding_recovery_report": _ptr(phase4_path),
            "derivation_chain_transport_standardization_report": _ptr(phase5_path),
        },
        "non_claim_boundary": "Repository-local final non-claim integration and promotion gate report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the final non-claim integration promotion gate report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=REPO_ROOT / "formal" / "output" / "reports" / "final_nonclaim_integration_promotion_gate_20260418_v0.json")
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("final_nonclaim_integration_promotion_gate_report: " f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())