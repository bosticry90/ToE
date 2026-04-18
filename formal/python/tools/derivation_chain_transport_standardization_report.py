from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_REPORT_20260418_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_20260418_v0.json"
)

CHAIN_SUFFIXES = [
    "ACTION_STAGE_STATUS_v0",
    "VARIATION_STAGE_STATUS_v0",
    "BRIDGE_STAGE_STATUS_v0",
    "OPERATOR_STAGE_STATUS_v0",
    "TRANSPORT_STAGE_STATUS_v0",
    "RESIDUAL_LAW_STAGE_STATUS_v0",
    "REGIME_LIMIT_STAGE_STATUS_v0",
]


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("standardization_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    standard_path = REPO_ROOT / str(required_inputs.get("foundational_derivation_chain_standard", "")).strip()
    plan_path = REPO_ROOT / str(required_inputs.get("foundational_derivation_chain_execution_plan", "")).strip()
    matrix_path = REPO_ROOT / str(required_inputs.get("foundational_derivation_chain_matrix", "")).strip()
    phase4_path = REPO_ROOT / str(required_inputs.get("master_action_packet01_transport_binding_recovery_report", "")).strip()

    standard_text = _read_text(standard_path)
    plan_text = _read_text(plan_path)
    matrix = _read_json(matrix_path)
    phase4 = _read_json(phase4_path)

    phase4_summary = dict(phase4.get("summary", {}))
    phase_rows = dict(matrix.get("phase_rows", {}))
    lanes = dict(matrix.get("lanes", {}))
    required_phase_status = str(policy.get("required_phase_status", "")).strip()
    required_m3_stage_status = str(policy.get("required_m3_stage_status", "")).strip()

    admitted_pillars: list[str] = []
    standardized_rows: list[dict[str, Any]] = []
    phase_rows_complete = True
    for pillar, row in sorted(phase_rows.items()):
        m2_ok = str(row.get("m2", {}).get("expected_status", "")).strip() == required_phase_status
        m3_ok = str(row.get("m3", {}).get("expected_status", "")).strip() == required_phase_status
        m4_ok = str(row.get("m4", {}).get("expected_status", "")).strip() == required_phase_status
        lane_key = f"{pillar}_M3"
        lane = dict(lanes.get(lane_key, {}))
        m3_stage_bundle_ok = all(str(lane.get(suffix, "")).strip() == required_m3_stage_status for suffix in CHAIN_SUFFIXES)
        row_ok = m2_ok and m3_ok and m4_ok and m3_stage_bundle_ok
        phase_rows_complete = phase_rows_complete and row_ok
        if row_ok:
            admitted_pillars.append(pillar)
        standardized_rows.append(
            {
                "pillar": pillar,
                "m2_status": row.get("m2", {}).get("expected_status"),
                "m3_status": row.get("m3", {}).get("expected_status"),
                "m4_status": row.get("m4", {}).get("expected_status"),
                "m3_stage_bundle_status": required_m3_stage_status if m3_stage_bundle_ok else "INCOMPLETE",
                "transport_read_token": phase4_summary.get("canonical_transport_read_token"),
                "standardized": row_ok,
            }
        )

    standard_tokens_present = all(token in standard_text for token in [
        "ACTION", "VARIATION", "BRIDGE", "OPERATOR", "TRANSPORT", "RESIDUAL_LAW", "REGIME_LIMIT"
    ])
    plan_tokens_present = all(token in plan_text for token in [
        "FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0", "FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0"
    ])
    phase4_materialized = str(phase4_summary.get("terminal_outcome", "")).strip() == str(
        policy.get("required_phase4_terminal_outcome", "")
    ).strip()
    phase4_token_match = str(phase4_summary.get("canonical_transport_read_token", "")).strip() == str(
        policy.get("required_phase4_transport_read_token", "")
    ).strip()
    phase4_next_action_match = str(phase4_summary.get("next_action", "")).strip() == str(
        policy.get("required_next_action", "")
    ).strip()
    matrix_version_match = int(matrix.get("matrix_version", -1)) == int(policy.get("required_matrix_version", -2))
    admitted_pillar_count = len(admitted_pillars)
    admitted_pillar_count_match = admitted_pillar_count == int(policy.get("required_admitted_pillar_count", 0))

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_EVIDENCE_INCOMPLETE")).strip()

    if not standardized_rows:
        terminal_outcome = "HOLD_PENDING_DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_REPAIR"
        next_action = "RESTORE_DERIVATION_CHAIN_INPUTS_AND_RERUN"
    elif all([standard_tokens_present, plan_tokens_present, phase4_materialized, phase4_token_match, phase4_next_action_match, matrix_version_match, admitted_pillar_count_match, phase_rows_complete]):
        terminal_outcome = "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_MATERIALIZED"
        next_action = "USE_STANDARDIZED_DERIVATION_CHAIN_AND_CANONICAL_TRANSPORT_READ_FOR_FINAL_NONCLAIM_INTEGRATION_GATE"
    else:
        terminal_outcome = "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_DERIVATION_CHAIN_STANDARDIZATION_INPUTS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "foundational_standard_tokens_present": standard_tokens_present,
            "execution_plan_tokens_present": plan_tokens_present,
            "phase4_recovery_materialized": phase4_materialized,
            "phase4_transport_read_token_match": phase4_token_match,
            "matrix_version_match": matrix_version_match,
            "admitted_pillar_count_match": admitted_pillar_count_match,
            "phase_rows_complete": phase_rows_complete,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_LAYER_ONLY"
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "admitted_pillars_standardized": admitted_pillar_count_match and phase_rows_complete,
                "canonical_transport_read_bound": phase4_token_match,
            },
            "inputs": {
                "admitted_pillars": admitted_pillars,
                "admitted_pillar_count": admitted_pillar_count,
                "canonical_transport_read_token": phase4_summary.get("canonical_transport_read_token"),
                "phase4_target_row": phase4_summary.get("target_row"),
                "phase4_target_seam": phase4_summary.get("target_seam"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "admitted_pillars": admitted_pillars,
            "admitted_pillar_count": admitted_pillar_count,
            "canonical_transport_read_token": phase4_summary.get("canonical_transport_read_token"),
            "phase4_target_row": phase4_summary.get("target_row"),
            "next_action": next_action,
        },
        "standardized_rows": standardized_rows,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "foundational_derivation_chain_standard": _ptr(standard_path),
            "foundational_derivation_chain_execution_plan": _ptr(plan_path),
            "foundational_derivation_chain_matrix": _ptr(matrix_path),
            "master_action_packet01_transport_binding_recovery_report": _ptr(phase4_path),
        },
        "non_claim_boundary": "Repository-local derivation-chain transport standardization report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the derivation-chain transport standardization report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=REPO_ROOT / "formal" / "output" / "reports" / "derivation_chain_transport_standardization_20260418_v0.json")
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("derivation_chain_transport_standardization_report: " f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())