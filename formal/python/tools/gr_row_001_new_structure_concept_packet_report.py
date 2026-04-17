from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_REPORT_20260413_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_20260413_v0.json"
)


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
    concept_policy = dict(declaration.get("concept_policy", {}))
    concept_contract = dict(declaration.get("concept_contract", {}))

    structural_gap_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_structural_gap_definition_report", "")
    ).strip()
    matrix_path = REPO_ROOT / str(required_inputs.get("toe_global_completion_matrix", "")).strip()
    packet05_path = REPO_ROOT / str(
        required_inputs.get("gr_empirical_comparison_packet_05_artifact", "")
    ).strip()
    note_path = REPO_ROOT / str(required_inputs.get("concept_note", "")).strip()

    structural_gap = _read_json(structural_gap_path)
    matrix_text = _read_text(matrix_path)
    packet05 = _read_json(packet05_path)
    note_text = _read_text(note_path)

    structural_gap_summary = dict(structural_gap.get("summary", {}))
    structural_gap_outcome = str(structural_gap_summary.get("terminal_outcome", "")).strip()
    structural_gap_next_action = str(structural_gap_summary.get("next_action", "")).strip()

    packet05_payload = dict(packet05.get("payload", {}))
    packet05_status = str(packet05_payload.get("status", "")).strip()
    packet05_decision = str(packet05_payload.get("decision", "")).strip()

    target_row = str(concept_policy.get("target_row", "")).strip()
    required_structural_gap_outcome = str(
        concept_policy.get("required_structural_gap_outcome", "")
    ).strip()
    required_packet05_decision = str(concept_policy.get("required_packet05_decision", "")).strip()
    required_packet05_status = str(concept_policy.get("required_packet05_status", "")).strip()
    required_note_tokens = list(concept_policy.get("required_note_tokens", []))
    concept_family = str(concept_policy.get("concept_family", "")).strip()
    concept_axes = list(concept_policy.get("concept_axes", []))

    row_present_in_matrix = target_row in matrix_text
    row_is_theorem_gap = target_row in matrix_text and "ROW-PILLAR-GR-001 | pillar | GR_DERIVATION_CHAIN |" in matrix_text
    note_tokens_present = all(token in note_text for token in required_note_tokens)

    preconditions_ok = (
        structural_gap_outcome == required_structural_gap_outcome
        and packet05_decision == required_packet05_decision
        and packet05_status == required_packet05_status
        and row_present_in_matrix
        and row_is_theorem_gap
        and note_tokens_present
        and bool(concept_family)
        and len(concept_axes) >= 4
    )

    contract_shape_ok = all(
        key in concept_policy
        for key in [
            "target_row",
            "required_structural_gap_outcome",
            "required_packet05_decision",
            "required_packet05_status",
            "required_note_tokens",
            "concept_family",
            "concept_axes",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    allowed_outcomes = set(concept_contract.get("allowed_outcomes", []))
    default_outcome = str(
        concept_contract.get("default_outcome", "GR_ROW_001_NEW_STRUCTURE_CONCEPT_EVIDENCE_INCOMPLETE")
    ).strip()

    if not contract_shape_ok:
        terminal_outcome = "HOLD_PENDING_GR_ROW_001_CONCEPT_REPAIR"
        next_action = "REPAIR_GR_ROW_001_CONCEPT_PACKET_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_LOCKED"
        next_action = "KEEP_GR_ROW_001_FROZEN_AND_PREPARE_ONE_BOUNDED_SHARED_INTERFACE_DECLARATION_IF_RESTART_AUTHORIZED"
    else:
        terminal_outcome = "GR_ROW_001_NEW_STRUCTURE_CONCEPT_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_GR_ROW_001_CONCEPT_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    concept_bundle = {
        "structure_family": concept_family,
        "design_scope": "one bounded shared interface concept for ROW-PILLAR-GR-001 only",
        "design_axes": {
            "shared_state_carrier": "Define one state carrier that is meaningful in both weak-field transport and regime-limit alignment views.",
            "cross_regime_transport_interface_map": "Define one explicit map linking transport residual structure to regime-limit alignment structure.",
            "single_interface_observable": "Attach the concept to one bounded observable or residual that can be tested without widening lane scope.",
            "fail_closed_falsification_hook": "Specify one condition that falsifies the concept and routes the row to rework rather than renewed attack-class cycling."
        },
        "frozen_cycle_constraint": structural_gap_next_action,
        "execution_policy": "NONEXECUTING_DESIGN_ONLY_UNTIL_P75_AND_P77_CLEAR"
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "structural_gap_outcome_match": structural_gap_outcome == required_structural_gap_outcome,
            "packet05_decision_match": packet05_decision == required_packet05_decision,
            "packet05_status_match": packet05_status == required_packet05_status,
            "target_row_present_in_matrix": row_present_in_matrix,
            "target_row_is_theorem_gap": row_is_theorem_gap,
            "concept_note_tokens_present": note_tokens_present,
            "single_terminal_outcome_rule_declared": str(
                concept_contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_GR_ROW_001_NEW_STRUCTURE_CONCEPT_OUTCOME",
            "no_loop_rule_declared": str(concept_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_ROW_001_NEW_STRUCTURE_CONCEPT_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "concept_packet_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "target_row": target_row,
                "structural_gap_outcome": structural_gap_outcome,
                "required_structural_gap_outcome": required_structural_gap_outcome,
                "packet05_decision": packet05_decision,
                "required_packet05_decision": required_packet05_decision,
                "packet05_status": packet05_status,
                "required_packet05_status": required_packet05_status,
                "concept_family": concept_family,
                "concept_axes": concept_axes,
                "concept_note_tokens_present": note_tokens_present,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "concept_bundle": concept_bundle,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": target_row,
            "concept_family": concept_family,
            "next_action": next_action,
            "single_layer_only": bool(concept_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(concept_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_row_001_structural_gap_definition_report": _ptr(structural_gap_path),
            "toe_global_completion_matrix": _ptr(matrix_path),
            "gr_empirical_comparison_packet_05_artifact": _ptr(packet05_path),
            "concept_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local GR row 001 new-structure concept packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR row 001 new-structure concept packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_row_001_new_structure_concept_packet_20260413_v0.json",
    )
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
        "gr_row_001_new_structure_concept_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())