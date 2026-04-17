from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_ROW_001_SHARED_INTERFACE_DECLARATION_REPORT_20260413_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GR_ROW_001_SHARED_INTERFACE_DECLARATION_20260413_v0.json"
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
    shared_interface_policy = dict(declaration.get("shared_interface_policy", {}))
    shared_interface_contract = dict(declaration.get("shared_interface_contract", {}))

    concept_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_new_structure_concept_packet_report", "")
    ).strip()
    structural_gap_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_structural_gap_definition_report", "")
    ).strip()
    packet05_path = REPO_ROOT / str(
        required_inputs.get("gr_empirical_comparison_packet_05_artifact", "")
    ).strip()
    note_path = REPO_ROOT / str(required_inputs.get("shared_interface_note", "")).strip()

    concept_report = _read_json(concept_path)
    structural_gap_report = _read_json(structural_gap_path)
    packet05 = _read_json(packet05_path)
    note_text = _read_text(note_path)

    concept_summary = dict(concept_report.get("summary", {}))
    structural_gap_summary = dict(structural_gap_report.get("summary", {}))
    packet05_payload = dict(packet05.get("payload", {}))

    concept_outcome = str(concept_summary.get("terminal_outcome", "")).strip()
    structural_gap_outcome = str(structural_gap_summary.get("terminal_outcome", "")).strip()
    packet05_decision = str(packet05_payload.get("decision", "")).strip()
    packet05_status = str(packet05_payload.get("status", "")).strip()

    target_row = str(shared_interface_policy.get("target_row", "")).strip()
    required_concept_outcome = str(shared_interface_policy.get("required_concept_outcome", "")).strip()
    required_structural_gap_outcome = str(
        shared_interface_policy.get("required_structural_gap_outcome", "")
    ).strip()
    required_packet05_decision = str(shared_interface_policy.get("required_packet05_decision", "")).strip()
    required_packet05_status = str(shared_interface_policy.get("required_packet05_status", "")).strip()
    required_note_tokens = list(shared_interface_policy.get("required_note_tokens", []))
    required_formula_phrase = str(shared_interface_policy.get("required_formula_phrase", "")).strip()
    interface_object = str(shared_interface_policy.get("interface_object", "")).strip()
    interface_domain = str(shared_interface_policy.get("interface_domain", "")).strip()
    interface_codomain = str(shared_interface_policy.get("interface_codomain", "")).strip()
    comparison_surface = str(shared_interface_policy.get("comparison_surface", "")).strip()

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    formula_phrase_present = required_formula_phrase in note_text

    policy_shape_ok = all(
        key in shared_interface_policy
        for key in [
            "target_row",
            "required_concept_outcome",
            "required_structural_gap_outcome",
            "required_packet05_decision",
            "required_packet05_status",
            "required_note_tokens",
            "required_formula_phrase",
            "interface_object",
            "interface_domain",
            "interface_codomain",
            "comparison_surface",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    preconditions_ok = (
        concept_outcome == required_concept_outcome
        and structural_gap_outcome == required_structural_gap_outcome
        and packet05_decision == required_packet05_decision
        and packet05_status == required_packet05_status
        and note_tokens_present
        and formula_phrase_present
        and bool(interface_object)
        and bool(interface_domain)
        and bool(interface_codomain)
        and bool(comparison_surface)
        and bool(target_row)
    )

    allowed_outcomes = set(shared_interface_contract.get("allowed_outcomes", []))
    default_outcome = str(
        shared_interface_contract.get("default_outcome", "GR_ROW_001_SHARED_INTERFACE_EVIDENCE_INCOMPLETE")
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_GR_ROW_001_SHARED_INTERFACE_REPAIR"
        next_action = "REPAIR_GR_ROW_001_SHARED_INTERFACE_DECLARATION_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "GR_ROW_001_SHARED_INTERFACE_DECLARED"
        next_action = "KEEP_DECLARATION_NONEXECUTING_AND_PREPARE_ONE_BOUNDED_COMPARATOR_SPEC_IF_RESTART_AUTHORIZED"
    else:
        terminal_outcome = "GR_ROW_001_SHARED_INTERFACE_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_GR_ROW_001_SHARED_INTERFACE_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    interface_summary = {
        "target_row": target_row,
        "interface_object": interface_object,
        "domain": interface_domain,
        "codomain": interface_codomain,
        "comparison_surface": comparison_surface,
        "candidate_observable": "DELTA_XI_GR_INTERFACE_SIGNED_RESIDUAL",
        "observable_formula": required_formula_phrase,
        "execution_policy": "NONEXECUTING_DECLARATION_ONLY_UNTIL_P75_AND_P77_CLEAR",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "concept_outcome_match": concept_outcome == required_concept_outcome,
            "structural_gap_outcome_match": structural_gap_outcome == required_structural_gap_outcome,
            "packet05_decision_match": packet05_decision == required_packet05_decision,
            "packet05_status_match": packet05_status == required_packet05_status,
            "note_tokens_present": note_tokens_present,
            "formula_phrase_present": formula_phrase_present,
            "single_terminal_outcome_rule_declared": str(
                shared_interface_contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_GR_ROW_001_SHARED_INTERFACE_DECLARATION_OUTCOME",
            "no_loop_rule_declared": str(shared_interface_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_ROW_001_SHARED_INTERFACE_DECLARATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "shared_interface_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "target_row": target_row,
                "concept_outcome": concept_outcome,
                "required_concept_outcome": required_concept_outcome,
                "structural_gap_outcome": structural_gap_outcome,
                "required_structural_gap_outcome": required_structural_gap_outcome,
                "packet05_decision": packet05_decision,
                "required_packet05_decision": required_packet05_decision,
                "packet05_status": packet05_status,
                "required_packet05_status": required_packet05_status,
                "interface_object": interface_object,
                "interface_domain": interface_domain,
                "interface_codomain": interface_codomain,
                "comparison_surface": comparison_surface,
                "formula_phrase_present": formula_phrase_present,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "shared_interface_summary": interface_summary,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": target_row,
            "interface_object": interface_object,
            "comparison_surface": comparison_surface,
            "next_action": next_action,
            "single_layer_only": bool(shared_interface_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(shared_interface_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_row_001_new_structure_concept_packet_report": _ptr(concept_path),
            "gr_row_001_structural_gap_definition_report": _ptr(structural_gap_path),
            "gr_empirical_comparison_packet_05_artifact": _ptr(packet05_path),
            "shared_interface_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local GR row 001 shared-interface declaration report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR row 001 shared-interface declaration report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_row_001_shared_interface_declaration_20260413_v0.json",
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
        "gr_row_001_shared_interface_declaration_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())