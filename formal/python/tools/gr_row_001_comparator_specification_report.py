from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_ROW_001_COMPARATOR_SPECIFICATION_REPORT_20260413_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GR_ROW_001_COMPARATOR_SPECIFICATION_20260413_v0.json"
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
    comparator_spec_policy = dict(declaration.get("comparator_spec_policy", {}))
    comparator_spec_contract = dict(declaration.get("comparator_spec_contract", {}))

    shared_interface_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_shared_interface_declaration_report", "")
    ).strip()
    concept_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_new_structure_concept_packet_report", "")
    ).strip()
    packet05_path = REPO_ROOT / str(
        required_inputs.get("gr_empirical_comparison_packet_05_artifact", "")
    ).strip()
    note_path = REPO_ROOT / str(required_inputs.get("comparator_spec_note", "")).strip()

    shared_interface_report = _read_json(shared_interface_path)
    concept_report = _read_json(concept_path)
    packet05 = _read_json(packet05_path)
    note_text = _read_text(note_path)

    shared_interface_summary = dict(shared_interface_report.get("summary", {}))
    concept_summary = dict(concept_report.get("summary", {}))
    packet05_payload = dict(packet05.get("payload", {}))

    shared_interface_outcome = str(shared_interface_summary.get("terminal_outcome", "")).strip()
    concept_outcome = str(concept_summary.get("terminal_outcome", "")).strip()
    packet05_decision = str(packet05_payload.get("decision", "")).strip()
    packet05_status = str(packet05_payload.get("status", "")).strip()

    target_row = str(comparator_spec_policy.get("target_row", "")).strip()
    required_shared_interface_outcome = str(
        comparator_spec_policy.get("required_shared_interface_outcome", "")
    ).strip()
    required_concept_outcome = str(comparator_spec_policy.get("required_concept_outcome", "")).strip()
    required_packet05_decision = str(comparator_spec_policy.get("required_packet05_decision", "")).strip()
    required_packet05_status = str(comparator_spec_policy.get("required_packet05_status", "")).strip()
    required_note_tokens = list(comparator_spec_policy.get("required_note_tokens", []))
    required_formula_phrase = str(comparator_spec_policy.get("required_formula_phrase", "")).strip()
    required_dormancy_phrase = str(comparator_spec_policy.get("required_dormancy_phrase", "")).strip()
    required_capstone_phrase = str(comparator_spec_policy.get("required_capstone_phrase", "")).strip()
    required_package_phrase = str(comparator_spec_policy.get("required_package_phrase", "")).strip()
    required_handoff_phrase = str(comparator_spec_policy.get("required_handoff_phrase", "")).strip()
    required_canonical_report_phrase = str(
        comparator_spec_policy.get("required_canonical_report_phrase", "")
    ).strip()
    required_preparation_not_progress_phrase = str(
        comparator_spec_policy.get("required_preparation_not_progress_phrase", "")
    ).strip()
    interface_object = str(comparator_spec_policy.get("interface_object", "")).strip()
    comparator_id = str(comparator_spec_policy.get("comparator_id", "")).strip()
    input_observable = str(comparator_spec_policy.get("input_observable", "")).strip()
    comparison_surface = str(comparator_spec_policy.get("comparison_surface", "")).strip()
    allowed_classes = list(comparator_spec_policy.get("allowed_classes", []))

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    formula_phrase_present = required_formula_phrase in note_text
    dormancy_phrase_present = required_dormancy_phrase in note_text
    capstone_phrase_present = required_capstone_phrase in note_text
    package_phrase_present = required_package_phrase in note_text
    handoff_phrase_present = required_handoff_phrase in note_text
    canonical_report_phrase_present = required_canonical_report_phrase in note_text
    preparation_not_progress_phrase_present = (
        required_preparation_not_progress_phrase in note_text
    )
    classes_present = all(class_name in note_text for class_name in allowed_classes)

    policy_shape_ok = all(
        key in comparator_spec_policy
        for key in [
            "target_row",
            "required_shared_interface_outcome",
            "required_concept_outcome",
            "required_packet05_decision",
            "required_packet05_status",
            "required_note_tokens",
            "required_formula_phrase",
            "required_dormancy_phrase",
            "required_capstone_phrase",
            "required_package_phrase",
            "required_handoff_phrase",
            "required_canonical_report_phrase",
            "required_preparation_not_progress_phrase",
            "interface_object",
            "comparator_id",
            "input_observable",
            "comparison_surface",
            "allowed_classes",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    preconditions_ok = (
        shared_interface_outcome == required_shared_interface_outcome
        and concept_outcome == required_concept_outcome
        and packet05_decision == required_packet05_decision
        and packet05_status == required_packet05_status
        and note_tokens_present
        and formula_phrase_present
        and dormancy_phrase_present
        and capstone_phrase_present
        and package_phrase_present
        and handoff_phrase_present
        and canonical_report_phrase_present
        and preparation_not_progress_phrase_present
        and classes_present
        and bool(target_row)
        and bool(interface_object)
        and bool(comparator_id)
        and bool(input_observable)
        and bool(comparison_surface)
        and len(allowed_classes) == 3
    )

    allowed_outcomes = set(comparator_spec_contract.get("allowed_outcomes", []))
    default_outcome = str(
        comparator_spec_contract.get("default_outcome", "GR_ROW_001_COMPARATOR_SPEC_EVIDENCE_INCOMPLETE")
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_GR_ROW_001_COMPARATOR_SPEC_REPAIR"
        next_action = "REPAIR_GR_ROW_001_COMPARATOR_SPECIFICATION_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "GR_ROW_001_COMPARATOR_SPEC_DECLARED"
        next_action = "STOP_DORMANT_GR_LAYERING_UNTIL_P75_AND_P77_CLEAR_OR_A_NEW_DISTINCT_AMBIGUITY_IS_IDENTIFIED"
    else:
        terminal_outcome = "GR_ROW_001_COMPARATOR_SPEC_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_GR_ROW_001_COMPARATOR_SPEC_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    comparator_summary = {
        "target_row": target_row,
        "interface_object": interface_object,
        "comparator_id": comparator_id,
        "input_observable": input_observable,
        "comparison_surface": comparison_surface,
        "allowed_classes": allowed_classes,
        "execution_policy": "NONEXECUTING_SPECIFICATION_ONLY_UNTIL_P75_AND_P77_CLEAR",
        "classification_only": True,
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "shared_interface_outcome_match": shared_interface_outcome == required_shared_interface_outcome,
            "concept_outcome_match": concept_outcome == required_concept_outcome,
            "packet05_decision_match": packet05_decision == required_packet05_decision,
            "packet05_status_match": packet05_status == required_packet05_status,
            "note_tokens_present": note_tokens_present,
            "formula_phrase_present": formula_phrase_present,
            "dormancy_phrase_present": dormancy_phrase_present,
            "capstone_phrase_present": capstone_phrase_present,
            "package_phrase_present": package_phrase_present,
            "handoff_phrase_present": handoff_phrase_present,
            "canonical_report_phrase_present": canonical_report_phrase_present,
            "preparation_not_progress_phrase_present": preparation_not_progress_phrase_present,
            "comparator_classes_present": classes_present,
            "single_terminal_outcome_rule_declared": str(
                comparator_spec_contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_GR_ROW_001_COMPARATOR_SPECIFICATION_OUTCOME",
            "no_loop_rule_declared": str(comparator_spec_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_ROW_001_COMPARATOR_SPECIFICATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "comparator_spec_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "target_row": target_row,
                "shared_interface_outcome": shared_interface_outcome,
                "required_shared_interface_outcome": required_shared_interface_outcome,
                "concept_outcome": concept_outcome,
                "required_concept_outcome": required_concept_outcome,
                "packet05_decision": packet05_decision,
                "required_packet05_decision": required_packet05_decision,
                "packet05_status": packet05_status,
                "required_packet05_status": required_packet05_status,
                "interface_object": interface_object,
                "comparator_id": comparator_id,
                "input_observable": input_observable,
                "comparison_surface": comparison_surface,
                "allowed_classes": allowed_classes,
                "capstone_phrase_present": capstone_phrase_present,
                "package_phrase_present": package_phrase_present,
                "handoff_phrase_present": handoff_phrase_present,
                "canonical_report_phrase_present": canonical_report_phrase_present,
                "preparation_not_progress_phrase_present": preparation_not_progress_phrase_present,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "comparator_spec_summary": comparator_summary,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": target_row,
            "comparator_id": comparator_id,
            "comparison_surface": comparison_surface,
            "package_status": "CANONICAL_DORMANT_GR_DESIGN_PACKAGE",
            "canonical_report_status": "CANONICAL_DORMANT_GR_DESIGN_HANDOFF_REPORT",
            "interpretation_boundary": "PREPARATION_NOT_EXECUTION_PROGRESS",
            "next_action": next_action,
            "single_layer_only": bool(comparator_spec_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(comparator_spec_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_row_001_shared_interface_declaration_report": _ptr(shared_interface_path),
            "gr_row_001_new_structure_concept_packet_report": _ptr(concept_path),
            "gr_empirical_comparison_packet_05_artifact": _ptr(packet05_path),
            "comparator_spec_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local GR row 001 comparator specification report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR row 001 comparator specification report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_row_001_comparator_specification_20260413_v0.json",
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
        "gr_row_001_comparator_specification_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())