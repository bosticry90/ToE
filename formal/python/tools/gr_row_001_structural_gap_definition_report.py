from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_ROW_001_STRUCTURAL_GAP_DEFINITION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "GR_ROW_001_STRUCTURAL_GAP_DEFINITION_20260412_v0.json"
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
    structural_gap_policy = dict(declaration.get("structural_gap_policy", {}))
    review_contract = dict(declaration.get("review_contract", {}))

    transport_retry_path = REPO_ROOT / str(
        required_inputs.get("gr_master_action_transport_attack_retry_packet_report", "")
    ).strip()
    alignment_retry_path = REPO_ROOT / str(
        required_inputs.get("gr_regime_limit_alignment_attack_retry_packet_report", "")
    ).strip()
    transport_obligation_path = REPO_ROOT / str(
        required_inputs.get("gr_master_action_transport_obligation_declaration_report", "")
    ).strip()
    alignment_obligation_path = REPO_ROOT / str(
        required_inputs.get("gr_regime_limit_alignment_obligation_declaration_report", "")
    ).strip()

    transport_retry = _read_json(transport_retry_path)
    alignment_retry = _read_json(alignment_retry_path)
    transport_obligation = _read_json(transport_obligation_path)
    alignment_obligation = _read_json(alignment_obligation_path)

    transport_retry_summary = dict(transport_retry.get("summary", {}))
    alignment_retry_summary = dict(alignment_retry.get("summary", {}))
    transport_obligation_summary = dict(transport_obligation.get("summary", {}))
    alignment_obligation_summary = dict(alignment_obligation.get("summary", {}))

    target_row = str(structural_gap_policy.get("target_row", "")).strip()
    transport_retry_target_row = str(transport_retry_summary.get("target_row", "")).strip()
    alignment_retry_target_row = str(alignment_retry_summary.get("target_row", "")).strip()

    transport_retry_outcome = str(transport_retry_summary.get("terminal_outcome", "")).strip()
    alignment_retry_outcome = str(alignment_retry_summary.get("terminal_outcome", "")).strip()
    transport_obligation_outcome = str(transport_obligation_summary.get("terminal_outcome", "")).strip()
    alignment_obligation_outcome = str(alignment_obligation_summary.get("terminal_outcome", "")).strip()

    transport_obligation_type = str(transport_obligation_summary.get("obligation_type", "")).strip().upper()
    alignment_obligation_type = str(alignment_obligation_summary.get("obligation_type", "")).strip().upper()

    freeze_attack_class_cycling_for_row = bool(
        structural_gap_policy.get("freeze_attack_class_cycling_for_row", True)
    )
    declareable_within_current_gr_scope = bool(
        structural_gap_policy.get("declareable_within_current_gr_scope", False)
    )
    requires_new_gr_seam_or_model_class = bool(
        structural_gap_policy.get("requires_new_gr_seam_or_model_class", False)
    )
    requires_higher_level_policy = bool(structural_gap_policy.get("requires_higher_level_policy", False))

    scope_match = target_row == transport_retry_target_row == alignment_retry_target_row

    convergent_declared_but_insufficient = (
        transport_retry_outcome == "GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
        and alignment_retry_outcome
        == "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
        and transport_obligation_outcome == "GR_TRANSPORT_OBLIGATION_DECLARED"
        and alignment_obligation_outcome == "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED"
    )

    theorem_linked_pair = (
        transport_obligation_type == "THEOREM_LINKED" and alignment_obligation_type == "THEOREM_LINKED"
    )

    allowed_outcomes = set(review_contract.get("allowed_outcomes", []))
    default_outcome = str(
        review_contract.get("default_outcome", "HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS")
    ).strip()

    if not scope_match:
        terminal_outcome = "HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS"
        next_action = "RESTORE_SCOPE_ALIGNMENT_BEFORE_ANY_FURTHER_ROW_WORK"
    elif not convergent_declared_but_insufficient:
        terminal_outcome = "HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS"
        next_action = "REVERIFY_CONVERGENT_FAILURE_BASIS"
    elif requires_higher_level_policy:
        terminal_outcome = "GR_REQUIRES_HIGHER_LEVEL_POLICY"
        next_action = "OPEN_HIGHER_LEVEL_POLICY_LAYER_FOR_GR_STRUCTURE"
    elif requires_new_gr_seam_or_model_class and theorem_linked_pair:
        terminal_outcome = "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"
        next_action = "FREEZE_ROW_001_ATTACK_CLASS_CYCLING_AND_DEFINE_NEW_GR_SEAM_OR_MODEL_CLASS"
    elif declareable_within_current_gr_scope:
        terminal_outcome = "GR_HIGHER_LEVEL_STRUCTURE_DECLARABLE"
        next_action = "DECLARE_HIGHER_LEVEL_GR_STRUCTURE_IN_SCOPE_THEN_REEVALUATE_ROW_001"
    else:
        terminal_outcome = "HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS"
        next_action = "HOLD_ROW_001_AND_SHIFT_ACTIVE_EXECUTION_PRESSURE_TO_EM_QFT"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_row_scope_match": scope_match,
            "convergent_declared_but_insufficient": convergent_declared_but_insufficient,
            "theorem_linked_obligation_pair": theorem_linked_pair,
            "freeze_attack_class_cycling_for_row": freeze_attack_class_cycling_for_row,
            "single_terminal_outcome_rule_declared": str(
                review_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_GR_ROW_001_STRUCTURAL_GAP_OUTCOME",
            "no_loop_rule_declared": str(review_contract.get("no_loop_rule", "")).strip()
            == "ONE_GR_ROW_001_STRUCTURAL_GAP_DEFINITION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "convergence_evidence_sufficient": convergent_declared_but_insufficient,
            },
            "inputs": {
                "target_row": target_row,
                "transport_retry_target_row": transport_retry_target_row,
                "alignment_retry_target_row": alignment_retry_target_row,
                "transport_retry_outcome": transport_retry_outcome,
                "alignment_retry_outcome": alignment_retry_outcome,
                "transport_obligation_outcome": transport_obligation_outcome,
                "alignment_obligation_outcome": alignment_obligation_outcome,
                "transport_obligation_type": transport_obligation_type,
                "alignment_obligation_type": alignment_obligation_type,
                "declareable_within_current_gr_scope": declareable_within_current_gr_scope,
                "requires_new_gr_seam_or_model_class": requires_new_gr_seam_or_model_class,
                "requires_higher_level_policy": requires_higher_level_policy,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
                "row_001_attack_class_cycling_status": "FROZEN"
                if freeze_attack_class_cycling_for_row
                else "UNFROZEN",
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": target_row,
            "next_action": next_action,
            "row_001_attack_class_cycling_frozen": freeze_attack_class_cycling_for_row,
            "single_review_only": bool(structural_gap_policy.get("single_review_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gr_master_action_transport_attack_retry_packet_report": _ptr(transport_retry_path),
            "gr_regime_limit_alignment_attack_retry_packet_report": _ptr(alignment_retry_path),
            "gr_master_action_transport_obligation_declaration_report": _ptr(transport_obligation_path),
            "gr_regime_limit_alignment_obligation_declaration_report": _ptr(alignment_obligation_path),
        },
        "non_claim_boundary": "Repository-local GR row 001 structural-gap definition report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate GR row 001 structural-gap definition report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "gr_row_001_structural_gap_definition_20260412_v0.json",
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
        "gr_row_001_structural_gap_definition_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
