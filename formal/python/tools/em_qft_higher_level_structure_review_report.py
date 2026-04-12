from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
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
    review_policy = dict(declaration.get("review_policy", {}))
    review_contract = dict(declaration.get("review_contract", {}))

    first_test_path = REPO_ROOT / str(required_inputs.get("em_qft_seam_first_test_packet_report", "")).strip()
    decision_path = REPO_ROOT / str(required_inputs.get("em_qft_post_first_test_decision_report", "")).strip()
    packet_path = REPO_ROOT / str(required_inputs.get("em_qft_interface_alignment_packet_report", "")).strip()
    obligation_path = REPO_ROOT / str(
        required_inputs.get("em_qft_interface_alignment_obligation_declaration_report", "")
    ).strip()
    retry_path = REPO_ROOT / str(required_inputs.get("em_qft_interface_alignment_retry_packet_report", "")).strip()

    first_test = _read_json(first_test_path)
    decision = _read_json(decision_path)
    packet = _read_json(packet_path)
    obligation = _read_json(obligation_path)
    retry = _read_json(retry_path)

    first_test_outcome = str(dict(first_test.get("summary", {})).get("terminal_outcome", "")).strip()
    decision_outcome = str(dict(decision.get("summary", {})).get("terminal_outcome", "")).strip()
    packet_outcome = str(dict(packet.get("summary", {})).get("terminal_outcome", "")).strip()
    obligation_outcome = str(dict(obligation.get("summary", {})).get("terminal_outcome", "")).strip()
    obligation_type = str(dict(obligation.get("summary", {})).get("obligation_type", "")).strip().upper()
    retry_outcome = str(dict(retry.get("summary", {})).get("terminal_outcome", "")).strip()

    seam_first_test = str(dict(first_test.get("summary", {})).get("target_seam", "")).strip()
    seam_decision = str(dict(decision.get("summary", {})).get("target_seam", "")).strip()
    seam_packet = str(dict(packet.get("summary", {})).get("target_seam", "")).strip()
    seam_retry = str(dict(retry.get("summary", {})).get("target_seam", "")).strip()

    target_seam = str(review_policy.get("target_seam", "")).strip()
    freeze_attack_class_cycling_for_seam = bool(review_policy.get("freeze_attack_class_cycling_for_seam", True))
    declareable_within_current_scope = bool(review_policy.get("declareable_within_current_scope", False))
    requires_new_seam_or_model_class = bool(review_policy.get("requires_new_seam_or_model_class", False))
    requires_higher_level_policy = bool(review_policy.get("requires_higher_level_policy", False))

    scope_match = target_seam == seam_first_test == seam_decision == seam_packet == seam_retry

    convergent_pattern = (
        first_test_outcome == "EM_QFT_SEAM_VALID_BUT_NONMOVING"
        and decision_outcome == "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS"
        and packet_outcome == "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE"
        and obligation_outcome == "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED"
        and retry_outcome == "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
        and obligation_type == "THEOREM_LINKED"
    )

    allowed_outcomes = set(review_contract.get("allowed_outcomes", []))
    default_outcome = str(
        review_contract.get("default_outcome", "HOLD_EM_QFT_AND_STOP_ATTACK_CLASS_CYCLING")
    ).strip()

    if not scope_match or not convergent_pattern:
        terminal_outcome = "HOLD_EM_QFT_AND_STOP_ATTACK_CLASS_CYCLING"
        next_action = "REVERIFY_EM_QFT_CONVERGENT_STRUCTURAL_PATTERN"
    elif requires_higher_level_policy:
        terminal_outcome = "EM_QFT_REQUIRES_HIGHER_LEVEL_POLICY"
        next_action = "OPEN_HIGHER_LEVEL_POLICY_LAYER_FOR_EM_QFT_STRUCTURE"
    elif requires_new_seam_or_model_class:
        terminal_outcome = "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"
        next_action = "FREEZE_EM_QFT_ATTACK_CLASS_CYCLING_AND_DEFINE_NEW_SEAM_OR_MODEL_CLASS"
    elif declareable_within_current_scope:
        terminal_outcome = "EM_QFT_HIGHER_LEVEL_STRUCTURE_DECLARABLE"
        next_action = "DECLARE_EM_QFT_HIGHER_LEVEL_STRUCTURE_WITHIN_SCOPE"
    else:
        terminal_outcome = "HOLD_EM_QFT_AND_STOP_ATTACK_CLASS_CYCLING"
        next_action = "HOLD_EM_QFT_AND_SHIFT_ACTIVE_EXECUTION_PRESSURE_TO_NEXT_SEAM"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_seam_scope_match": scope_match,
            "convergent_structural_pattern_detected": convergent_pattern,
            "theorem_linked_obligation_type": obligation_type == "THEOREM_LINKED",
            "freeze_attack_class_cycling_for_seam": freeze_attack_class_cycling_for_seam,
            "single_terminal_outcome_rule_declared": str(
                review_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(review_contract.get("no_loop_rule", "")).strip()
            == "ONE_EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "convergence_evidence_sufficient": convergent_pattern,
            },
            "inputs": {
                "target_seam": target_seam,
                "first_test_outcome": first_test_outcome,
                "decision_outcome": decision_outcome,
                "packet_outcome": packet_outcome,
                "obligation_outcome": obligation_outcome,
                "obligation_type": obligation_type,
                "retry_outcome": retry_outcome,
                "declareable_within_current_scope": declareable_within_current_scope,
                "requires_new_seam_or_model_class": requires_new_seam_or_model_class,
                "requires_higher_level_policy": requires_higher_level_policy,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
                "em_qft_attack_class_cycling_status": "FROZEN"
                if freeze_attack_class_cycling_for_seam
                else "UNFROZEN",
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_seam": target_seam,
            "next_action": next_action,
            "em_qft_attack_class_cycling_frozen": freeze_attack_class_cycling_for_seam,
            "single_review_only": bool(review_policy.get("single_review_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "em_qft_seam_first_test_packet_report": _ptr(first_test_path),
            "em_qft_post_first_test_decision_report": _ptr(decision_path),
            "em_qft_interface_alignment_packet_report": _ptr(packet_path),
            "em_qft_interface_alignment_obligation_declaration_report": _ptr(obligation_path),
            "em_qft_interface_alignment_retry_packet_report": _ptr(retry_path),
        },
        "non_claim_boundary": "Repository-local EM-QFT higher-level structural review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate EM-QFT higher-level structure review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "em_qft_higher_level_structure_review_20260412_v0.json",
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
        "em_qft_higher_level_structure_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
