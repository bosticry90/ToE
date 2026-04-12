from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SHARED_MODEL_CLASS_BINDING_REFINEMENT_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_BINDING_REFINEMENT_20260412_v0.json"
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
    refinement_policy = dict(declaration.get("refinement_policy", {}))
    refinement_contract = dict(declaration.get("refinement_contract", {}))

    binding_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_comparator_binding_execution_report", "")
    ).strip()
    interpretation_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_post_signal_interpretation_report", "")
    ).strip()
    first_test_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_first_bounded_test_packet_report", "")
    ).strip()
    proposal_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_program_proposal_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    binding = _read_json(binding_path)
    interpretation = _read_json(interpretation_path)
    first_test = _read_json(first_test_path)
    proposal = _read_json(proposal_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    binding_outcome = str(dict(binding.get("summary", {})).get("terminal_outcome", "")).strip()
    binding_next_action = str(dict(binding.get("summary", {})).get("next_action", "")).strip()
    interpretation_outcome = str(dict(interpretation.get("summary", {})).get("terminal_outcome", "")).strip()
    first_test_outcome = str(dict(first_test.get("summary", {})).get("terminal_outcome", "")).strip()
    proposal_outcome = str(dict(proposal.get("summary", {})).get("terminal_outcome", "")).strip()

    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_binding_outcome = str(refinement_policy.get("required_binding_outcome", "")).strip()
    required_binding_next_action = str(refinement_policy.get("required_binding_next_action", "")).strip()
    required_interpretation_outcome = str(refinement_policy.get("required_interpretation_outcome", "")).strip()
    required_first_test_outcome = str(refinement_policy.get("required_first_test_outcome", "")).strip()
    required_proposal_outcome = str(refinement_policy.get("required_proposal_outcome", "")).strip()
    qm_stat_required_review_outcome = str(refinement_policy.get("qm_stat_required_review_outcome", "")).strip()
    gr_required_outcome = str(refinement_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(refinement_policy.get("em_qft_required_outcome", "")).strip()

    weakness = dict(refinement_policy.get("binding_weakness", {}))
    refinement = dict(refinement_policy.get("single_refinement", {}))

    single_comparator_only = bool(refinement_policy.get("single_comparator_only", False))
    single_quantity_only = bool(refinement_policy.get("single_quantity_only", False))
    no_scope_widening = bool(refinement_policy.get("no_scope_widening", False))
    refinement_executable = bool(refinement_policy.get("refinement_executable_under_declared_structure", False))
    binding_confirmed = bool(refinement_policy.get("binding_confirmed", False))
    probe_ready = bool(refinement_policy.get("probe_ready", False))
    binding_still_partial_hold = bool(refinement_policy.get("binding_still_partial_hold", False))
    requires_undeclared_structure = bool(refinement_policy.get("requires_undeclared_structure", False))

    weakness_declared = str(weakness.get("weakness_id", "")).strip() != ""
    refinement_declared = str(refinement.get("refinement_id", "")).strip() != ""

    preconditions_ok = (
        binding_outcome == required_binding_outcome
        and binding_next_action == required_binding_next_action
        and interpretation_outcome == required_interpretation_outcome
        and first_test_outcome == required_first_test_outcome
        and proposal_outcome == required_proposal_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and em_qft_outcome == em_qft_required_outcome
        and gr_frozen
        and em_qft_frozen
    )

    allowed_outcomes = set(refinement_contract.get("allowed_outcomes", []))
    default_outcome = str(
        refinement_contract.get("default_outcome", "SHARED_MODEL_CLASS_BINDING_STILL_PARTIAL_HOLD")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "SHARED_MODEL_CLASS_REFINEMENT_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "RESTORE_BINDING_REFINEMENT_PRECONDITIONS"
    elif requires_undeclared_structure:
        terminal_outcome = "SHARED_MODEL_CLASS_REFINEMENT_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "DECLARE_MISSING_REFINEMENT_STRUCTURE_BEFORE_NEXT_STEP"
    elif (
        refinement_executable
        and weakness_declared
        and refinement_declared
        and single_comparator_only
        and single_quantity_only
        and no_scope_widening
        and binding_confirmed
        and probe_ready
    ):
        terminal_outcome = "SHARED_MODEL_CLASS_PROBE_READY"
        next_action = "OPEN_ONE_BOUNDED_SHARED_MODEL_CLASS_PROBE_EXECUTION_LAYER"
    elif (
        refinement_executable
        and weakness_declared
        and refinement_declared
        and single_comparator_only
        and single_quantity_only
        and no_scope_widening
        and binding_confirmed
    ):
        terminal_outcome = "SHARED_MODEL_CLASS_BINDING_CONFIRMED"
        next_action = "OPEN_PROBE_READINESS_ADJUDICATION_LAYER"
    elif (
        refinement_executable
        and weakness_declared
        and refinement_declared
        and single_comparator_only
        and single_quantity_only
        and no_scope_widening
        and binding_still_partial_hold
    ):
        terminal_outcome = "SHARED_MODEL_CLASS_BINDING_STILL_PARTIAL_HOLD"
        next_action = "OPEN_NEXT_BOUNDED_REFINEMENT_OR_HOLD_DECISION_LAYER"
    else:
        terminal_outcome = "SHARED_MODEL_CLASS_REFINEMENT_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "DECLARE_MISSING_REFINEMENT_STRUCTURE_BEFORE_NEXT_STEP"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "binding_outcome_match": binding_outcome == required_binding_outcome,
            "binding_next_action_match": binding_next_action == required_binding_next_action,
            "interpretation_outcome_match": interpretation_outcome == required_interpretation_outcome,
            "first_test_outcome_match": first_test_outcome == required_first_test_outcome,
            "proposal_outcome_match": proposal_outcome == required_proposal_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "weakness_declared": weakness_declared,
            "single_refinement_declared": refinement_declared,
            "no_scope_widening": no_scope_widening,
            "single_terminal_outcome_rule_declared": str(
                refinement_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_BINDING_REFINEMENT_OUTCOME",
            "no_loop_rule_declared": str(refinement_contract.get("no_loop_rule", "")).strip()
            == "ONE_SHARED_MODEL_CLASS_BINDING_REFINEMENT_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "refinement_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "binding_outcome": binding_outcome,
                "required_binding_outcome": required_binding_outcome,
                "binding_next_action": binding_next_action,
                "required_binding_next_action": required_binding_next_action,
                "interpretation_outcome": interpretation_outcome,
                "required_interpretation_outcome": required_interpretation_outcome,
                "first_test_outcome": first_test_outcome,
                "required_first_test_outcome": required_first_test_outcome,
                "proposal_outcome": proposal_outcome,
                "required_proposal_outcome": required_proposal_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "refinement_payload": {
            "binding_weakness": weakness,
            "single_refinement": refinement,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(refinement_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(refinement_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "shared_model_class_comparator_binding_execution_report": _ptr(binding_path),
            "shared_model_class_post_signal_interpretation_report": _ptr(interpretation_path),
            "shared_model_class_first_bounded_test_packet_report": _ptr(first_test_path),
            "shared_model_class_program_proposal_report": _ptr(proposal_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local shared model-class binding refinement report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate shared model-class binding refinement report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "shared_model_class_binding_refinement_20260412_v0.json",
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
        "shared_model_class_binding_refinement_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
