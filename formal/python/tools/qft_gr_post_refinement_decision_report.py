from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_POST_REFINEMENT_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_POST_REFINEMENT_DECISION_20260412_v0.json"
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
    decision_policy = dict(declaration.get("decision_policy", {}))
    decision_contract = dict(declaration.get("decision_contract", {}))

    binding_path = REPO_ROOT / str(
        required_inputs.get("qft_gr_comparator_binding_execution_report", "")
    ).strip()
    refinement_path = REPO_ROOT / str(required_inputs.get("qft_gr_binding_refinement_report", "")).strip()
    interpretation_path = REPO_ROOT / str(
        required_inputs.get("qft_gr_post_signal_interpretation_report", "")
    ).strip()
    first_test_path = REPO_ROOT / str(required_inputs.get("qft_gr_first_test_packet_report", "")).strip()
    lane_selection_path = REPO_ROOT / str(
        required_inputs.get("science_new_untouched_lane_selection_report", "")
    ).strip()
    preservation_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_preservation_record_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    binding = _read_json(binding_path)
    refinement = _read_json(refinement_path)
    interpretation = _read_json(interpretation_path)
    first_test = _read_json(first_test_path)
    lane_selection = _read_json(lane_selection_path)
    preservation = _read_json(preservation_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    binding_outcome = str(dict(binding.get("summary", {})).get("terminal_outcome", "")).strip()
    refinement_outcome = str(dict(refinement.get("summary", {})).get("terminal_outcome", "")).strip()
    refinement_next_action = str(dict(refinement.get("summary", {})).get("next_action", "")).strip()
    interpretation_outcome = str(dict(interpretation.get("summary", {})).get("terminal_outcome", "")).strip()
    first_test_outcome = str(dict(first_test.get("summary", {})).get("terminal_outcome", "")).strip()
    lane_selection_outcome = str(dict(lane_selection.get("summary", {})).get("terminal_outcome", "")).strip()
    preservation_outcome = str(dict(preservation.get("summary", {})).get("terminal_outcome", "")).strip()

    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_binding_outcome = str(decision_policy.get("required_binding_outcome", "")).strip()
    required_refinement_outcome = str(decision_policy.get("required_refinement_outcome", "")).strip()
    required_refinement_next_action = str(decision_policy.get("required_refinement_next_action", "")).strip()
    required_interpretation_outcome = str(decision_policy.get("required_interpretation_outcome", "")).strip()
    required_first_test_outcome = str(decision_policy.get("required_first_test_outcome", "")).strip()
    required_lane_selection_outcome = str(decision_policy.get("required_lane_selection_outcome", "")).strip()
    required_preservation_outcome = str(decision_policy.get("required_preservation_outcome", "")).strip()
    qm_stat_required_review_outcome = str(decision_policy.get("qm_stat_required_review_outcome", "")).strip()
    gr_required_outcome = str(decision_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(decision_policy.get("em_qft_required_outcome", "")).strip()

    consecutive_partial_hold_count = int(decision_policy.get("consecutive_partial_hold_count", 0))
    one_more_refinement_justified = bool(decision_policy.get("one_more_refinement_justified", False))
    higher_level_comparator_policy_required = bool(
        decision_policy.get("higher_level_comparator_policy_required", False)
    )
    path_falsified = bool(decision_policy.get("path_falsified", False))

    preconditions_ok = (
        binding_outcome == required_binding_outcome
        and refinement_outcome == required_refinement_outcome
        and refinement_next_action == required_refinement_next_action
        and interpretation_outcome == required_interpretation_outcome
        and first_test_outcome == required_first_test_outcome
        and lane_selection_outcome == required_lane_selection_outcome
        and preservation_outcome == required_preservation_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and em_qft_outcome == em_qft_required_outcome
        and gr_frozen
        and em_qft_frozen
    )

    allowed_outcomes = set(decision_contract.get("allowed_outcomes", []))
    default_outcome = str(
        decision_contract.get(
            "default_outcome",
            "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
        )
    ).strip()

    if not preconditions_ok or path_falsified:
        terminal_outcome = "QFT_GR_PATH_FALSIFIED"
        next_action = "CLOSE_QFT_GR_LANE_AND_REASSESS"
    elif higher_level_comparator_policy_required:
        terminal_outcome = "REQUIRES_HIGHER_LEVEL_COMPARATOR_POLICY"
        next_action = "OPEN_QFT_GR_HIGHER_LEVEL_COMPARATOR_POLICY_LAYER"
    elif one_more_refinement_justified and consecutive_partial_hold_count >= 2:
        terminal_outcome = "AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT"
        next_action = "OPEN_ONE_FINAL_BOUNDED_QFT_GR_REFINEMENT_LAYER"
    elif consecutive_partial_hold_count >= 2:
        terminal_outcome = "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"
        next_action = "MAINTAIN_QFT_GR_LIMITED_HOLD_AND_WAIT_FOR_STRONGER_POLICY_OR_EVIDENCE"
    else:
        terminal_outcome = "AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT"
        next_action = "OPEN_ONE_FINAL_BOUNDED_QFT_GR_REFINEMENT_LAYER"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "binding_outcome_match": binding_outcome == required_binding_outcome,
            "refinement_outcome_match": refinement_outcome == required_refinement_outcome,
            "refinement_next_action_match": refinement_next_action == required_refinement_next_action,
            "interpretation_outcome_match": interpretation_outcome == required_interpretation_outcome,
            "first_test_outcome_match": first_test_outcome == required_first_test_outcome,
            "lane_selection_outcome_match": lane_selection_outcome == required_lane_selection_outcome,
            "preservation_outcome_match": preservation_outcome == required_preservation_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "consecutive_partial_hold_threshold_met": consecutive_partial_hold_count >= 2,
            "single_terminal_outcome_rule_declared": str(
                decision_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_QFT_GR_POST_REFINEMENT_DECISION_OUTCOME",
            "no_loop_rule_declared": str(decision_contract.get("no_loop_rule", "")).strip()
            == "ONE_QFT_GR_POST_REFINEMENT_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "decision_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "binding_outcome": binding_outcome,
                "required_binding_outcome": required_binding_outcome,
                "refinement_outcome": refinement_outcome,
                "required_refinement_outcome": required_refinement_outcome,
                "refinement_next_action": refinement_next_action,
                "required_refinement_next_action": required_refinement_next_action,
                "interpretation_outcome": interpretation_outcome,
                "required_interpretation_outcome": required_interpretation_outcome,
                "first_test_outcome": first_test_outcome,
                "required_first_test_outcome": required_first_test_outcome,
                "lane_selection_outcome": lane_selection_outcome,
                "required_lane_selection_outcome": required_lane_selection_outcome,
                "preservation_outcome": preservation_outcome,
                "required_preservation_outcome": required_preservation_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "consecutive_partial_hold_count": consecutive_partial_hold_count,
                "one_more_refinement_justified": one_more_refinement_justified,
                "higher_level_comparator_policy_required": higher_level_comparator_policy_required,
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
            "single_layer_only": bool(decision_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(decision_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qft_gr_comparator_binding_execution_report": _ptr(binding_path),
            "qft_gr_binding_refinement_report": _ptr(refinement_path),
            "qft_gr_post_signal_interpretation_report": _ptr(interpretation_path),
            "qft_gr_first_test_packet_report": _ptr(first_test_path),
            "science_new_untouched_lane_selection_report": _ptr(lane_selection_path),
            "science_frontier_preservation_record_report": _ptr(preservation_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local QFT-GR post-refinement decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QFT-GR post-refinement decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_post_refinement_decision_20260412_v0.json",
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
        "qft_gr_post_refinement_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
