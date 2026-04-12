from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_COMPARATOR_BINDING_EXECUTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
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
    binding_policy = dict(declaration.get("binding_policy", {}))
    binding_contract = dict(declaration.get("binding_contract", {}))

    interpretation_path = REPO_ROOT / str(
        required_inputs.get("qft_gr_post_signal_interpretation_report", "")
    ).strip()
    first_test_path = REPO_ROOT / str(
        required_inputs.get("qft_gr_first_test_packet_report", "")
    ).strip()
    lane_selection_path = REPO_ROOT / str(
        required_inputs.get("science_new_untouched_lane_selection_report", "")
    ).strip()
    preservation_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_preservation_record_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_structural_gap_definition_report", "")
    ).strip()
    em_qft_path = REPO_ROOT / str(
        required_inputs.get("em_qft_higher_level_structure_review_report", "")
    ).strip()
    qm_stat_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_review_report", "")
    ).strip()

    interpretation = _read_json(interpretation_path)
    first_test = _read_json(first_test_path)
    lane_selection = _read_json(lane_selection_path)
    preservation = _read_json(preservation_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    interpretation_outcome = str(
        dict(interpretation.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    first_test_outcome = str(
        dict(first_test.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    lane_selection_outcome = str(
        dict(lane_selection.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    preservation_outcome = str(
        dict(preservation.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_interpretation_outcome = str(
        binding_policy.get("required_interpretation_outcome", "")
    ).strip()
    required_first_test_outcome = str(binding_policy.get("required_first_test_outcome", "")).strip()
    required_lane_selection_outcome = str(
        binding_policy.get("required_lane_selection_outcome", "")
    ).strip()
    required_preservation_outcome = str(
        binding_policy.get("required_preservation_outcome", "")
    ).strip()
    qm_stat_required_review_outcome = str(
        binding_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(binding_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(binding_policy.get("em_qft_required_outcome", "")).strip()

    single_comparator = dict(binding_policy.get("single_comparator", {}))
    single_bound_quantity = dict(binding_policy.get("single_bound_quantity", {}))
    binding_confirmed = bool(binding_policy.get("binding_confirmed", False))
    binding_partial_evidence = bool(binding_policy.get("binding_partial_evidence", False))
    probe_ready_now = bool(binding_policy.get("probe_ready_now", False))
    path_falsified = bool(binding_policy.get("path_falsified", False))

    preconditions_ok = (
        interpretation_outcome == required_interpretation_outcome
        and first_test_outcome == required_first_test_outcome
        and lane_selection_outcome == required_lane_selection_outcome
        and preservation_outcome == required_preservation_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and gr_frozen
        and em_qft_outcome == em_qft_required_outcome
        and em_qft_frozen
    )

    allowed_outcomes = set(binding_contract.get("allowed_outcomes", []))
    default_outcome = str(
        binding_contract.get("default_outcome", "QFT_GR_BINDING_PARTIAL_HOLD")
    ).strip()

    if not preconditions_ok or path_falsified:
        terminal_outcome = "QFT_GR_PATH_FALSIFIED"
        next_action = "CLOSE_QFT_GR_LANE_AND_REASSESS"
    elif probe_ready_now:
        terminal_outcome = "QFT_GR_PROBE_READY"
        next_action = "OPEN_QFT_GR_PROBE_EXECUTION_GATING_LAYER"
    elif binding_confirmed:
        terminal_outcome = "QFT_GR_COMPARATOR_BINDING_CONFIRMED"
        next_action = "OPEN_QFT_GR_TARGETED_PROBE_READINESS_REVIEW"
    elif binding_partial_evidence:
        terminal_outcome = "QFT_GR_BINDING_PARTIAL_HOLD"
        next_action = "OPEN_ONE_BOUNDED_QFT_GR_BINDING_REFINEMENT_LAYER"
    else:
        terminal_outcome = "QFT_GR_PATH_FALSIFIED"
        next_action = "CLOSE_QFT_GR_LANE_AND_REASSESS"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "interpretation_outcome_match": interpretation_outcome == required_interpretation_outcome,
            "first_test_outcome_match": first_test_outcome == required_first_test_outcome,
            "lane_selection_outcome_match": lane_selection_outcome == required_lane_selection_outcome,
            "preservation_outcome_match": preservation_outcome == required_preservation_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "single_terminal_outcome_rule_declared": str(
                binding_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_QFT_GR_COMPARATOR_BINDING_EXECUTION_OUTCOME",
            "no_loop_rule_declared": str(binding_contract.get("no_loop_rule", "")).strip()
            == "ONE_QFT_GR_COMPARATOR_BINDING_EXECUTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "binding_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
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
                "single_comparator": single_comparator,
                "single_bound_quantity": single_bound_quantity,
                "binding_confirmed": binding_confirmed,
                "binding_partial_evidence": binding_partial_evidence,
                "probe_ready_now": probe_ready_now,
                "path_falsified": path_falsified,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "single_comparator_id": str(single_comparator.get("comparator_id", "")).strip(),
            "single_bound_quantity_id": str(single_bound_quantity.get("quantity_id", "")).strip(),
            "next_action": next_action,
            "single_layer_only": bool(binding_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(binding_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qft_gr_post_signal_interpretation_report": _ptr(interpretation_path),
            "qft_gr_first_test_packet_report": _ptr(first_test_path),
            "science_new_untouched_lane_selection_report": _ptr(lane_selection_path),
            "science_frontier_preservation_record_report": _ptr(preservation_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local QFT-GR comparator-binding execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QFT-GR comparator-binding execution report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qft_gr_comparator_binding_execution_20260412_v0.json",
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
        "qft_gr_comparator_binding_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} "
        f"single_comparator_id={payload['summary']['single_comparator_id']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
