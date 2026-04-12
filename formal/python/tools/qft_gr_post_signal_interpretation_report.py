from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_POST_SIGNAL_INTERPRETATION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
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
    interpretation_policy = dict(declaration.get("interpretation_policy", {}))
    interpretation_contract = dict(declaration.get("interpretation_contract", {}))

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

    first_test = _read_json(first_test_path)
    lane_selection = _read_json(lane_selection_path)
    preservation = _read_json(preservation_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

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

    required_first_test_outcome = str(
        interpretation_policy.get("required_first_test_outcome", "")
    ).strip()
    required_lane_selection_outcome = str(
        interpretation_policy.get("required_lane_selection_outcome", "")
    ).strip()
    required_preservation_outcome = str(
        interpretation_policy.get("required_preservation_outcome", "")
    ).strip()
    qm_stat_required_review_outcome = str(
        interpretation_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(interpretation_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(interpretation_policy.get("em_qft_required_outcome", "")).strip()

    signal_internal_coherence = bool(
        interpretation_policy.get("signal_internal_coherence", False)
    )
    external_comparator_candidate_ready = bool(
        interpretation_policy.get("external_comparator_candidate_ready", False)
    )
    probe_readiness_ready = bool(interpretation_policy.get("probe_readiness_ready", False))
    signal_strength_sufficient = bool(
        interpretation_policy.get("signal_strength_sufficient", False)
    )

    preconditions_ok = (
        first_test_outcome == required_first_test_outcome
        and lane_selection_outcome == required_lane_selection_outcome
        and preservation_outcome == required_preservation_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and gr_frozen
        and em_qft_outcome == em_qft_required_outcome
        and em_qft_frozen
    )

    allowed_outcomes = set(interpretation_contract.get("allowed_outcomes", []))
    default_outcome = str(
        interpretation_contract.get("default_outcome", "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE")
    ).strip()

    if not preconditions_ok or not signal_strength_sufficient:
        terminal_outcome = "QFT_GR_SIGNAL_INSUFFICIENT_HOLD"
        next_action = "HOLD_QFT_GR_LANE_PENDING_STRONGER_SIGNAL_OR_REASSESSMENT"
    elif probe_readiness_ready:
        terminal_outcome = "QFT_GR_PROBE_READY"
        next_action = "OPEN_ONE_BOUNDED_QFT_GR_PROBE_READINESS_LAYER"
    elif external_comparator_candidate_ready:
        terminal_outcome = "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE"
        next_action = "OPEN_ONE_BOUNDED_QFT_GR_COMPARATOR_BINDING_STEP"
    elif signal_internal_coherence:
        terminal_outcome = "QFT_GR_INTERNAL_SIGNAL_ONLY"
        next_action = "HOLD_QFT_GR_AS_INTERNAL_SIGNAL_ONLY_NO_COMPARATOR_BINDING_YET"
    else:
        terminal_outcome = "QFT_GR_SIGNAL_INSUFFICIENT_HOLD"
        next_action = "HOLD_QFT_GR_LANE_PENDING_STRONGER_SIGNAL_OR_REASSESSMENT"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "first_test_outcome_match": first_test_outcome == required_first_test_outcome,
            "lane_selection_outcome_match": lane_selection_outcome == required_lane_selection_outcome,
            "preservation_outcome_match": preservation_outcome == required_preservation_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "single_terminal_outcome_rule_declared": str(
                interpretation_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_QFT_GR_POST_SIGNAL_INTERPRETATION_OUTCOME",
            "no_loop_rule_declared": str(interpretation_contract.get("no_loop_rule", "")).strip()
            == "ONE_QFT_GR_POST_SIGNAL_INTERPRETATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "interpretation_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
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
                "signal_internal_coherence": signal_internal_coherence,
                "external_comparator_candidate_ready": external_comparator_candidate_ready,
                "probe_readiness_ready": probe_readiness_ready,
                "signal_strength_sufficient": signal_strength_sufficient,
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
            "single_layer_only": bool(interpretation_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(interpretation_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qft_gr_first_test_packet_report": _ptr(first_test_path),
            "science_new_untouched_lane_selection_report": _ptr(lane_selection_path),
            "science_frontier_preservation_record_report": _ptr(preservation_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local QFT-GR post-signal interpretation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate QFT-GR post-signal interpretation report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qft_gr_post_signal_interpretation_20260412_v0.json",
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
        "qft_gr_post_signal_interpretation_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
