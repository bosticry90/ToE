from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DISCOVERY_ENGINE_REVIEW_CHECKPOINT_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_REVIEW_CHECKPOINT_20260411_v0.json"
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


def _ruling_token(payload: dict[str, Any]) -> str:
    summary = dict(payload.get("summary", {}))
    return str(summary.get("ruling", "")).strip() or str(summary.get("terminal_outcome", "")).strip()


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))
    review_questions = list(declaration.get("review_questions", []))

    transition_packet_path = REPO_ROOT / str(required_inputs.get("discovery_engine_transition_packet", "")).strip()
    queue_transition_path = REPO_ROOT / str(required_inputs.get("discovery_queue_transition_decision_report", "")).strip()
    queue_review_path = REPO_ROOT / str(required_inputs.get("discovery_queue_review_pass_report", "")).strip()
    queue_rescore_path = REPO_ROOT / str(required_inputs.get("discovery_queue_rescoring_pass_report", "")).strip()
    qm_ruling_path = REPO_ROOT / str(required_inputs.get("qm_stat_discovery_ruling_report", "")).strip()
    qm_post_path = REPO_ROOT / str(required_inputs.get("qm_stat_post_cycle_decision_report", "")).strip()
    qft_ruling_path = REPO_ROOT / str(required_inputs.get("qft_gr_discovery_ruling_report", "")).strip()
    qft_post_path = REPO_ROOT / str(required_inputs.get("qft_gr_post_cycle_decision_report", "")).strip()
    gr_tranche_path = REPO_ROOT / str(required_inputs.get("gr_discovery_discriminator_tranche_report", "")).strip()
    gr_ruling_path = REPO_ROOT / str(required_inputs.get("gr_discovery_ruling_report", "")).strip()

    transition_packet = _read_json(transition_packet_path)
    queue_transition = _read_json(queue_transition_path)
    queue_review = _read_json(queue_review_path)
    queue_rescore = _read_json(queue_rescore_path)
    qm_ruling = _read_json(qm_ruling_path)
    qm_post = _read_json(qm_post_path)
    qft_ruling = _read_json(qft_ruling_path)
    qft_post = _read_json(qft_post_path)
    gr_tranche = _read_json(gr_tranche_path)
    gr_ruling = _read_json(gr_ruling_path)

    transition_mode = dict(transition_packet.get("mode_transition", {}))
    primary_optimization_target = dict(transition_packet.get("primary_optimization_target", {}))
    queue_transition_summary = dict(queue_transition.get("summary", {}))
    queue_review_summary = dict(queue_review.get("summary", {}))
    queue_rescore_summary = dict(queue_rescore.get("summary", {}))
    qm_post_summary = dict(qm_post.get("summary", {}))
    qft_post_summary = dict(qft_post.get("summary", {}))
    gr_tranche_summary = dict(gr_tranche.get("summary", {}))
    gr_ruling_summary = dict(gr_ruling.get("summary", {}))

    pretransition_overlay_disabled = str(transition_mode.get("from", "")).strip() == "CONTROL_MODE_PRIMARY"
    current_mode = str(transition_mode.get("to", "")).strip()
    yield_priority_declared = str(primary_optimization_target.get("metric_name", "")).strip() == "DISCOVERY_YIELD"
    pretransition_baseline_yield = 0 if pretransition_overlay_disabled else None

    discovery_rulings = [
        {"lane": "QM_STAT", "ruling": _ruling_token(qm_ruling)},
        {"lane": "QFT_GR", "ruling": _ruling_token(qft_ruling)},
        {"lane": "GR", "ruling": _ruling_token(gr_ruling)},
    ]
    discriminator_output_count = sum(1 for row in discovery_rulings if row["ruling"] == "DISCRIMINATOR_PRODUCED")
    blocker_moved_count = sum(1 for row in discovery_rulings if row["ruling"] == "BLOCKER_MOVED")
    path_falsified_count = sum(1 for row in discovery_rulings if row["ruling"] == "PATH_FALSIFIED")
    retired_count = sum(1 for row in discovery_rulings if row["ruling"] == "NONPRODUCTIVE_RETIRED")
    total_discovery_yield_outputs = discriminator_output_count + blocker_moved_count + path_falsified_count
    yield_improved_vs_pretransition = (
        pretransition_baseline_yield is not None and total_discovery_yield_outputs > pretransition_baseline_yield
    )

    qm_internal_only = str(qm_post_summary.get("interpretation", "")).strip() == "INTERNAL_DISCRIMINATIVE_ONLY"
    qft_internal_only = str(qft_post_summary.get("interpretation", "")).strip() == "INTERNAL_DISCRIMINATIVE_ONLY"
    internal_only_lane_count = int(qm_internal_only) + int(qft_internal_only)

    minimum_internal_only_lanes_for_review_hold = int(
        decision_policy.get("minimum_internal_only_lanes_for_review_hold", 2)
    )
    external_discriminative_leverage_established = bool(
        queue_transition_summary.get("external_discriminative_leverage_established", False)
    )
    queue_activation_route_present = (
        str(queue_rescore_summary.get("terminal_route", "")).strip() == "ACTIVATE_NEXT_RANKED_SEAM"
    )
    gr_tranche_executable = (
        str(gr_tranche_summary.get("execution_classification", "")).strip() == "DISCOVERY_TRANCHE_EXECUTABLE"
    )
    gr_ruling_confirmed = (
        str(gr_ruling_summary.get("ruling_status", "")).strip() == "TERMINAL_OUTCOME_CONFIRMED"
        and str(gr_ruling_summary.get("ruling", "")).strip() == "DISCRIMINATOR_PRODUCED"
    )

    if yield_improved_vs_pretransition:
        discovery_yield_relative_to_pretransition_baseline = "IMPROVED_FROM_ZERO_PRETRANSITION_BASELINE"
    else:
        discovery_yield_relative_to_pretransition_baseline = "NOT_YET_IMPROVED_OR_BASELINE_UNRESOLVED"

    if internal_only_lane_count >= minimum_internal_only_lanes_for_review_hold and not external_discriminative_leverage_established:
        internal_only_discriminator_accumulation_status = "INTERNAL_ONLY_SEAMS_ACCUMULATING_WITHOUT_EXTERNAL_PATH"
    elif internal_only_lane_count >= minimum_internal_only_lanes_for_review_hold:
        internal_only_discriminator_accumulation_status = "INTERNAL_ONLY_SEAMS_ACCUMULATING_TOWARD_EXTERNAL_PATH"
    else:
        internal_only_discriminator_accumulation_status = "INTERNAL_ONLY_ACCUMULATION_NOT_YET_ESTABLISHED"

    if (
        yield_improved_vs_pretransition
        and internal_only_lane_count >= minimum_internal_only_lanes_for_review_hold
        and not external_discriminative_leverage_established
        and queue_activation_route_present
        and gr_tranche_executable
        and gr_ruling_confirmed
        and bool(decision_policy.get("pause_when_yield_improves_but_external_path_not_established", True))
    ):
        selected_expansion_decision = "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT"
        next_action = str(decision_policy.get("pause_next_action", "")).strip() or (
            "REASSESS_DISCOVERY_SCORING_ROUTING_BEFORE_ANY_FURTHER_LANE_EXPANSION"
        )
    elif (
        yield_improved_vs_pretransition
        and external_discriminative_leverage_established
        and bool(decision_policy.get("allow_expansion_only_when_external_discriminative_leverage_established", True))
    ):
        selected_expansion_decision = "ALLOW_ONE_NEW_DISCOVERY_SEAM_EXPANSION"
        next_action = str(decision_policy.get("expansion_next_action", "")).strip() or (
            "AUTHORIZE_ONE_NEW_DISCOVERY_SEAM_EXPANSION"
        )
    else:
        selected_expansion_decision = "CHECKPOINT_INPUT_REPAIR_REQUIRED_OR_REASSESSMENT_INCOMPLETE"
        next_action = str(decision_policy.get("repair_next_action", "")).strip() or (
            "RESTORE_DISCOVERY_REVIEW_INPUTS_AND_REEVALUATE_ONCE"
        )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "yield_priority_declared": yield_priority_declared,
            "pretransition_overlay_disabled": pretransition_overlay_disabled,
            "queue_activation_route_present": queue_activation_route_present,
            "gr_tranche_executable": gr_tranche_executable,
            "gr_ruling_confirmed": gr_ruling_confirmed,
            "two_internal_only_lanes_present": internal_only_lane_count >= minimum_internal_only_lanes_for_review_hold,
            "external_discriminative_leverage_established": external_discriminative_leverage_established,
            "bounded_checkpoint_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "hold_policy_declared": bool(str(decision_policy.get("hold_policy", "")).strip()),
                "yield_improvement_observed": yield_improved_vs_pretransition,
                "internal_only_accumulation_recognized": internal_only_lane_count >= minimum_internal_only_lanes_for_review_hold,
                "checkpoint_decision_materialized": selected_expansion_decision
                in {
                    "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT",
                    "ALLOW_ONE_NEW_DISCOVERY_SEAM_EXPANSION",
                    "CHECKPOINT_INPUT_REPAIR_REQUIRED_OR_REASSESSMENT_INCOMPLETE",
                },
            },
            "inputs": {
                "review_questions": review_questions,
                "pretransition_baseline_inference_rule": decision_policy.get("pretransition_baseline_inference_rule"),
                "pretransition_baseline_yield": pretransition_baseline_yield,
                "current_mode": current_mode,
                "current_discovery_yield": {
                    "discriminator_output_count": discriminator_output_count,
                    "blocker_moved_count": blocker_moved_count,
                    "path_falsified_count": path_falsified_count,
                    "retired_count": retired_count,
                    "total_discovery_yield_outputs": total_discovery_yield_outputs,
                },
                "internal_only_lanes": {
                    "qm_stat_internal_only": qm_internal_only,
                    "qft_gr_internal_only": qft_internal_only,
                    "internal_only_lane_count": internal_only_lane_count,
                },
                "queue_state": {
                    "transition_route": queue_transition_summary.get("selected_route"),
                    "review_selected_next_route": queue_review_summary.get("selected_next_route"),
                    "rescoring_terminal_route": queue_rescore_summary.get("terminal_route"),
                    "rank_gap_after_rescoring": queue_rescore_summary.get("rank_gap_after_rescoring"),
                    "external_discriminative_leverage_established": external_discriminative_leverage_established,
                },
                "gr_shadow_state": {
                    "execution_classification": gr_tranche_summary.get("execution_classification"),
                    "target_row": gr_tranche_summary.get("target_row"),
                    "ruling_status": gr_ruling_summary.get("ruling_status"),
                    "ruling": gr_ruling_summary.get("ruling"),
                },
                "hold_policy": decision_policy.get("hold_policy"),
            },
            "summary": {
                "all_criteria_satisfied": selected_expansion_decision
                != "CHECKPOINT_INPUT_REPAIR_REQUIRED_OR_REASSESSMENT_INCOMPLETE",
                "phase_status": "COMPLETE"
                if selected_expansion_decision
                != "CHECKPOINT_INPUT_REPAIR_REQUIRED_OR_REASSESSMENT_INCOMPLETE"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "discovery_yield_relative_to_pretransition_baseline": discovery_yield_relative_to_pretransition_baseline,
            "internal_only_discriminator_accumulation_status": internal_only_discriminator_accumulation_status,
            "selected_expansion_decision": selected_expansion_decision,
            "hold_policy": str(decision_policy.get("hold_policy", "")).strip(),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_engine_transition_packet": _ptr(transition_packet_path),
            "discovery_queue_transition_decision_report": _ptr(queue_transition_path),
            "discovery_queue_review_pass_report": _ptr(queue_review_path),
            "discovery_queue_rescoring_pass_report": _ptr(queue_rescore_path),
            "qm_stat_discovery_ruling_report": _ptr(qm_ruling_path),
            "qm_stat_post_cycle_decision_report": _ptr(qm_post_path),
            "qft_gr_discovery_ruling_report": _ptr(qft_ruling_path),
            "qft_gr_post_cycle_decision_report": _ptr(qft_post_path),
            "gr_discovery_discriminator_tranche_report": _ptr(gr_tranche_path),
            "gr_discovery_ruling_report": _ptr(gr_ruling_path),
        },
        "non_claim_boundary": "Repository-local discovery-engine review checkpoint report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the discovery-engine review checkpoint report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "discovery_engine_review_checkpoint_20260411_v0.json",
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
        "discovery_engine_review_checkpoint_report: "
        f"decision={payload['summary']['selected_expansion_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
