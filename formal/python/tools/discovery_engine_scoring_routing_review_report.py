from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DISCOVERY_ENGINE_SCORING_ROUTING_REVIEW_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_SCORING_ROUTING_REVIEW_20260411_v0.json"
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


def _as_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value)
    return None


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    review_policy = dict(declaration.get("review_policy", {}))
    review_questions = list(declaration.get("review_questions", []))

    queue_decl_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_declaration", "")).strip()
    queue_report_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()
    transition_decl_path = REPO_ROOT / str(required_inputs.get("discovery_queue_transition_declaration", "")).strip()
    transition_report_path = REPO_ROOT / str(required_inputs.get("discovery_queue_transition_decision_report", "")).strip()
    review_pass_path = REPO_ROOT / str(required_inputs.get("discovery_queue_review_pass_report", "")).strip()
    rescoring_path = REPO_ROOT / str(required_inputs.get("discovery_queue_rescoring_pass_report", "")).strip()
    checkpoint_path = REPO_ROOT / str(required_inputs.get("discovery_engine_review_checkpoint_report", "")).strip()
    qm_interp_path = REPO_ROOT / str(required_inputs.get("qm_stat_discovery_interpretation_report", "")).strip()
    qft_interp_path = REPO_ROOT / str(required_inputs.get("qft_gr_discovery_interpretation_report", "")).strip()

    queue_decl = _read_json(queue_decl_path)
    queue_report = _read_json(queue_report_path)
    transition_decl = _read_json(transition_decl_path)
    transition_report = _read_json(transition_report_path)
    review_pass = _read_json(review_pass_path)
    rescoring = _read_json(rescoring_path)
    checkpoint = _read_json(checkpoint_path)
    qm_interp = _read_json(qm_interp_path)
    qft_interp = _read_json(qft_interp_path)

    queue_decl_policy = dict(queue_decl.get("ranking_policy", {}))
    transition_policy = dict(transition_decl.get("decision_policy", {}))
    transition_summary = dict(transition_report.get("summary", {}))
    review_pass_summary = dict(review_pass.get("summary", {}))
    rescoring_summary = dict(rescoring.get("summary", {}))
    checkpoint_summary = dict(checkpoint.get("summary", {}))
    checkpoint_inputs = dict(checkpoint.get("objective_quality", {}).get("inputs", {}))
    qm_summary = dict(qm_interp.get("summary", {}))
    qft_summary = dict(qft_interp.get("summary", {}))

    score_formula = str(queue_decl_policy.get("score_formula", "")).strip()
    rank_gap_threshold = int(transition_policy.get("min_rank3_score_gap_over_rank4_for_activation", 3))
    rank_gap_after_rescoring = _as_int(rescoring_summary.get("rank_gap_after_rescoring"))
    queue_behavior_is_coherent = (
        str(transition_summary.get("selected_route", "")).strip() == "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS"
        and str(review_pass_summary.get("selected_next_route", "")).strip() == "EXECUTE_ONE_BOUNDED_QUEUE_RESCORING"
        and str(rescoring_summary.get("terminal_route", "")).strip() == "ACTIVATE_NEXT_RANKED_SEAM"
        and rank_gap_after_rescoring is not None
        and rank_gap_after_rescoring >= rank_gap_threshold
    )

    external_discriminative_leverage_established = bool(
        checkpoint_inputs.get("queue_state", {}).get("external_discriminative_leverage_established", False)
    )
    internal_only_accumulation_status = str(
        checkpoint_summary.get("internal_only_discriminator_accumulation_status", "")
    ).strip()

    qm_external_candidate = bool(qm_summary.get("externally_comparable", False)) or bool(
        qm_summary.get("numerical_probe_ready", False)
    )
    qft_external_candidate = bool(qft_summary.get("probe_ready", False)) or bool(
        qft_summary.get("probe_lane_allowed", False)
    )

    credible_external_path_signal_present = (
        external_discriminative_leverage_established and (qm_external_candidate or qft_external_candidate)
    )
    credible_external_path_signal_definition = (
        "QUEUE_EXTERNAL_DISCRIMINATIVE_LEVERAGE_ESTABLISHED_TRUE_AND_"
        "AT_LEAST_ONE_DISCOVERY_LANE_NOT_INTERNAL_ONLY_"
        "(QM_STAT_EXTERNALLY_COMPARABLE_OR_NUMERICAL_PROBE_READY_OR_QFT_GR_PROBE_READY)"
    )
    lane_expansion_reopen_condition = (
        "CREDIBLE_EXTERNAL_PATH_SIGNAL_PRESENT_AND_RANK3_OVER_RANK4_GAP_GE_3_"
        "AND_DISCOVERY_REVIEW_HOLD_RESOLVED_ONCE"
    )

    if queue_behavior_is_coherent and not credible_external_path_signal_present:
        scoring_weight_assessment = "KEEP_BASE_WEIGHTS_ADD_EXTERNAL_PATH_GATING_OVERLAY"
    elif not queue_behavior_is_coherent:
        scoring_weight_assessment = "REVIEW_WEIGHT_FORMULA_FOR_QUEUE_INCOHERENCE"
    else:
        scoring_weight_assessment = "BASE_WEIGHTS_ACCEPTABLE_FOR_REOPEN"

    if not credible_external_path_signal_present:
        routing_threshold_assessment = "RANK_GAP_THRESHOLD_3_REMAINS_NECESSARY_BUT_NOT_SUFFICIENT_WITHOUT_EXTERNAL_PATH_SIGNAL"
    else:
        routing_threshold_assessment = "RANK_GAP_THRESHOLD_3_AND_EXTERNAL_PATH_SIGNAL_SUPPORT_REOPEN"

    if queue_behavior_is_coherent and not credible_external_path_signal_present:
        selected_review_disposition = "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY"
        next_action = str(review_policy.get("default_hold_next_action", "")).strip() or (
            "MAINTAIN_DISCOVERY_HOLD_AND_REASSESS_SCORING_ROUTING_RULES_ONLY"
        )
    elif credible_external_path_signal_present and rank_gap_after_rescoring is not None and rank_gap_after_rescoring >= rank_gap_threshold:
        selected_review_disposition = "REOPEN_ONE_BOUNDED_LANE_EXPANSION"
        next_action = str(review_policy.get("default_reopen_next_action", "")).strip() or (
            "AUTHORIZE_ONE_BOUNDED_LANE_EXPANSION"
        )
    else:
        selected_review_disposition = "REPAIR_REVIEW_INPUTS_OR_POLICY"
        next_action = str(review_policy.get("default_repair_next_action", "")).strip() or (
            "RESTORE_REVIEW_INPUTS_AND_REEVALUATE_DISCOVERY_SCORING_ROUTING_ONCE"
        )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "score_formula_present": bool(score_formula),
            "queue_behavior_is_coherent": queue_behavior_is_coherent,
            "rank_gap_threshold_present": rank_gap_threshold > 0,
            "external_path_signal_present": credible_external_path_signal_present,
            "bounded_review_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "retain_base_score_formula_when_queue_behavior_is_coherent": bool(
                    review_policy.get("retain_base_score_formula_when_queue_behavior_is_coherent", True)
                ),
                "reopen_requires_external_path_signal": bool(
                    review_policy.get("require_external_path_signal_for_lane_expansion_reopen", True)
                ),
                "hold_when_internal_only_accumulation_persists": bool(
                    review_policy.get("hold_when_internal_only_accumulation_persists_without_external_path", True)
                ),
                "review_disposition_materialized": selected_review_disposition
                in {
                    "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY",
                    "REOPEN_ONE_BOUNDED_LANE_EXPANSION",
                    "REPAIR_REVIEW_INPUTS_OR_POLICY",
                },
            },
            "inputs": {
                "review_questions": review_questions,
                "score_formula": score_formula,
                "transition_rank_gap_threshold": rank_gap_threshold,
                "rank_gap_after_rescoring": rank_gap_after_rescoring,
                "internal_only_accumulation_status": internal_only_accumulation_status,
                "qm_stat_interpretation": {
                    "interpretation": qm_summary.get("interpretation"),
                    "externally_comparable": qm_summary.get("externally_comparable"),
                    "numerical_probe_ready": qm_summary.get("numerical_probe_ready"),
                },
                "qft_gr_interpretation": {
                    "interpretation": qft_summary.get("interpretation"),
                    "probe_ready": qft_summary.get("probe_ready"),
                    "probe_lane_allowed": qft_summary.get("probe_lane_allowed"),
                },
                "external_discriminative_leverage_established": external_discriminative_leverage_established,
                "checkpoint_selected_expansion_decision": checkpoint_summary.get("selected_expansion_decision"),
                "transition_selected_route": transition_summary.get("selected_route"),
                "review_selected_next_route": review_pass_summary.get("selected_next_route"),
                "rescoring_terminal_route": rescoring_summary.get("terminal_route"),
            },
            "summary": {
                "all_criteria_satisfied": selected_review_disposition != "REPAIR_REVIEW_INPUTS_OR_POLICY",
                "phase_status": "COMPLETE"
                if selected_review_disposition != "REPAIR_REVIEW_INPUTS_OR_POLICY"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "scoring_weight_assessment": scoring_weight_assessment,
            "routing_threshold_assessment": routing_threshold_assessment,
            "credible_external_path_signal_definition": credible_external_path_signal_definition,
            "credible_external_path_signal_present": credible_external_path_signal_present,
            "lane_expansion_reopen_condition": lane_expansion_reopen_condition,
            "selected_review_disposition": selected_review_disposition,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_priority_queue_declaration": _ptr(queue_decl_path),
            "discovery_priority_queue_report": _ptr(queue_report_path),
            "discovery_queue_transition_declaration": _ptr(transition_decl_path),
            "discovery_queue_transition_decision_report": _ptr(transition_report_path),
            "discovery_queue_review_pass_report": _ptr(review_pass_path),
            "discovery_queue_rescoring_pass_report": _ptr(rescoring_path),
            "discovery_engine_review_checkpoint_report": _ptr(checkpoint_path),
            "qm_stat_discovery_interpretation_report": _ptr(qm_interp_path),
            "qft_gr_discovery_interpretation_report": _ptr(qft_interp_path),
        },
        "non_claim_boundary": "Repository-local bounded discovery scoring and routing review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the discovery scoring and routing review report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "discovery_engine_scoring_routing_review_20260411_v0.json",
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
        "discovery_engine_scoring_routing_review_report: "
        f"disposition={payload['summary']['selected_review_disposition']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
