from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_20260412_v0.json"
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
    routing_policy = dict(declaration.get("routing_policy", {}))
    routing_contract = dict(declaration.get("routing_contract", {}))

    post_refinement_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_post_refinement_decision_report", "")
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

    post_refinement = _read_json(post_refinement_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    post_refinement_outcome = str(
        dict(post_refinement.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_post_refinement_outcome = str(
        routing_policy.get("required_post_refinement_decision_outcome", "")
    ).strip()
    qm_stat_required_review_outcome = str(
        routing_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(routing_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(routing_policy.get("em_qft_required_outcome", "")).strip()

    reopen_discovery_queue = bool(
        routing_policy.get("reopen_discovery_queue_for_new_untouched_lane", False)
    )
    open_higher_level_policy = bool(
        routing_policy.get("open_higher_level_policy_evidence_standard_lane", False)
    )
    require_architecture_review = bool(
        routing_policy.get("require_architecture_review", False)
    )

    preconditions_ok = (
        post_refinement_outcome == required_post_refinement_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and gr_frozen
        and em_qft_outcome == em_qft_required_outcome
        and em_qft_frozen
    )

    allowed_outcomes = set(routing_contract.get("allowed_outcomes", []))
    default_outcome = str(
        routing_contract.get(
            "default_outcome",
            "PRESERVE_CURRENT_FRONTIER_AND_STOP_ACTIVE_EXECUTION",
        )
    ).strip()

    if not preconditions_ok or require_architecture_review:
        terminal_outcome = "HOLD_AND_REQUIRE_ARCHITECTURE_REVIEW"
        next_action = "OPEN_ARCHITECTURE_REVIEW_BEFORE_NEXT_STEP"
    elif open_higher_level_policy:
        terminal_outcome = "OPEN_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LANE"
        next_action = "OPEN_ONE_BOUNDED_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LAYER"
    elif reopen_discovery_queue:
        terminal_outcome = "REOPEN_DISCOVERY_QUEUE_FOR_NEW_UNTOUCHED_LANE"
        next_action = "OPEN_ONE_BOUNDED_DISCOVERY_SCORING_LAYER_FOR_NEW_UNTOUCHED_CANDIDATE"
    else:
        terminal_outcome = "PRESERVE_CURRENT_FRONTIER_AND_STOP_ACTIVE_EXECUTION"
        next_action = "NO_FURTHER_ACTIVE_EXECUTION_AUTHORIZED"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "post_refinement_outcome_match": post_refinement_outcome == required_post_refinement_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "single_terminal_outcome_rule_declared": str(
                routing_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_OUTCOME",
            "no_loop_rule_declared": str(routing_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "routing_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "post_refinement_outcome": post_refinement_outcome,
                "required_post_refinement_decision_outcome": required_post_refinement_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "reopen_discovery_queue_for_new_untouched_lane": reopen_discovery_queue,
                "open_higher_level_policy_evidence_standard_lane": open_higher_level_policy,
                "require_architecture_review": require_architecture_review,
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
            "single_layer_only": bool(routing_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(routing_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "shared_model_class_post_refinement_decision_report": _ptr(post_refinement_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local science post-shared-model-class frontier routing decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate science post-shared-model-class frontier decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_post_shared_model_class_frontier_decision_20260412_v0.json",
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
        "science_post_shared_model_class_frontier_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
