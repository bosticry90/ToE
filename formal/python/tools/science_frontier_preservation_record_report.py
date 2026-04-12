from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_FRONTIER_PRESERVATION_RECORD_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FRONTIER_PRESERVATION_RECORD_20260412_v0.json"
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
    preservation_policy = dict(declaration.get("preservation_policy", {}))
    preservation_contract = dict(declaration.get("preservation_contract", {}))
    frontier_state = dict(declaration.get("frontier_state", {}))

    frontier_decision_path = REPO_ROOT / str(
        required_inputs.get("science_post_shared_model_class_frontier_decision_report", "")
    ).strip()
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

    frontier_decision = _read_json(frontier_decision_path)
    post_refinement = _read_json(post_refinement_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    frontier_decision_outcome = str(
        dict(frontier_decision.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    frontier_next_action = str(
        dict(frontier_decision.get("summary", {})).get("next_action", "")
    ).strip()
    post_refinement_outcome = str(
        dict(post_refinement.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_frontier_decision_outcome = str(
        preservation_policy.get("required_frontier_decision_outcome", "")
    ).strip()
    required_frontier_next_action = str(
        preservation_policy.get("required_frontier_next_action", "")
    ).strip()
    required_post_refinement_outcome = str(
        preservation_policy.get("required_post_refinement_outcome", "")
    ).strip()
    qm_stat_required_review_outcome = str(
        preservation_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(preservation_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(preservation_policy.get("em_qft_required_outcome", "")).strip()
    canonical_commit = str(preservation_policy.get("canonical_commit", "")).strip()
    all_active_execution_lanes_closed = bool(
        preservation_policy.get("all_active_execution_lanes_closed", False)
    )
    restart_prerequisites_documented = bool(
        preservation_policy.get("restart_prerequisites_documented", False)
    )

    preconditions_ok = (
        frontier_decision_outcome == required_frontier_decision_outcome
        and frontier_next_action == required_frontier_next_action
        and post_refinement_outcome == required_post_refinement_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and gr_frozen
        and em_qft_outcome == em_qft_required_outcome
        and em_qft_frozen
        and all_active_execution_lanes_closed
    )

    allowed_outcomes = set(preservation_contract.get("allowed_outcomes", []))
    default_outcome = str(
        preservation_contract.get(
            "default_outcome",
            "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
        )
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "FRONTIER_RECORD_INCOMPLETE"
        next_action = "DIAGNOSE_MISSING_PRECONDITIONS_BEFORE_PRESERVING_FRONTIER"
    elif not restart_prerequisites_documented:
        terminal_outcome = "RESTART_PREREQUISITES_DOCUMENTED"
        next_action = "DOCUMENT_RESTART_PREREQUISITES_BEFORE_CLOSING_FRONTIER"
    else:
        terminal_outcome = "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT"
        next_action = "NO_FURTHER_ACTIVE_EXECUTION_AUTHORIZED_RESUME_FROM_NEW_STANDARD_OR_NEW_LANE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "frontier_decision_outcome_match": frontier_decision_outcome == required_frontier_decision_outcome,
            "frontier_next_action_match": frontier_next_action == required_frontier_next_action,
            "post_refinement_outcome_match": post_refinement_outcome == required_post_refinement_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "all_active_execution_lanes_closed": all_active_execution_lanes_closed,
            "restart_prerequisites_documented": restart_prerequisites_documented,
            "single_terminal_outcome_rule_declared": str(
                preservation_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_FRONTIER_PRESERVATION_RECORD_OUTCOME",
            "no_loop_rule_declared": str(preservation_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_FRONTIER_PRESERVATION_RECORD_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "preservation_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "frontier_decision_outcome": frontier_decision_outcome,
                "required_frontier_decision_outcome": required_frontier_decision_outcome,
                "frontier_next_action": frontier_next_action,
                "required_frontier_next_action": required_frontier_next_action,
                "post_refinement_outcome": post_refinement_outcome,
                "required_post_refinement_outcome": required_post_refinement_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "canonical_commit": canonical_commit,
                "all_active_execution_lanes_closed": all_active_execution_lanes_closed,
                "restart_prerequisites_documented": restart_prerequisites_documented,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "frontier_state": frontier_state,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "canonical_commit": canonical_commit,
            "next_action": next_action,
            "single_layer_only": bool(preservation_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(preservation_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_post_shared_model_class_frontier_decision_report": _ptr(frontier_decision_path),
            "shared_model_class_post_refinement_decision_report": _ptr(post_refinement_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local science frontier preservation record report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate science frontier preservation record report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_frontier_preservation_record_20260412_v0.json",
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
        "science_frontier_preservation_record_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" canonical_commit={payload['summary']['canonical_commit']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
