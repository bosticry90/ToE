from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_20260411_v0.json"
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
    proposal_scope = dict(declaration.get("proposal_scope", {}))
    proposal_contract = dict(declaration.get("proposal_contract", {}))

    routing_refresh_path = REPO_ROOT / str(
        required_inputs.get("discovery_external_path_routing_refresh_report", "")
    ).strip()
    qm_status_path = REPO_ROOT / str(required_inputs.get("qm_stat_cycle11_lane_status_report", "")).strip()
    feasibility_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_transition_dynamics_feasibility_review_report", "")
    ).strip()
    sigma_db_path = REPO_ROOT / str(required_inputs.get("qm_stat_rl10_sigma_db_transformation_report", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()

    routing_refresh = _read_json(routing_refresh_path)
    qm_status = _read_json(qm_status_path)
    feasibility = _read_json(feasibility_path)
    sigma_db = _read_json(sigma_db_path)
    comparator = _read_json(comparator_path)

    routing_summary = dict(routing_refresh.get("summary", {}))
    qm_summary = dict(qm_status.get("summary", {}))
    feasibility_summary = dict(feasibility.get("summary", {}))
    sigma_db_summary = dict(sigma_db.get("summary", {}))
    comparator_summary = dict(comparator.get("summary", {}))

    remaining_external_path_candidate_count = int(routing_summary.get("remaining_external_path_candidate_count", 0))
    routing_refresh_outcome = str(routing_summary.get("refresh_outcome", "")).strip()
    qm_externalization_status = str(qm_summary.get("externalization_status", "")).strip()
    qm_internal_lane_status = str(qm_summary.get("internal_lane_status", "")).strip()
    transition_feasibility_outcome = str(feasibility_summary.get("review_outcome", "")).strip()
    resulting_model_class = str(feasibility_summary.get("resulting_model_class", "")).strip()
    sigma_proxy_missing = not bool(sigma_db_summary.get("sigma_proxy_definable_from_current_qm_stat_surfaces", False))
    db_residual_missing = not bool(sigma_db_summary.get("db_residual_definable_from_current_qm_stat_surfaces", False))
    sigma_required = list(sigma_db_summary.get("sigma_proxy_assumptions_required", []))
    db_required = list(sigma_db_summary.get("db_residual_assumptions_required", []))
    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()
    baseline_id = str(comparator_summary.get("baseline_id", "")).strip()

    proposed_seam_model_class_id = str(proposal_scope.get("proposed_seam_model_class_id", "")).strip()
    bounded_first_test_id = str(proposal_scope.get("bounded_first_test_id", "")).strip()
    bounded_first_test_description = str(proposal_scope.get("bounded_first_test_description", "")).strip()

    baseline_comparator_compatible = (
        comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        and baseline_id == str(proposal_scope.get("baseline_comparator_id", "")).strip()
    )
    missing_structure_is_specific = sigma_proxy_missing and db_residual_missing and bool(sigma_required) and bool(db_required)
    new_model_needed = (
        qm_externalization_status == "OUT_OF_SCOPE_UNDER_CYCLE11"
        and transition_feasibility_outcome == "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE"
        and resulting_model_class == "NEW_SEAM_OR_MODEL_CLASS_REQUIRED"
    )
    no_current_external_candidate = (
        routing_refresh_outcome == "QM_STAT_EXCLUDED_NO_EXTERNAL_PATH_CANDIDATE_REMAINS"
        and remaining_external_path_candidate_count == 0
    )
    proposal_defined = bool(proposed_seam_model_class_id and bounded_first_test_id and bounded_first_test_description)

    if proposal_defined and no_current_external_candidate and new_model_needed and missing_structure_is_specific and baseline_comparator_compatible:
        proposal_outcome = "NEW_SEAM_MODEL_PROPOSAL_JUSTIFIED"
        next_action = "MATERIALIZE_ONE_BOUNDED_FIRST_TEST_PACKET_FOR_QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM"
    elif not proposal_defined or not baseline_comparator_compatible:
        proposal_outcome = "PROPOSAL_UNDERDEFINED"
        next_action = "COMPLETE_PROPOSAL_SCOPE_AND_BASELINE_COMPATIBILITY_FIELDS_ONCE"
    else:
        proposal_outcome = "NO_NEW_SEAM_MODEL_CLASS_JUSTIFIED_YET"
        next_action = "MAINTAIN_DISCOVERY_HOLD_UNTIL_STRONGER_MISSING_STRUCTURE_OR_EXTERNAL_PATH_CASE_EMERGES"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "no_current_external_path_candidate_remains": no_current_external_candidate,
            "qm_stat_cycle11_externalization_closed": qm_externalization_status == "OUT_OF_SCOPE_UNDER_CYCLE11",
            "new_model_class_required_by_feasibility_review": new_model_needed,
            "missing_transition_structure_is_specific": missing_structure_is_specific,
            "single_baseline_comparator_compatible": baseline_comparator_compatible,
            "no_loop_rule_declared": str(proposal_contract.get("no_loop_rule", "")).strip()
            == "ONE_NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": proposal_outcome
                in set(proposal_contract.get("allowed_outcomes", [])),
                "new_seam_model_class_named": bool(proposed_seam_model_class_id),
                "bounded_first_test_named": bool(bounded_first_test_id and bounded_first_test_description),
                "existing_lane_reopen_block_preserved": str(proposal_contract.get("no_existing_lane_reopen_rule", "")).strip()
                == "DO_NOT_REOPEN_EXISTING_QM_STAT_OR_OTHER_CYCLE11_LANES_FROM_THIS_PROPOSAL",
            },
            "inputs": {
                "proposed_seam_model_class_id": proposed_seam_model_class_id,
                "target_row_family": proposal_scope.get("target_row_family"),
                "baseline_comparator_id": proposal_scope.get("baseline_comparator_id"),
                "baseline_comparator_status": comparator_status,
                "missing_external_path_structures": proposal_scope.get("missing_external_path_structures", []),
                "sigma_proxy_assumptions_required": sigma_required,
                "db_residual_assumptions_required": db_required,
                "non_insertability_claim": proposal_scope.get("non_insertability_claim"),
                "bounded_first_test_id": bounded_first_test_id,
                "bounded_first_test_description": bounded_first_test_description,
                "routing_refresh_outcome": routing_refresh_outcome,
                "qm_internal_lane_status": qm_internal_lane_status,
                "qm_externalization_status": qm_externalization_status,
                "transition_dynamics_feasibility_outcome": transition_feasibility_outcome,
                "resulting_model_class": resulting_model_class,
            },
            "summary": {
                "all_criteria_satisfied": proposal_outcome != "PROPOSAL_UNDERDEFINED",
                "phase_status": "COMPLETE" if proposal_outcome != "PROPOSAL_UNDERDEFINED" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "proposal_outcome": proposal_outcome,
            "proposed_seam_model_class_id": proposed_seam_model_class_id,
            "missing_external_path_structure_added": proposal_scope.get("missing_external_path_structures", []),
            "why_not_insertable_into_qm_stat_cycle11": proposal_scope.get("non_insertability_claim"),
            "baseline_comparator_compatible": baseline_comparator_compatible,
            "bounded_first_test_id": bounded_first_test_id,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_external_path_routing_refresh_report": _ptr(routing_refresh_path),
            "qm_stat_cycle11_lane_status_report": _ptr(qm_status_path),
            "qm_stat_transition_dynamics_feasibility_review_report": _ptr(feasibility_path),
            "qm_stat_rl10_sigma_db_transformation_report": _ptr(sigma_db_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
        },
        "non_claim_boundary": "Repository-local new external-path seam/model-class proposal report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the new external-path seam/model-class proposal report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "new_external_path_seam_model_proposal_20260411_v0.json",
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
        "new_external_path_seam_model_proposal_report: "
        f"proposal_outcome={payload['summary']['proposal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
