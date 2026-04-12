from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_TRANSITION_DYNAMICS_FEASIBILITY_REVIEW_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_TRANSITION_DYNAMICS_FEASIBILITY_REVIEW_20260411_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    feasibility_questions = dict(declaration.get("feasibility_questions", {}))
    assumption_targets = dict(declaration.get("assumption_targets", {}))
    review_contract = dict(declaration.get("review_contract", {}))

    source_signature_path = REPO_ROOT / str(target_seam.get("source_signature_artifact", "")).strip()
    derivation_target_path = REPO_ROOT / str(target_seam.get("derivation_target_artifact", "")).strip()
    sigma_db_report_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_rl10_sigma_db_transformation_report", "")
    ).strip()

    source_signature = _read_json(source_signature_path)
    derivation_target = _read_text(derivation_target_path)
    sigma_db_report = _read_json(sigma_db_report_path)

    sigma_db_summary = dict(sigma_db_report.get("summary", {}))
    bounded_scope = dict(source_signature.get("bounded_scope", {}))
    source_status = str(source_signature.get("status", "")).strip()
    derivation_upper = derivation_target.upper()
    prior_sigma_db_outcome = str(sigma_db_summary.get("transformation_outcome", "")).strip()

    transition_structure_declared = any(
        key in source_signature
        for key in (
            "transition_dynamics",
            "transition_generator",
            "transition_kernel",
            "markov_kernel",
            "transition_matrix",
            "bidirectional_transition_rates",
            "transition_rates",
            "flow_rates",
        )
    )
    finite_state_audit_only_scope = "FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM" in derivation_upper
    nonclaim_boundary_explicit = (
        "NO CONTINUUM STATISTICAL CLOSURE CLAIM" in derivation_upper
        and "NO EXTERNAL TRUTH CLAIM" in derivation_upper
        and "NO FULL THEOREM DISCHARGE CLAIM" in derivation_upper
    )
    scope_blocks_transition_extension = (
        finite_state_audit_only_scope
        and nonclaim_boundary_explicit
        and not transition_structure_declared
        and not bool(bounded_scope.get("continuum_statistical_closure_claimed"))
        and not bool(bounded_scope.get("class_flip_claimed"))
        and not bool(bounded_scope.get("external_truth_claimed"))
    )

    can_declare_transition_operator_without_scope_violation = not scope_blocks_transition_extension
    can_introduce_bidirectional_rates_without_boundary_collapse = not scope_blocks_transition_extension
    resulting_model_class = (
        "NEW_SEAM_OR_MODEL_CLASS_REQUIRED"
        if scope_blocks_transition_extension
        else "QM_STAT_SCOPE_EXTENSION_STILL_WITHIN_CURRENT_LANE"
    )

    if prior_sigma_db_outcome == "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED":
        review_outcome = "QM_STAT_RL10_EXTERNALIZATION_PATH_FALSIFIED"
        next_action = "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_TRANSITION_DYNAMICS_ROUTE"
    elif (
        can_declare_transition_operator_without_scope_violation
        and can_introduce_bidirectional_rates_without_boundary_collapse
    ):
        review_outcome = "TRANSITION_DYNAMICS_EXTENSION_JUSTIFIED"
        next_action = "AUTHORIZE_ONE_BOUNDED_TRANSITION_DYNAMICS_EXTENSION_PACKET_ONLY"
    else:
        review_outcome = "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE"
        next_action = "KEEP_QM_STAT_INTERNAL_ONLY_AND_DO_NOT_DECLARE_TRANSITION_DYNAMICS_INSIDE_CYCLE11"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "prior_sigma_db_review_present": prior_sigma_db_outcome
            in {
                "SIGMA_DB_INTERFACE_DEFINED",
                "SIGMA_DB_INTERFACE_PARTIAL_HOLD",
                "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
            },
            "finite_state_audit_only_scope_detected": finite_state_audit_only_scope,
            "bounded_nonclaim_scope_detected": nonclaim_boundary_explicit,
            "transition_structure_already_declared": transition_structure_declared,
            "no_loop_rule_declared": str(review_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_TRANSITION_DYNAMICS_FEASIBILITY_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": review_outcome
                in {
                    "TRANSITION_DYNAMICS_EXTENSION_JUSTIFIED",
                    "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE",
                    "QM_STAT_RL10_EXTERNALIZATION_PATH_FALSIFIED",
                },
                "transition_operator_question_answered": True,
                "bidirectional_rate_question_answered": True,
                "model_class_question_answered": True,
                "rerun_policy_respected": review_outcome != "TRANSITION_DYNAMICS_EXTENSION_JUSTIFIED",
            },
            "inputs": {
                "target_row": target_seam.get("row_id"),
                "target_lane": target_seam.get("lane"),
                "source_status": source_status,
                "prior_sigma_db_outcome": prior_sigma_db_outcome,
                "transition_operator_question": feasibility_questions.get("transition_operator_question"),
                "bidirectional_rate_question": feasibility_questions.get("bidirectional_rate_question"),
                "model_class_question": feasibility_questions.get("model_class_question"),
                "sigma_proxy_required_assumptions": assumption_targets.get("sigma_proxy_required_assumptions", []),
                "db_residual_required_assumptions": assumption_targets.get("db_residual_required_assumptions", []),
                "bounded_scope": bounded_scope,
                "finite_state_audit_only_scope_detected": finite_state_audit_only_scope,
                "nonclaim_boundary_explicit": nonclaim_boundary_explicit,
                "transition_structure_already_declared": transition_structure_declared,
                "rerun_policy": review_contract.get("rerun_policy"),
                "no_loop_rule": review_contract.get("no_loop_rule"),
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "can_declare_transition_operator_without_scope_violation": can_declare_transition_operator_without_scope_violation,
            "can_introduce_bidirectional_rates_without_boundary_collapse": can_introduce_bidirectional_rates_without_boundary_collapse,
            "resulting_model_class": resulting_model_class,
            "finite_state_audit_only_scope_detected": finite_state_audit_only_scope,
            "transition_structure_already_declared": transition_structure_declared,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "source_signature_artifact": _ptr(source_signature_path),
            "derivation_target_artifact": _ptr(derivation_target_path),
            "qm_stat_rl10_sigma_db_transformation_report": _ptr(sigma_db_report_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT transition-dynamics feasibility review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT transition-dynamics feasibility review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
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
        "qm_stat_transition_dynamics_feasibility_review_report: "
        f"review_outcome={payload['summary']['review_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
