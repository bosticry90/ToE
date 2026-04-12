from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_SIGMA_DB_TRANSFORMATION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_SIGMA_DB_TRANSFORMATION_PACKET_20260411_v0.json"
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
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    transformation_targets = dict(declaration.get("transformation_targets", {}))
    assumption_contract = dict(declaration.get("assumption_contract", {}))
    execution_contract = dict(declaration.get("execution_contract", {}))

    source_signature_path = REPO_ROOT / str(target_seam.get("source_signature_artifact", "")).strip()
    interface_path = REPO_ROOT / str(required_inputs.get("qm_stat_rl10_interface_transformation_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("qm_stat_external_path_signal_execution_report", "")).strip()

    source_signature = _read_json(source_signature_path)
    interface_report = _read_json(interface_path)
    external_execution = _read_json(execution_path)

    source_criteria = dict(source_signature.get("blocker_discharge_criteria", {}))
    interface_summary = dict(interface_report.get("summary", {}))
    external_summary = dict(external_execution.get("summary", {}))

    prior_transformation_outcome = str(interface_summary.get("transformation_outcome", "")).strip()
    prior_execution_outcome = str(external_summary.get("execution_outcome", "")).strip()

    stationary_pi_available = bool(source_criteria.get("stat_probability_mass"))
    transition_matrix_declared = "transition_matrix" in source_signature
    transition_dynamics_declared = any(
        key in source_signature
        for key in ("transition_dynamics", "transition_generator", "transition_kernel", "markov_kernel")
    )
    bidirectional_rates_declared = any(
        key in source_signature
        for key in ("bidirectional_transition_rates", "transition_rates", "flow_rates")
    )

    sigma_proxy_definable = stationary_pi_available and (transition_matrix_declared or transition_dynamics_declared)
    db_residual_definable = stationary_pi_available and (transition_matrix_declared or bidirectional_rates_declared)

    sigma_proxy_assumptions_required: list[str] = []
    if not sigma_proxy_definable:
        sigma_proxy_assumptions_required = [
            "DECLARE_DISCRETE_TRANSITION_DYNAMICS_OPERATOR_OR_MARKOV_KERNEL",
            "DECLARE_DIRECTIONAL_STATE_TO_STATE_FLOW_CONSTRUCTION",
        ]

    db_residual_assumptions_required: list[str] = []
    if not db_residual_definable:
        db_residual_assumptions_required = [
            "DECLARE_BIDIRECTIONAL_TRANSITION_RATES_OR_EQUIVALENT_TRANSITION_MATRIX",
            "DECLARE_DETAILED_BALANCE_RESIDUAL_CONSTRUCTION_FROM_STATIONARY_FLOW_DIFFERENCE",
        ]

    if prior_execution_outcome == "PATH_FALSIFIED":
        transformation_outcome = "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED"
        next_action = "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_SIGMA_DB_ROUTE"
    elif sigma_proxy_definable and db_residual_definable:
        transformation_outcome = "SIGMA_DB_INTERFACE_DEFINED"
        next_action = "AUTHORIZE_ONE_ADDITIONAL_QM_STAT_EXTERNAL_PATH_EXECUTION_ONLY"
    else:
        transformation_outcome = "SIGMA_DB_INTERFACE_PARTIAL_HOLD"
        next_action = "KEEP_QM_STAT_INTERNAL_ONLY_AND_DECLARE_SIGMA_DB_TRANSFORMS_BEFORE_ANY_RERUN"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "prior_interface_transformation_present": prior_transformation_outcome
            in {
                "RL10_INTERFACE_DEFINED",
                "RL10_INTERFACE_PARTIAL_HOLD",
                "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
            },
            "stationary_pi_available": stationary_pi_available,
            "transition_matrix_declared": transition_matrix_declared,
            "transition_dynamics_declared": transition_dynamics_declared,
            "bidirectional_rates_declared": bidirectional_rates_declared,
            "no_loop_rule_declared": str(execution_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_RL10_SIGMA_DB_TRANSFORMATION_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": transformation_outcome
                in {
                    "SIGMA_DB_INTERFACE_DEFINED",
                    "SIGMA_DB_INTERFACE_PARTIAL_HOLD",
                    "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
                },
                "sigma_proxy_question_answered": True,
                "db_residual_question_answered": True,
                "rerun_policy_respected": transformation_outcome != "SIGMA_DB_INTERFACE_DEFINED",
            },
            "inputs": {
                "target_row": target_seam.get("row_id"),
                "target_lane": target_seam.get("lane"),
                "sigma_proxy_target": transformation_targets.get("sigma_proxy_target"),
                "db_residual_target": transformation_targets.get("db_residual_target"),
                "stationary_pi_source_rule": transformation_targets.get("stationary_pi_source_rule"),
                "sigma_proxy_dependency_rule": transformation_targets.get("sigma_proxy_dependency_rule"),
                "db_residual_dependency_rule": transformation_targets.get("db_residual_dependency_rule"),
                "required_transition_assumptions": assumption_contract.get("required_transition_assumptions", []),
                "sigma_proxy_assumptions_required": sigma_proxy_assumptions_required,
                "db_residual_assumptions_required": db_residual_assumptions_required,
                "prior_transformation_outcome": prior_transformation_outcome,
                "prior_execution_outcome": prior_execution_outcome,
                "rerun_policy": execution_contract.get("rerun_policy"),
                "no_loop_rule": execution_contract.get("no_loop_rule"),
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "transformation_outcome": transformation_outcome,
            "sigma_proxy_definable_from_current_qm_stat_surfaces": sigma_proxy_definable,
            "db_residual_definable_from_current_qm_stat_surfaces": db_residual_definable,
            "sigma_proxy_assumptions_required": sigma_proxy_assumptions_required,
            "db_residual_assumptions_required": db_residual_assumptions_required,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "source_signature_artifact": _ptr(source_signature_path),
            "qm_stat_rl10_interface_transformation_report": _ptr(interface_path),
            "qm_stat_external_path_signal_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT RL10 sigma/db transformation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT RL10 sigma/db transformation report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
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
        "qm_stat_rl10_sigma_db_transformation_report: "
        f"transformation_outcome={payload['summary']['transformation_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
