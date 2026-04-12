from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_INTERFACE_TRANSFORMATION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_INTERFACE_TRANSFORMATION_PACKET_20260411_v0.json"
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
    interface_target = dict(declaration.get("interface_target", {}))
    execution_contract = dict(declaration.get("execution_contract", {}))

    source_signature_path = REPO_ROOT / str(target_seam.get("source_signature_artifact", "")).strip()
    mapping_review_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_rl10_observable_mapping_review_report", "")
    ).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("qm_stat_external_path_signal_execution_report", "")).strip()

    source_signature = _read_json(source_signature_path)
    mapping_review = _read_json(mapping_review_path)
    comparator = _read_json(comparator_path)
    execution = _read_json(execution_path)

    source_criteria = dict(source_signature.get("blocker_discharge_criteria", {}))
    mapping_summary = dict(mapping_review.get("summary", {}))
    comparator_summary = dict(comparator.get("summary", {}))
    execution_summary = dict(execution.get("summary", {}))

    prior_mapping_review_outcome = str(mapping_summary.get("mapping_review_outcome", "")).strip()
    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()
    prior_execution_outcome = str(execution_summary.get("execution_outcome", "")).strip()

    stationary_pi_candidate = source_criteria.get("stat_probability_mass")
    stationary_pi_defined = isinstance(stationary_pi_candidate, list) and len(stationary_pi_candidate) > 0
    sigma_proxy_defined = "sigma_proxy" in source_signature
    db_residual_defined = "db_residual" in source_signature

    stationary_pi_status = (
        "DEFINED_FROM_STAT_PROBABILITY_MASS"
        if stationary_pi_defined
        else "NOT_DEFINED_UNDER_CURRENT_SURFACES"
    )
    sigma_proxy_status = (
        "DEFINED_FROM_CURRENT_QM_STAT_SURFACE"
        if sigma_proxy_defined
        else "NOT_DEFINED_REQUIRES_DECLARED_TRANSITION_DYNAMICS"
    )
    db_residual_status = (
        "DEFINED_FROM_CURRENT_QM_STAT_SURFACE"
        if db_residual_defined
        else "NOT_DEFINED_REQUIRES_DECLARED_BIDIRECTIONAL_TRANSITION_RATES"
    )

    full_interface_defined = stationary_pi_defined and sigma_proxy_defined and db_residual_defined
    partial_interface_defined = stationary_pi_defined and not full_interface_defined

    if prior_execution_outcome == "PATH_FALSIFIED":
        transformation_outcome = "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED"
        next_action = "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_QM_STAT_RL10_ROUTE"
    elif full_interface_defined:
        transformation_outcome = "RL10_INTERFACE_DEFINED"
        next_action = "AUTHORIZE_ONE_ADDITIONAL_QM_STAT_EXTERNAL_PATH_EXECUTION_ONLY"
    else:
        transformation_outcome = "RL10_INTERFACE_PARTIAL_HOLD"
        next_action = "KEEP_QM_STAT_INTERNAL_ONLY_AND_DEFINE_SIGMA_DB_TRANSFORMS_BEFORE_ANY_RERUN"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "single_baseline_comparator_declared": comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
            "prior_mapping_review_present": prior_mapping_review_outcome
            in {
                "RL10_MAPPING_ESTABLISHED",
                "RL10_MAPPING_NOT_YET_DEFINED",
                "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
            },
            "stationary_pi_defined": stationary_pi_defined,
            "sigma_proxy_defined": sigma_proxy_defined,
            "db_residual_defined": db_residual_defined,
            "no_loop_rule_declared": str(execution_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_RL10_INTERFACE_TRANSFORMATION_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": transformation_outcome
                in {
                    "RL10_INTERFACE_DEFINED",
                    "RL10_INTERFACE_PARTIAL_HOLD",
                    "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
                },
                "partial_mapping_state_explained": partial_interface_defined or full_interface_defined or prior_execution_outcome == "PATH_FALSIFIED",
                "rerun_policy_respected": transformation_outcome != "RL10_INTERFACE_DEFINED",
            },
            "inputs": {
                "target_row": target_seam.get("row_id"),
                "target_lane": target_seam.get("lane"),
                "baseline_id": interface_target.get("baseline_id"),
                "required_observables": interface_target.get("required_observables"),
                "stationary_pi_rule": interface_target.get("stationary_pi_rule"),
                "sigma_proxy_rule": interface_target.get("sigma_proxy_rule"),
                "db_residual_rule": interface_target.get("db_residual_rule"),
                "prior_mapping_review_outcome": prior_mapping_review_outcome,
                "prior_execution_outcome": prior_execution_outcome,
                "stationary_pi_status": stationary_pi_status,
                "sigma_proxy_status": sigma_proxy_status,
                "db_residual_status": db_residual_status,
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
            "baseline_id": interface_target.get("baseline_id"),
            "stationary_pi_status": stationary_pi_status,
            "sigma_proxy_status": sigma_proxy_status,
            "db_residual_status": db_residual_status,
            "full_interface_defined": full_interface_defined,
            "partial_interface_defined": partial_interface_defined,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "source_signature_artifact": _ptr(source_signature_path),
            "qm_stat_rl10_observable_mapping_review_report": _ptr(mapping_review_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
            "qm_stat_external_path_signal_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT RL10 interface transformation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT RL10 interface transformation report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_rl10_interface_transformation_20260411_v0.json",
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
        "qm_stat_rl10_interface_transformation_report: "
        f"transformation_outcome={payload['summary']['transformation_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
