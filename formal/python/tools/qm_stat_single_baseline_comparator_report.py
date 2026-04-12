from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_SINGLE_BASELINE_COMPARATOR_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_SINGLE_BASELINE_COMPARATOR_20260411_v0.json"
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
    baseline = dict(declaration.get("baseline_comparator", {}))
    comparison_spec = dict(declaration.get("comparison_spec", {}))
    execution_policy = dict(declaration.get("execution_policy", {}))

    target_row = str(target_seam.get("row_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()
    source_signature_id = str(target_seam.get("source_signature_id", "")).strip()
    source_signature_path = REPO_ROOT / str(target_seam.get("source_signature_artifact", "")).strip()

    source_signature = _read_json(source_signature_path)
    blocker_criteria = dict(source_signature.get("blocker_discharge_criteria", {}))
    incompatibility = dict(source_signature.get("bounded_incompatibility_exclusion", {}))

    lock_path = REPO_ROOT / str(baseline.get("lock_markdown", "")).strip()
    contract_path = REPO_ROOT / str(baseline.get("front_door_contract", "")).strip()
    reference_artifact_path = REPO_ROOT / str(baseline.get("reference_artifact", "")).strip()
    candidate_artifact_path = REPO_ROOT / str(baseline.get("candidate_artifact", "")).strip()

    baseline_paths_exist = all(
        path.exists()
        for path in (
            lock_path,
            contract_path,
            reference_artifact_path,
            candidate_artifact_path,
        )
    )
    single_baseline_only = int(baseline.get("baseline_count", 0)) == 1 and bool(
        execution_policy.get("single_baseline_only", False)
    )
    comparison_method_declared = bool(str(comparison_spec.get("comparison_method", "")).strip())
    threshold_declared = bool(str(comparison_spec.get("external_comparability_threshold", "")).strip()) and bool(
        str(comparison_spec.get("numerical_probe_ready_threshold", "")).strip()
    )
    no_loop_rule_declared = (
        str(execution_policy.get("no_loop_rule", "")).strip()
        == "ONE_SINGLE_BASELINE_COMPARATOR_DECLARATION_ONLY"
    )

    source_signature_declared = (
        bool(blocker_criteria.get("shared_support"))
        and bool(blocker_criteria.get("qm_probability_mass"))
        and bool(blocker_criteria.get("stat_probability_mass"))
        and bool(blocker_criteria.get("eighteenth_central_moment"))
        and str(incompatibility.get("classification", "")).strip() == "NONCOMPATIBLE_EXCLUDED_v0"
    )

    rl10_interface_fields_present = all(
        key in source_signature for key in ("transition_matrix", "stationary_pi", "sigma_proxy", "db_residual")
    )

    declaration_complete = all(
        (
            target_row,
            target_lane,
            source_signature_id,
            str(baseline.get("baseline_id", "")).strip(),
            str(baseline.get("baseline_schema", "")).strip(),
            str(comparison_spec.get("compared_observable", "")).strip(),
        )
    )

    comparator_status = (
        "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        if declaration_complete
        and baseline_paths_exist
        and single_baseline_only
        and comparison_method_declared
        and threshold_declared
        and no_loop_rule_declared
        and source_signature_declared
        else "COMPARATOR_DECLARATION_INCOMPLETE"
    )

    candidate_mapping_status = (
        "BASELINE_COMPARATOR_EVALUABLE"
        if rl10_interface_fields_present
        else "MOMENT_PARITY_SIGNATURE_ONLY_NOT_YET_RL10_OBSERVABLE_READY"
    )

    next_action = (
        "EXECUTE_ONE_QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_ONCE"
        if comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        else "REPAIR_QM_STAT_SINGLE_BASELINE_COMPARATOR_DECLARATION_ONCE"
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "single_baseline_only": single_baseline_only,
            "baseline_paths_exist": baseline_paths_exist,
            "comparison_method_declared": comparison_method_declared,
            "threshold_declared": threshold_declared,
            "source_signature_declared": source_signature_declared,
            "no_loop_rule_declared": no_loop_rule_declared,
        },
        "objective_quality": {
            "criteria": {
                "declaration_complete": declaration_complete,
                "single_baseline_only": single_baseline_only,
                "comparator_status_materialized": comparator_status
                in {"DECLARED_COMPLETE_SINGLE_BASELINE_ONLY", "COMPARATOR_DECLARATION_INCOMPLETE"},
                "candidate_mapping_status_materialized": candidate_mapping_status
                in {
                    "BASELINE_COMPARATOR_EVALUABLE",
                    "MOMENT_PARITY_SIGNATURE_ONLY_NOT_YET_RL10_OBSERVABLE_READY",
                },
            },
            "inputs": {
                "target_row": target_row,
                "target_lane": target_lane,
                "source_signature_id": source_signature_id,
                "baseline_id": baseline.get("baseline_id"),
                "baseline_schema": baseline.get("baseline_schema"),
                "selection_reason": baseline.get("selection_reason"),
                "compared_observable": comparison_spec.get("compared_observable"),
                "comparison_method": comparison_spec.get("comparison_method"),
                "external_comparability_threshold": comparison_spec.get("external_comparability_threshold"),
                "numerical_probe_ready_threshold": comparison_spec.get("numerical_probe_ready_threshold"),
                "non_separation_rule": comparison_spec.get("non_separation_rule"),
                "single_baseline_only_rule": execution_policy.get("single_baseline_only_rule"),
                "no_loop_rule": execution_policy.get("no_loop_rule"),
            },
            "summary": {
                "all_criteria_satisfied": comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "phase_status": "COMPLETE"
                if comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "comparator_status": comparator_status,
            "baseline_id": baseline.get("baseline_id"),
            "baseline_name": baseline.get("baseline_name"),
            "baseline_schema": baseline.get("baseline_schema"),
            "target_row": target_row,
            "target_lane": target_lane,
            "compared_observable": comparison_spec.get("compared_observable"),
            "candidate_mapping_status": candidate_mapping_status,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "source_signature_artifact": _ptr(source_signature_path),
            "lock_markdown": _ptr(lock_path),
            "front_door_contract": _ptr(contract_path),
            "reference_artifact": _ptr(reference_artifact_path),
            "candidate_artifact": _ptr(candidate_artifact_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT single-baseline comparator report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT single-baseline comparator report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
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
        "qm_stat_single_baseline_comparator_report: "
        f"comparator_status={payload['summary']['comparator_status']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
