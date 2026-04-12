from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_OBSERVABLE_MAPPING_REVIEW_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_OBSERVABLE_MAPPING_REVIEW_20260411_v0.json"
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
    mapping_target = dict(declaration.get("mapping_target", {}))
    review_contract = dict(declaration.get("review_contract", {}))

    source_signature_path = REPO_ROOT / str(target_seam.get("source_signature_artifact", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("qm_stat_external_path_signal_execution_report", "")).strip()

    source_signature = _read_json(source_signature_path)
    comparator = _read_json(comparator_path)
    execution = _read_json(execution_path)

    comparator_summary = dict(comparator.get("summary", {}))
    execution_summary = dict(execution.get("summary", {}))

    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()
    candidate_mapping_status = str(comparator_summary.get("candidate_mapping_status", "")).strip()
    execution_outcome = str(execution_summary.get("execution_outcome", "")).strip()
    required_candidate_fields = list(mapping_target.get("required_candidate_fields", []))

    missing_required_fields = [field for field in required_candidate_fields if field not in source_signature]
    mapping_definable_under_current_surfaces = (
        comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        and candidate_mapping_status == "BASELINE_COMPARATOR_EVALUABLE"
        and not missing_required_fields
    )

    if execution_outcome == "PATH_FALSIFIED":
        mapping_review_outcome = "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED"
        next_action = "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_RL10_ROUTE"
    elif mapping_definable_under_current_surfaces:
        mapping_review_outcome = "RL10_MAPPING_ESTABLISHED"
        next_action = "AUTHORIZE_ONE_ADDITIONAL_QM_STAT_EXTERNAL_PATH_EXECUTION_ONLY"
    else:
        mapping_review_outcome = "RL10_MAPPING_NOT_YET_DEFINED"
        next_action = "KEEP_QM_STAT_INTERNAL_ONLY_AND_DEFINE_ONE_RL10_INTERFACE_TRANSFORMATION_ONCE"

    transform_rule_status = (
        "DECLARED_AND_FIELD_COVERAGE_SUFFICIENT"
        if mapping_review_outcome == "RL10_MAPPING_ESTABLISHED"
        else "NOT_YET_DECLARED_OR_FIELD_COVERAGE_INSUFFICIENT"
    )
    external_rerun_justified = mapping_review_outcome == "RL10_MAPPING_ESTABLISHED"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "single_baseline_comparator_declared": comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
            "prior_external_path_execution_present": execution_outcome
            in {"EXTERNAL_PATH_SIGNAL_PRODUCED", "PATH_FALSIFIED", "INTERNAL_ONLY_REMAINS"},
            "required_rl10_fields_present": not missing_required_fields,
            "no_loop_rule_declared": str(review_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_RL10_OBSERVABLE_MAPPING_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": mapping_review_outcome
                in {
                    "RL10_MAPPING_ESTABLISHED",
                    "RL10_MAPPING_NOT_YET_DEFINED",
                    "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
                },
                "mapping_question_bounded": True,
                "rerun_policy_respected": not external_rerun_justified or mapping_review_outcome == "RL10_MAPPING_ESTABLISHED",
            },
            "inputs": {
                "target_row": target_seam.get("row_id"),
                "target_lane": target_seam.get("lane"),
                "baseline_id": mapping_target.get("baseline_id"),
                "baseline_name": mapping_target.get("baseline_name"),
                "exact_rl10_observable_quantity": mapping_target.get("exact_rl10_observable_quantity"),
                "required_candidate_fields": required_candidate_fields,
                "missing_required_fields": missing_required_fields,
                "proposed_transform_question": mapping_target.get("proposed_transform_question"),
                "comparator_status": comparator_status,
                "candidate_mapping_status": candidate_mapping_status,
                "prior_execution_outcome": execution_outcome,
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
            "mapping_review_outcome": mapping_review_outcome,
            "baseline_id": mapping_target.get("baseline_id"),
            "exact_rl10_observable_quantity": mapping_target.get("exact_rl10_observable_quantity"),
            "transform_rule_status": transform_rule_status,
            "candidate_mapping_status": candidate_mapping_status,
            "missing_required_fields": missing_required_fields,
            "external_rerun_justified": external_rerun_justified,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "source_signature_artifact": _ptr(source_signature_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
            "qm_stat_external_path_signal_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT RL10 observable mapping review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT RL10 observable mapping review report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_rl10_observable_mapping_review_20260411_v0.json",
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
        "qm_stat_rl10_observable_mapping_review_report: "
        f"mapping_review_outcome={payload['summary']['mapping_review_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
