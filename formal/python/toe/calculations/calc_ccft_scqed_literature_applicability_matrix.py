from __future__ import annotations

import argparse
import hashlib
import json
import platform
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CALCULATION_ID = "CALC-CCFT-SCQED-LITERATURE-APPLICABILITY-MATRIX-v0"
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
INPUT_RELATIVE_PATH = (
    "formal/docs/release/SELECTED_CCFT_OPEN_SYSTEM_DECOHERENCE_"
    "SUPERCONDUCTING_CIRCUIT_QED_PLATFORM_SPECIFIC_LITERATURE_"
    "APPLICABILITY_CROSSWALK_PACKET_20260709_v0.json"
)
INPUT_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SELECTED_CCFT_OPEN_SYSTEM_DECOHERENCE_"
    "SUPERCONDUCTING_CIRCUIT_QED_PLATFORM_SPECIFIC_LITERATURE_"
    "APPLICABILITY_CROSSWALK_PACKET_RESULT_REVIEW_20260709_v0.json"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_ccft_scqed_literature_applicability_matrix.py"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/calculations/"
    "test_calc_ccft_scqed_literature_applicability_matrix.py"
)
OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-CCFT-SCQED-LITERATURE-APPLICABILITY-MATRIX-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-CCFT-SCQED-LITERATURE-APPLICABILITY-MATRIX-"
    "MANIFEST-v0.json"
)
RESULT_REVIEW_TARGET = (
    "review_calc_ccft_scqed_literature_applicability_matrix_v0_result"
)
EXECUTION_COMMAND = (
    "python -m formal.python.toe.calculations."
    "calc_ccft_scqed_literature_applicability_matrix"
)

ROW_KEY = "platform_specific_literature_applicability_crosswalk_rows"
STATUS_COUNT_KEY = (
    "platform_specific_literature_applicability_crosswalk_status_counts"
)
SUMMARY_COUNT_KEY = (
    "platform_specific_literature_applicability_crosswalk_summary_counts"
)
ALLOWED_STATUSES = (
    "platform_relevant_unvalidated",
    "partially_relevant_unvalidated",
    "unclear_requires_review",
    "blocked_missing_requirement_binding",
    "not_applicable_for_requirement",
)
RELEVANCE_STATUSES = frozenset(
    {
        "platform_relevant_unvalidated",
        "partially_relevant_unvalidated",
    }
)
BLOCKER_STATUSES = frozenset({"blocked_missing_requirement_binding"})
UNRESOLVED_REVIEW_STATUSES = frozenset({"unclear_requires_review"})
MISSING_FIELDS = (
    "missing_variables",
    "missing_units",
    "missing_assumptions",
)
REQUIRED_ROW_FIELDS = frozenset(
    {
        "crosswalk_row_id",
        "literature_review_row_id",
        "source_candidate_id",
        "source_candidate_family",
        "source_candidate_origin",
        "platform_requirement_id",
        "literature_source_locator",
        "applicability_status",
        "missing_variables",
        "missing_units",
        "missing_assumptions",
        "source_validation_status",
        "equation_adoption_status",
        "tau_baseline_status",
    }
)
NONCLAIM_IDS = (
    "NC-NO-MASTER-ACTION-PROMOTION",
    "NC-NO-PILLAR-COMPLETION",
    "NC-NO-SEAM-CLOSURE",
    "NC-NO-PHASE2",
    "NC-NO-EMPIRICAL-ADEQUACY",
    "NC-NO-CANONICAL-TOE",
    "NC-NO-QFT-GR-SOURCE-MAP-CLOSURE",
)


def _resolve(path: Path | str) -> Path:
    candidate = Path(path)
    return candidate if candidate.is_absolute() else REPO_ROOT / candidate


def _relative(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT)).replace("\\", "/")
    except ValueError:
        return str(path.resolve()).replace("\\", "/")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _status_counts(rows: Iterable[dict[str, Any]]) -> dict[str, int]:
    observed = Counter(row["applicability_status"] for row in rows)
    return {status: observed.get(status, 0) for status in ALLOWED_STATUSES}


def _missing_summary(
    rows: list[dict[str, Any]], field: str
) -> dict[str, Any]:
    occurrences: Counter[str] = Counter()
    rows_with_missing = 0
    for row in rows:
        values = row[field]
        if values:
            rows_with_missing += 1
            occurrences.update(values)
    return {
        "total_occurrences": sum(occurrences.values()),
        "rows_with_missing": rows_with_missing,
        "rows_without_missing": len(rows) - rows_with_missing,
        "unique_item_count": len(occurrences),
        "occurrence_counts": dict(sorted(occurrences.items())),
    }


def _per_source_counts(rows: list[dict[str, Any]]) -> dict[str, Any]:
    grouped: defaultdict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[row["source_candidate_id"]].append(row)

    result: dict[str, Any] = {}
    for source_id, source_rows in sorted(grouped.items()):
        result[source_id] = {
            "source_candidate_family": source_rows[0]["source_candidate_family"],
            "source_candidate_origin": source_rows[0]["source_candidate_origin"],
            "row_count": len(source_rows),
            "literature_review_row_count": len(
                {row["literature_review_row_id"] for row in source_rows}
            ),
            "literature_source_locator_count": len(
                {row["literature_source_locator"] for row in source_rows}
            ),
            "platform_requirement_count": len(
                {row["platform_requirement_id"] for row in source_rows}
            ),
            "status_counts": _status_counts(source_rows),
            "relevance_row_count": sum(
                row["applicability_status"] in RELEVANCE_STATUSES
                for row in source_rows
            ),
            "blocked_requirement_binding_row_count": sum(
                row["applicability_status"] in BLOCKER_STATUSES
                for row in source_rows
            ),
            "unclear_requires_review_row_count": sum(
                row["applicability_status"] in UNRESOLVED_REVIEW_STATUSES
                for row in source_rows
            ),
        }
    return result


def _per_locator_counts(rows: list[dict[str, Any]]) -> dict[str, Any]:
    grouped: defaultdict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[row["literature_review_row_id"]].append(row)

    result: dict[str, Any] = {}
    for literature_row_id, source_rows in sorted(grouped.items()):
        result[literature_row_id] = {
            "source_candidate_id": source_rows[0]["source_candidate_id"],
            "literature_source_locator": source_rows[0][
                "literature_source_locator"
            ],
            "row_count": len(source_rows),
            "platform_requirement_count": len(
                {row["platform_requirement_id"] for row in source_rows}
            ),
            "status_counts": _status_counts(source_rows),
        }
    return result


def _per_requirement_counts(rows: list[dict[str, Any]]) -> dict[str, Any]:
    grouped: defaultdict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[row["platform_requirement_id"]].append(row)

    result: dict[str, Any] = {}
    for requirement_id, requirement_rows in sorted(grouped.items()):
        result[requirement_id] = {
            "row_count": len(requirement_rows),
            "source_candidate_count": len(
                {row["source_candidate_id"] for row in requirement_rows}
            ),
            "literature_locator_count": len(
                {row["literature_source_locator"] for row in requirement_rows}
            ),
            "status_counts": _status_counts(requirement_rows),
            "blocked_missing_requirement_binding_count": sum(
                row["applicability_status"] in BLOCKER_STATUSES
                for row in requirement_rows
            ),
            "unclear_requires_review_count": sum(
                row["applicability_status"] in UNRESOLVED_REVIEW_STATUSES
                for row in requirement_rows
            ),
            "not_applicable_classification_count": sum(
                row["applicability_status"]
                == "not_applicable_for_requirement"
                for row in requirement_rows
            ),
            "rows_with_missing_variables": sum(
                bool(row["missing_variables"]) for row in requirement_rows
            ),
            "rows_with_missing_units": sum(
                bool(row["missing_units"]) for row in requirement_rows
            ),
            "rows_with_missing_assumptions": sum(
                bool(row["missing_assumptions"]) for row in requirement_rows
            ),
        }
    return result


def _applicability_matrix(rows: list[dict[str, Any]]) -> dict[str, Any]:
    matrix: defaultdict[str, dict[str, str]] = defaultdict(dict)
    for row in rows:
        matrix[row["literature_review_row_id"]][
            row["platform_requirement_id"]
        ] = row["applicability_status"]
    return {
        literature_row_id: dict(sorted(requirement_map.items()))
        for literature_row_id, requirement_map in sorted(matrix.items())
    }


def load_and_validate_crosswalk(input_path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    payload = json.loads(input_path.read_text(encoding="utf-8"))
    rows = payload.get(ROW_KEY)
    if not isinstance(rows, list):
        raise ValueError(f"{ROW_KEY} must be a list")
    if len(rows) != 48:
        raise ValueError(f"expected 48 crosswalk rows, found {len(rows)}")

    row_ids: set[str] = set()
    pairs: set[tuple[str, str]] = set()
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"crosswalk row {index} must be an object")
        missing_keys = REQUIRED_ROW_FIELDS - row.keys()
        if missing_keys:
            raise ValueError(
                f"crosswalk row {index} missing fields: {sorted(missing_keys)}"
            )
        row_id = row["crosswalk_row_id"]
        if row_id in row_ids:
            raise ValueError(f"duplicate crosswalk_row_id: {row_id}")
        row_ids.add(row_id)
        pair = (
            row["literature_review_row_id"],
            row["platform_requirement_id"],
        )
        if pair in pairs:
            raise ValueError(f"duplicate literature/requirement pair: {pair}")
        pairs.add(pair)
        if row["applicability_status"] not in ALLOWED_STATUSES:
            raise ValueError(
                f"unsupported applicability status: {row['applicability_status']}"
            )
        for field in MISSING_FIELDS:
            values = row[field]
            if not isinstance(values, list) or not all(
                isinstance(value, str) for value in values
            ):
                raise ValueError(f"{row_id}.{field} must be a list of strings")
        if row["source_validation_status"] != "not_validated":
            raise ValueError(f"{row_id} unexpectedly changes source validation")
        if row["equation_adoption_status"] != "not_adopted":
            raise ValueError(f"{row_id} unexpectedly changes equation adoption")
        if row["tau_baseline_status"] != "not_computed":
            raise ValueError(f"{row_id} unexpectedly changes tau_baseline status")

    literature_rows = {row["literature_review_row_id"] for row in rows}
    requirements = {row["platform_requirement_id"] for row in rows}
    locators = {row["literature_source_locator"] for row in rows}
    if len(literature_rows) != 4 or len(locators) != 4:
        raise ValueError("expected four literature rows and four locators")
    if len(requirements) != 12:
        raise ValueError("expected twelve platform requirements")
    if pairs != {
        (literature_row, requirement)
        for literature_row in literature_rows
        for requirement in requirements
    }:
        raise ValueError("crosswalk is not a complete 4 x 12 Cartesian matrix")

    computed_status_counts = _status_counts(rows)
    if payload.get(STATUS_COUNT_KEY) != computed_status_counts:
        raise ValueError("stored status counts do not match crosswalk rows")
    summary = payload.get(SUMMARY_COUNT_KEY, {})
    if summary.get("total_rows") != 48:
        raise ValueError("stored summary total_rows is not 48")
    if summary.get("validated_sources") != 0:
        raise ValueError("stored summary unexpectedly validates a source")
    if summary.get("adopted_equations") != 0:
        raise ValueError("stored summary unexpectedly adopts an equation")
    if summary.get("tau_baseline_computed") is not False:
        raise ValueError("stored summary unexpectedly computes tau_baseline")
    return payload, rows


def build_result(
    input_path: Path,
    *,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    source_payload, rows = load_and_validate_crosswalk(input_path)
    literature_rows = {row["literature_review_row_id"] for row in rows}
    source_ids = {row["source_candidate_id"] for row in rows}
    requirements = {row["platform_requirement_id"] for row in rows}
    locators = {row["literature_source_locator"] for row in rows}
    status_counts = _status_counts(rows)
    script_path = REPO_ROOT / SCRIPT_RELATIVE_PATH

    return {
        "schema_id": f"{CALCULATION_ID}-RESULT",
        "calculation_id": CALCULATION_ID,
        "calculation_status": "executed_pending_result_review",
        "captured_at_utc": captured_at_utc,
        "claim": {
            "context_type": "active_release",
            "primary_label": "E-REPRO",
            "supporting_labels": [],
            "claim_status": "generated_pending_result_review",
            "claim_scope": (
                "reproducible deterministic applicability matrix and counts only"
            ),
            "e_repro_applies_to": [
                "status distribution",
                "missing-variable counts",
                "missing-unit counts",
                "missing-assumption counts",
                "per-source applicability counts",
                "per-requirement blocker counts",
            ],
            "e_repro_does_not_apply_to": [
                "source validation or adoption",
                "equation import or adoption",
                "Lindblad or master-equation import",
                "tau_baseline or tau_candidate computation",
                "empirical r_tau calculation",
                "residual separation",
                "CCFT validation",
                "master-action promotion",
            ],
            "evidence_pointers": [
                OUTPUT_RELATIVE_PATH,
                MANIFEST_RELATIVE_PATH,
                SCRIPT_RELATIVE_PATH,
                TEST_RELATIVE_PATH,
            ],
            "nonclaim_ids": list(NONCLAIM_IDS),
            "next_work_status": RESULT_REVIEW_TARGET,
        },
        "input": {
            "path": INPUT_RELATIVE_PATH,
            "review_path": INPUT_REVIEW_RELATIVE_PATH,
            "sha256": sha256_file(input_path),
            "source_schema_id": source_payload.get("schema_id"),
            "accepted_as": "calculation_input_only",
        },
        "implementation": {
            "script_path": SCRIPT_RELATIVE_PATH,
            "script_sha256": sha256_file(script_path),
            "test_path": TEST_RELATIVE_PATH,
            "execution_command": EXECUTION_COMMAND,
            "python_version": platform.python_version(),
        },
        "matrix_dimensions": {
            "total_rows": len(rows),
            "literature_review_rows": len(literature_rows),
            "literature_source_locators": len(locators),
            "source_candidates": len(source_ids),
            "platform_requirements": len(requirements),
            "expected_cartesian_rows": len(literature_rows) * len(requirements),
            "complete_cartesian_matrix": True,
            "unique_crosswalk_row_ids": len(
                {row["crosswalk_row_id"] for row in rows}
            ),
        },
        "status_distribution": status_counts,
        "missing_field_counts": {
            field: _missing_summary(rows, field) for field in MISSING_FIELDS
        },
        "per_source_applicability_counts": _per_source_counts(rows),
        "per_literature_locator_counts": _per_locator_counts(rows),
        "per_requirement_blocker_counts": _per_requirement_counts(rows),
        "applicability_matrix": _applicability_matrix(rows),
        "classification_semantics": {
            "blocked_statuses": sorted(BLOCKER_STATUSES),
            "unresolved_review_statuses": sorted(UNRESOLVED_REVIEW_STATUSES),
            "not_applicable_for_requirement": (
                "applicability classification only, not source rejection"
            ),
            "input_classifications_modified": False,
            "scores_or_acceptance_thresholds_computed": False,
        },
        "boundary": {
            "calculation_executed": True,
            "source_validated": False,
            "source_adopted": False,
            "source_replaced": False,
            "equation_imported": False,
            "equation_adopted": False,
            "lindblad_or_master_equation_imported": False,
            "tau_baseline_computed": False,
            "tau_candidate_computed": False,
            "r_tau_empirical_value_computed": False,
            "empirical_fit_executed": False,
            "measurement_protocol_defined": False,
            "statistical_validation_performed": False,
            "residual_separation_claimed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
        },
        "result_review": {
            "status": "pending",
            "target": RESULT_REVIEW_TARGET,
        },
    }


def write_artifacts(
    *,
    input_path: Path,
    output_path: Path,
    manifest_path: Path,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> tuple[dict[str, Any], dict[str, Any]]:
    result = build_result(input_path, captured_at_utc=captured_at_utc)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    manifest = {
        "schema_id": f"{CALCULATION_ID}-MANIFEST",
        "calculation_id": CALCULATION_ID,
        "input_path": INPUT_RELATIVE_PATH,
        "input_sha256": sha256_file(input_path),
        "script_path": SCRIPT_RELATIVE_PATH,
        "script_sha256": sha256_file(REPO_ROOT / SCRIPT_RELATIVE_PATH),
        "test_path": TEST_RELATIVE_PATH,
        "execution_command": EXECUTION_COMMAND,
        "python_version": platform.python_version(),
        "captured_at_utc": captured_at_utc,
        "output_path": OUTPUT_RELATIVE_PATH,
        "output_sha256": sha256_file(output_path),
        "claim_label": "E-REPRO",
        "claim_scope": "reproducible matrix/counts calculation only",
        "result_review_status": "pending",
        "result_review_target": RESULT_REVIEW_TARGET,
        "source_validation_status": "not_validated",
        "equation_adoption_status": "not_adopted",
        "tau_baseline_status": "not_computed",
    }
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return result, manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Compute the bounded CCFT SCQED literature applicability matrix "
            "counts and reproducibility manifest."
        )
    )
    parser.add_argument("--input", type=Path, default=Path(INPUT_RELATIVE_PATH))
    parser.add_argument("--output", type=Path, default=Path(OUTPUT_RELATIVE_PATH))
    parser.add_argument(
        "--manifest", type=Path, default=Path(MANIFEST_RELATIVE_PATH)
    )
    parser.add_argument("--captured-at-utc", default=CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    output_path = _resolve(args.output)
    manifest_path = _resolve(args.manifest)
    result, manifest = write_artifacts(
        input_path=_resolve(args.input),
        output_path=output_path,
        manifest_path=manifest_path,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        json.dumps(
            {
                "calculation_id": result["calculation_id"],
                "claim_label": result["claim"]["primary_label"],
                "output": _relative(output_path),
                "output_sha256": manifest["output_sha256"],
                "manifest": _relative(manifest_path),
                "result_review_target": RESULT_REVIEW_TARGET,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
