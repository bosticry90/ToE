from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.minimal_global_toe_mathematical_obligation_index_report import (
    DEFAULT_OUT as DEFAULT_INDEX_PATH,
    INDEX_ID as EXPECTED_INDEX_ID,
    OUTCOME_ID as EXPECTED_INDEX_OUTCOME,
    QFT_GR_CALCULATION_TARGET,
    QFT_GR_FIRST_BREAK_ROW_ID,
    QFT_GR_FIRST_REQUIRED_CALCULATION,
    SCHEMA_ID as EXPECTED_INDEX_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_RESULT_REVIEW_20260616_v0"
REVIEW_ID = "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_RESULT_REVIEW_ACCEPTS_"
    "CALCULATION_FIRST_INDEX_AND_AUTHORIZES_SELECTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "minimal_global_toe_mathematical_obligation_index_result_review_accepts_"
    "calculation_first_index_and_authorizes_selection_only"
)
CONSUMED_TARGET = "review_minimal_global_toe_mathematical_obligation_index_result"
NEXT_TARGET = "select_next_global_toe_work_target_from_mathematical_obligation_index"
NEXT_TARGET_KIND = "global_toe_calculation_target_selection"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_RESULT_REVIEW_20260616_v0.json"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MinimalGlobalToeMathematicalObligationIndexResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def build_minimal_global_toe_mathematical_obligation_index_result_review(
    *,
    index_path: Path = DEFAULT_INDEX_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    index = _read_json(index_path)
    rows = index.get("obligation_rows", [])
    qft_gr_rows = [row for row in rows if row.get("unit_id") == "QFT_GR"]
    qft_gr = qft_gr_rows[0] if qft_gr_rows else {}
    acceptance_criteria = {
        "consumes_expected_index": (
            index.get("schema_id") == EXPECTED_INDEX_SCHEMA_ID
            and index.get("index_id") == EXPECTED_INDEX_ID
            and index.get("outcome_id") == EXPECTED_INDEX_OUTCOME
            and index.get("selected_next_target") == CONSUMED_TARGET
        ),
        "index_remains_small_and_nonpromotional": (
            index.get("global_maturity_matrix_deferred") is True
            and index.get("obligation_row_count", 99) <= 8
            and index.get("theory_closure_claimed") is False
            and index.get("public_hypothesis_ready_claimed") is False
        ),
        "qft_gr_obligation_is_first_selection_candidate": (
            len(qft_gr_rows) == 1
            and qft_gr.get("first_unresolved_blocker") == QFT_GR_FIRST_BREAK_ROW_ID
            and qft_gr.get("first_required_calculation")
            == QFT_GR_FIRST_REQUIRED_CALCULATION
            and qft_gr.get("next_calculation_target") == QFT_GR_CALCULATION_TARGET
        ),
        "all_rows_are_calculation_oriented": all(
            row.get("first_required_calculation") is not None
            and row.get("mathematical_evidence", {}).get("calculation_performed")
            is False
            and row.get("calculation_status") == "BLOCKED_NOT_EXECUTED"
            for row in rows
        ),
        "selection_only_next_target": NEXT_TARGET
        == "select_next_global_toe_work_target_from_mathematical_obligation_index",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = NEXT_TARGET if accepted else "REMEDIATE_MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_REVIEW"
    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "result_review_accepted": accepted,
        "outcome_id": OUTCOME_ID if accepted else "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "reviewed_artifact_id": index.get("schema_id"),
        "reviewed_index_id": index.get("index_id"),
        "review_outcome": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "qft_gr_first_required_calculation": QFT_GR_FIRST_REQUIRED_CALCULATION,
        "qft_gr_first_break_row_id": QFT_GR_FIRST_BREAK_ROW_ID,
        "qft_gr_next_calculation_target": QFT_GR_CALCULATION_TARGET,
        "selection_only_authorized": accepted,
        "calculation_packet_not_yet_prepared_by_this_review": True,
        "source_admissibility_claimed": False,
        "qft_gr_closure_claimed": False,
        "theory_closure_claimed": False,
        "public_hypothesis_ready_claimed": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "acceptance_criteria": acceptance_criteria,
        "lean_review_file": _ptr(LEAN_REVIEW_PATH),
        "validation_policy": {
            "bounded_focused_validation_only": True,
            "full_pytest_required": False,
            "full_governance_suite_required": False,
            "full_aggregate_lean_required": False,
            "full_ci_parity_required": False,
            "full_security_scan_required": False,
        },
        "non_claim_boundary": (
            "The review accepts the minimal obligation index as a small "
            "calculation-selection support artifact only. It authorizes "
            "selection of the next calculation target, not repair execution, "
            "source admissibility, QFT-GR closure, public readiness, or "
            "master-action promotion."
        ),
    }


def write_minimal_global_toe_mathematical_obligation_index_result_review(
    *,
    index_path: Path = DEFAULT_INDEX_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_minimal_global_toe_mathematical_obligation_index_result_review(
        index_path=index_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate minimal obligation index result review JSON.")
    parser.add_argument("--index", type=Path, default=DEFAULT_INDEX_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    index_path = ns.index if ns.index.is_absolute() else (REPO_ROOT / ns.index)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_minimal_global_toe_mathematical_obligation_index_result_review(
        index_path=index_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "review_id": payload["review_id"],
                "outcome_id": payload["outcome_id"],
                "accepted": payload["accepted"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
