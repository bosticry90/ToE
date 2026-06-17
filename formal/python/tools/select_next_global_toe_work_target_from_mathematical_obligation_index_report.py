from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.minimal_global_toe_mathematical_obligation_index_result_review_report import (
    DEFAULT_OUT as DEFAULT_INDEX_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_INDEX_REVIEW_OUTCOME,
    REVIEW_ID as EXPECTED_INDEX_REVIEW_ID,
    SCHEMA_ID as EXPECTED_INDEX_REVIEW_SCHEMA_ID,
)
from formal.python.tools.minimal_global_toe_mathematical_obligation_index_report import (
    QFT_GR_CALCULATION_TARGET,
    QFT_GR_FIRST_BREAK_ROW_ID,
    QFT_GR_FIRST_REQUIRED_CALCULATION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "NEXT_GLOBAL_TOE_WORK_TARGET_FROM_MATHEMATICAL_OBLIGATION_INDEX_SELECTION_"
    "20260616_v0"
)
SELECTION_ID = "NEXT_GLOBAL_TOE_WORK_TARGET_FROM_MATHEMATICAL_OBLIGATION_INDEX_SELECTION_v0"
OUTCOME_ID = (
    "NEXT_GLOBAL_TOE_WORK_TARGET_FROM_MATHEMATICAL_OBLIGATION_INDEX_SELECTS_"
    "QFT_GR_WEAK_PAIRING_CALCULATION_PACKET_WITH_NO_REPAIR_EXECUTION_OR_CLOSURE"
)
SELECTION_CLASSIFICATION = (
    "next_global_toe_work_target_from_mathematical_obligation_index_selects_"
    "qft_gr_weak_pairing_calculation_packet_without_repair_execution_or_closure"
)
NEXT_TARGET = QFT_GR_CALCULATION_TARGET
NEXT_TARGET_KIND = "qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_preparation"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "NEXT_GLOBAL_TOE_WORK_TARGET_FROM_MATHEMATICAL_OBLIGATION_INDEX_"
        "SELECTION_20260616_v0.json"
    )
)
LEAN_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "NextGlobalToeWorkTargetFromMathematicalObligationIndex.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def build_select_next_global_toe_work_target_from_mathematical_obligation_index(
    *,
    index_review_path: Path = DEFAULT_INDEX_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(index_review_path)
    candidate_targets = [
        {
            "target": QFT_GR_CALCULATION_TARGET,
            "decision": "selected",
            "selection_reason": (
                "The minimal obligation index carries forward the QFT-GR "
                "first break at source action, test action, and weak-pairing "
                "domain as the most specific next calculation."
            ),
            "first_required_calculation": QFT_GR_FIRST_REQUIRED_CALCULATION,
        },
        {
            "target": "prepare_global_toe_pillar_seam_candidate_maturity_matrix",
            "decision": "deferred",
            "selection_reason": "The broad maturity matrix remains deferred.",
            "first_required_calculation": "not_selected",
        },
        {
            "target": "repair_qft_gr_source_action_test_action_and_weak_pairing_domain",
            "decision": "not_authorized",
            "selection_reason": "Repair execution is not authorized by a selector.",
            "first_required_calculation": "not_selected",
        },
    ]
    acceptance_criteria = {
        "consumes_expected_index_review": (
            review.get("schema_id") == EXPECTED_INDEX_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_INDEX_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_INDEX_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "selects_one_calculation_target": [
            row["target"] for row in candidate_targets if row["decision"] == "selected"
        ]
        == [QFT_GR_CALCULATION_TARGET],
        "qft_gr_obstruction_is_selection_basis": (
            review.get("qft_gr_first_break_row_id") == QFT_GR_FIRST_BREAK_ROW_ID
            and review.get("qft_gr_first_required_calculation")
            == QFT_GR_FIRST_REQUIRED_CALCULATION
            and review.get("qft_gr_next_calculation_target") == QFT_GR_CALCULATION_TARGET
        ),
        "selection_does_not_execute_repair": True,
    }
    selected = all(acceptance_criteria.values())
    selected_next_target = NEXT_TARGET if selected else "REMEDIATE_GLOBAL_TOE_WORK_TARGET_SELECTION"
    return {
        "schema_id": SCHEMA_ID,
        "selection_id": SELECTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "selected": selected,
        "accepted": selected,
        "outcome_id": OUTCOME_ID if selected else "NEXT_GLOBAL_TOE_WORK_TARGET_SELECTION_REQUIRES_REMEDIATION",
        "selection_classification": SELECTION_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_target_is_calculation_packet": True,
        "selected_target_executes_repair": False,
        "qft_gr_first_break_row_id": QFT_GR_FIRST_BREAK_ROW_ID,
        "qft_gr_first_required_calculation": QFT_GR_FIRST_REQUIRED_CALCULATION,
        "candidate_targets": candidate_targets,
        "candidate_target_count": len(candidate_targets),
        "selection_count": 1 if selected else 0,
        "source_admissibility_claimed": False,
        "qft_gr_closure_claimed": False,
        "theory_closure_claimed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "lean_selection_file": _ptr(LEAN_SELECTION_PATH),
        "acceptance_criteria": acceptance_criteria,
        "validation_policy": {
            "bounded_focused_validation_only": True,
            "full_pytest_required": False,
            "full_governance_suite_required": False,
            "full_aggregate_lean_required": False,
            "full_ci_parity_required": False,
            "full_security_scan_required": False,
        },
        "non_claim_boundary": (
            "The selector chooses the next calculation packet from the "
            "minimal obligation index. It does not perform repair, construct "
            "a source map, claim source admissibility, close QFT-GR, or "
            "promote the master action."
        ),
    }


def write_select_next_global_toe_work_target_from_mathematical_obligation_index(
    *,
    index_review_path: Path = DEFAULT_INDEX_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_select_next_global_toe_work_target_from_mathematical_obligation_index(
        index_review_path=index_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Select the next ToE work target from the obligation index.")
    parser.add_argument("--index-review", type=Path, default=DEFAULT_INDEX_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    index_review_path = ns.index_review if ns.index_review.is_absolute() else (REPO_ROOT / ns.index_review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_select_next_global_toe_work_target_from_mathematical_obligation_index(
        index_review_path=index_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "selection_id": payload["selection_id"],
                "outcome_id": payload["outcome_id"],
                "selected": payload["selected"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
