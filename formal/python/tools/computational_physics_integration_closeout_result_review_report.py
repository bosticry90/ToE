from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.computational_physics_integration_closeout_report import (
    EXPECTED_ROWS,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_NONCLAIM_INFRASTRUCTURE_STACK_"
    "AND_RETURNS_TO_MAIN_TARGET_SELECTION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_CLOSEOUT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0.json"
)

FORBIDDEN_EFFECTS = [
    "theory_validation",
    "empirical_validation",
    "referent_comparison_execution",
    "robustness_scan_execution",
    "prediction_execution",
    "falsifier_execution",
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "seam_closure",
    "phase2_authorization",
    "master_action_promotion",
    "simulation_execution",
    "validation_upgrade",
    "claim_promotion",
    "numerical_credibility_scoring",
    "external_truth_claim",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _all_final_non_execution_true(closeout: dict[str, Any]) -> bool:
    return all(value is True for value in closeout.get("final_non_execution_readout", {}).values())


def build_result_review(
    *,
    closeout_path: Path = DEFAULT_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(closeout_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    acceptance_criteria = {
        "consumes_closeout": closeout.get("closeout_id") == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0",
        "closeout_status_nonclaim": closeout.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "closeout_prepared": closeout.get("prepared") is True,
        "authorization_class_preserved": closeout.get("authorization_class")
        == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "stack_layer_count_eight": closeout.get("summary", {}).get("stack_layer_count") == 8,
        "all_result_reviews_accepted": closeout.get("all_result_reviews_accepted") is True,
        "lineage_preserved": closeout.get("lineage_preserved") is True,
        "row_ids_preserved": closeout.get("expected_row_ids") == EXPECTED_ROWS,
        "execution_claim_count_zero": int(closeout.get("execution_claim_count", -1)) == 0,
        "completion_claim_count_zero": int(closeout.get("completion_claim_count", -1)) == 0,
        "validation_upgrade_count_zero": int(closeout.get("validation_upgrade_count", -1)) == 0,
        "promotion_allowed_count_zero": int(closeout.get("promotion_allowed_count", -1)) == 0,
        "no_numerical_credibility_score": closeout.get("scoring_policy") == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "final_non_execution_readout_all_true": _all_final_non_execution_true(closeout),
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }
    accepted = all(acceptance_criteria.values())
    if accepted:
        next_action = "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
        outcome_id = OUTCOME_ID
    else:
        next_action = "REMEDIATE_COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_FAILURE"
        outcome_id = "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_closeout": {
            "closeout_id": closeout.get("closeout_id"),
            "closeout_path": _ptr(closeout_path),
            "closeout_schema_id": closeout.get("schema_id"),
            "closeout_preparation_result": closeout.get("preparation_result"),
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "stack_layer_count": closeout.get("summary", {}).get("stack_layer_count"),
            "result_review_count": closeout.get("summary", {}).get("result_review_count"),
            "row_count": closeout.get("row_count"),
            "lineage_preserved": closeout.get("lineage_preserved"),
            "all_result_reviews_accepted": closeout.get("all_result_reviews_accepted"),
            "promotion_allowed_count": int(closeout.get("promotion_allowed_count", -1)),
            "validation_upgrade_count": int(closeout.get("validation_upgrade_count", -1)),
            "execution_claim_count": int(closeout.get("execution_claim_count", -1)),
            "completion_claim_count": int(closeout.get("completion_claim_count", -1)),
            "scoring_policy": closeout.get("scoring_policy"),
            "terminal_readout": closeout.get("summary", {}).get("terminal_readout"),
            "final_non_execution_readout": closeout.get("final_non_execution_readout", {}),
        },
        "next_action": next_action,
        "next_action_scope": "MAIN_TARGET_SELECTION_ONLY_NO_COMPUTATIONAL_EXECUTION_AUTHORIZATION",
        "roadmap_terminal_status": "CLOSED_BOUNDED_NONCLAIM",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Closeout result review accepts the computational-physics infrastructure stack as nonclaim credibility "
            "infrastructure only. It returns to main physics target selection and does not authorize theory validation, "
            "empirical validation, referent comparison execution, robustness scan execution, prediction execution, "
            "falsifier execution, theorem discharge, blocker movement, lane reopen, seam closure, Phase 2 authorization, "
            "master-action promotion, or external-truth claim."
        ),
    }


def write_result_review(
    *,
    closeout_path: Path = DEFAULT_CLOSEOUT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(closeout_path=closeout_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the computational-physics closeout result review.")
    parser.add_argument("--closeout", type=Path, default=DEFAULT_CLOSEOUT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    closeout_path = ns.closeout if ns.closeout.is_absolute() else (REPO_ROOT / ns.closeout)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        closeout_path=closeout_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "computational_physics_integration_closeout_result_review_report: "
        f"accepted={payload['accepted']} next_action={payload['next_action']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
