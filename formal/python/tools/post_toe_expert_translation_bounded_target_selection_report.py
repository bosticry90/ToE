from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_post_mr_assump004_governed_maturation_reports import (
    CAPTURED_AT_UTC,
    EXPERT_TRANSLATION_PATH,
    FINAL_LIVE_TARGET,
    MATURATION_INDEX_PATH,
    MINIMAL_MODEL_PATH,
    NONCLAIMS,
    WITNESS_ATTEMPT_REVIEW_PATH,
)


REPO_ROOT = find_repo_root(Path(__file__))

CONSUMED_TARGET = FINAL_LIVE_TARGET
SELECTED_NEXT_TARGET = "prepare_qft_gr_minimal_working_model_demonstration_packet"
SCHEMA_ID = "POST_TOE_EXPERT_TRANSLATION_BOUNDED_TARGET_SELECTION_20260610_v0"
SELECTION_ID = "POST_TOE_EXPERT_TRANSLATION_BOUNDED_TARGET_SELECTION_v0"
OUTCOME_ID = (
    "POST_TOE_EXPERT_TRANSLATION_BOUNDED_TARGET_SELECTION_SELECTS_QFT_GR_"
    "MINIMAL_MODEL_DEMONSTRATION_PACKET_NO_PROMOTION"
)
OUTCOME_CATEGORY = "post_translation_next_target_selected"
ALLOWED_OUTCOME_CATEGORIES = [
    "post_translation_next_target_selected",
    "post_translation_followup_obstruction_identified",
    "post_translation_bounded_handoff_requires_review",
]
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_TOE_EXPERT_TRANSLATION_BOUNDED_TARGET_SELECTION_20260610_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required text file: {path}")
    return path.read_text(encoding="utf-8")


def _selected_targets(rows: list[dict[str, Any]]) -> list[str]:
    return [str(row["target"]) for row in rows if row.get("decision") == "selected"]


def build_selection(
    *,
    maturation_index_path: Path = MATURATION_INDEX_PATH,
    expert_translation_path: Path = EXPERT_TRANSLATION_PATH,
    minimal_model_path: Path = MINIMAL_MODEL_PATH,
    witness_review_path: Path = WITNESS_ATTEMPT_REVIEW_PATH,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    index = _read_json(maturation_index_path)
    witness_review = _read_json(witness_review_path)
    expert_translation = _read_text(expert_translation_path)
    minimal_model = _read_text(minimal_model_path)

    candidate_next_targets = [
        {
            "target": SELECTED_NEXT_TARGET,
            "decision": "selected",
            "outcome_category": OUTCOME_CATEGORY,
            "reason": (
                "The reviewed witness reattempt is inconclusive because a minimal "
                "model demonstration is missing."
            ),
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
            "decision": "not_authorized",
            "outcome_category": "post_translation_followup_obstruction_identified",
            "reason": (
                "The witness reattempt did not name Bianchi compatibility as the "
                "exact missing condition family."
            ),
        },
        {
            "target": "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized",
            "outcome_category": "post_translation_followup_obstruction_identified",
            "reason": (
                "The witness reattempt did not authorize a source-admissibility "
                "assumption family."
            ),
        },
        {
            "target": "authorize_public_theory_readiness_or_release_submission",
            "decision": "not_authorized",
            "outcome_category": "post_translation_bounded_handoff_requires_review",
            "reason": (
                "Expert translation is a legibility layer only and does not create "
                "public-theory or release readiness."
            ),
        },
    ]
    selected_targets = _selected_targets(candidate_next_targets)
    artifact_order = index.get("artifact_order", [])
    acceptance_criteria = {
        "consumes_post_witness_maturation_index": index.get("index_id")
        == "TOE_POST_WITNESS_MATURATION_INDEX_v0",
        "maturation_index_selected_this_live_target": index.get("selected_next_target")
        == CONSUMED_TARGET,
        "expert_translation_is_terminal_maturation_artifact": artifact_order[-1:]
        == [_ptr(expert_translation_path)],
        "witness_review_accepted_model_demonstration_route": witness_review.get(
            "accepted_attempt_classification"
        )
        == "bounded_witness_inconclusive_requires_model_demonstration",
        "witness_review_did_not_open_assumption_family": witness_review.get(
            "next_assumption_family_authorized"
        )
        is False,
        "minimal_model_program_defines_first_model": "## First Model" in minimal_model
        and "free scalar-field" in minimal_model,
        "expert_translation_remains_legibility_only": "terminology mapping only"
        in expert_translation,
        "allowed_outcome_category_used": OUTCOME_CATEGORY in ALLOWED_OUTCOME_CATEGORIES,
        "selects_exactly_one_next_target": selected_targets == [SELECTED_NEXT_TARGET],
        "preserves_nonclaims": all(value is False for value in NONCLAIMS.values()),
    }
    return {
        "schema_id": SCHEMA_ID,
        "selection_id": SELECTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_target": CONSUMED_TARGET,
        "consumes_post_witness_maturation_index": index.get("index_id"),
        "consumes_post_witness_maturation_index_pointer": _ptr(maturation_index_path),
        "consumes_witness_result_review": witness_review.get("review_id"),
        "consumes_witness_result_review_pointer": _ptr(witness_review_path),
        "expert_translation_pointer": _ptr(expert_translation_path),
        "minimal_model_program_pointer": _ptr(minimal_model_path),
        "outcome_id": OUTCOME_ID,
        "outcome_category": OUTCOME_CATEGORY,
        "allowed_outcome_categories": ALLOWED_OUTCOME_CATEGORIES,
        "selection_classification": (
            "post_translation_next_target_selected_minimal_model_demonstration_packet"
        ),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "qft_gr_minimal_model_demonstration_packet_preparation",
        "selected_next_target_role": (
            "bounded Level 3 toy-model demonstration packet preparation"
        ),
        "candidate_next_targets": candidate_next_targets,
        "selection_count": len(selected_targets),
        "next_assumption_family_authorized": False,
        "public_theory_readiness_claimed": False,
        "release_or_public_submission_authorized": False,
        "bounded_handoff_requires_review": True,
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": NONCLAIMS,
    }


def write_report(path: Path = DEFAULT_OUT) -> dict[str, Any]:
    payload = build_selection()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Select the next bounded target after the ToE expert translation layer."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    payload = write_report(args.out)
    print(
        "post_toe_expert_translation_bounded_target_selection_report: "
        f"selected={payload['selected_next_target']} out={_ptr(args.out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
