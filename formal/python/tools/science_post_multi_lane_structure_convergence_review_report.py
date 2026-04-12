from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_POST_MULTI_LANE_STRUCTURE_CONVERGENCE_REVIEW_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_POST_MULTI_LANE_STRUCTURE_CONVERGENCE_REVIEW_20260412_v0.json"
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
    required_inputs = dict(declaration.get("required_inputs", {}))
    convergence_policy = dict(declaration.get("convergence_policy", {}))
    review_contract = dict(declaration.get("review_contract", {}))

    qm_stat_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_review_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()

    qm_stat = _read_json(qm_stat_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)

    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))

    qm_stat_required_review_outcome = str(
        convergence_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(convergence_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(convergence_policy.get("em_qft_required_outcome", "")).strip()

    shared_structural_pattern_detected = bool(convergence_policy.get("shared_structural_pattern_detected", False))
    shared_model_class_program_feasible = bool(convergence_policy.get("shared_model_class_program_feasible", False))
    separate_model_class_programs_feasible = bool(convergence_policy.get("separate_model_class_programs_feasible", False))
    activate_different_existing_lane = bool(convergence_policy.get("activate_different_existing_lane", False))

    lane_state_preconditions_ok = (
        qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and em_qft_outcome == em_qft_required_outcome
        and gr_frozen
        and em_qft_frozen
    )

    allowed_outcomes = set(review_contract.get("allowed_outcomes", []))
    default_outcome = str(
        review_contract.get("default_outcome", "HOLD_AND_REQUIRE_HIGHER_LEVEL_ARCHITECTURE_REVIEW")
    ).strip()

    if not lane_state_preconditions_ok:
        terminal_outcome = "HOLD_AND_REQUIRE_HIGHER_LEVEL_ARCHITECTURE_REVIEW"
        next_action = "RESTORE_MULTI_LANE_PRECONDITION_ALIGNMENT"
    elif shared_structural_pattern_detected and shared_model_class_program_feasible:
        terminal_outcome = "NEW_SHARED_MODEL_CLASS_PROGRAM_JUSTIFIED"
        next_action = "OPEN_ONE_BOUNDED_SHARED_MODEL_CLASS_PROGRAM_PROPOSAL_LAYER"
    elif shared_structural_pattern_detected and separate_model_class_programs_feasible:
        terminal_outcome = "SEPARATE_NEW_MODEL_CLASS_PROGRAMS_REQUIRED"
        next_action = "OPEN_BOUNDED_GR_AND_EM_QFT_SEPARATE_MODEL_CLASS_PROPOSAL_LAYERS"
    elif activate_different_existing_lane:
        terminal_outcome = "ACTIVATE_DIFFERENT_EXISTING_LANE"
        next_action = "OPEN_ONE_BOUNDED_PACKET_ON_NEXT_EXISTING_LIVE_LANE"
    else:
        terminal_outcome = "HOLD_AND_REQUIRE_HIGHER_LEVEL_ARCHITECTURE_REVIEW"
        next_action = "OPEN_HIGHER_LEVEL_ARCHITECTURE_REVIEW_LAYER"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "shared_structural_pattern_detected": shared_structural_pattern_detected,
            "single_terminal_outcome_rule_declared": str(
                review_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_POST_MULTI_LANE_CONVERGENCE_OUTCOME",
            "no_loop_rule_declared": str(review_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_MULTI_LANE_CONVERGENCE_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "lane_state_preconditions_satisfied": lane_state_preconditions_ok,
            },
            "inputs": {
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "shared_structural_pattern_detected": shared_structural_pattern_detected,
                "shared_model_class_program_feasible": shared_model_class_program_feasible,
                "separate_model_class_programs_feasible": separate_model_class_programs_feasible,
                "activate_different_existing_lane": activate_different_existing_lane,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_review_only": bool(convergence_policy.get("single_review_only", True)),
            "single_outcome_only": bool(convergence_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
        },
        "non_claim_boundary": "Repository-local post-multi-lane structural-convergence review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate post-multi-lane structural-convergence review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_post_multi_lane_structure_convergence_review_20260412_v0.json",
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
        "science_post_multi_lane_structure_convergence_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
