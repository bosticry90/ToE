from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_20260412_v0.json"
)

_CANONICAL_LEGACY_LANES = {
    "QM-STAT",
    "GR-ROW-001",
    "EM-QFT",
    "SHARED-MODEL-CLASS",
    "QFT-GR",
}


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
    synthesis_policy = dict(declaration.get("synthesis_policy", {}))
    synthesis_contract = dict(declaration.get("synthesis_contract", {}))

    phase_j_path = REPO_ROOT / str(
        required_inputs.get("science_phase_j_untouched_lane_post_refinement_decision_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()
    phase_d_path = REPO_ROOT / str(
        required_inputs.get("science_phase_d_untouched_lane_selection_report", "")
    ).strip()
    qm_stat_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_review_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_structural_gap_definition_report", "")
    ).strip()
    em_qft_path = REPO_ROOT / str(
        required_inputs.get("em_qft_higher_level_structure_review_report", "")
    ).strip()
    shared_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_post_refinement_decision_report", "")
    ).strip()
    qft_gr_path = REPO_ROOT / str(
        required_inputs.get("qft_gr_post_refinement_decision_report", "")
    ).strip()

    phase_j = _read_json(phase_j_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)
    phase_d = _read_json(phase_d_path)
    qm_stat = _read_json(qm_stat_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    shared = _read_json(shared_path)
    qft_gr = _read_json(qft_gr_path)

    phase_j_outcome = str(dict(phase_j.get("summary", {})).get("terminal_outcome", "")).strip()
    phase_j_target_lane = str(dict(phase_j.get("summary", {})).get("target_lane", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    phase_d_selection_outcome = str(dict(phase_d.get("summary", {})).get("terminal_outcome", "")).strip()

    legacy_lane_outcomes = {
        "QM-STAT": str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip(),
        "GR-ROW-001": str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip(),
        "EM-QFT": str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip(),
        "SHARED-MODEL-CLASS": str(dict(shared.get("summary", {})).get("terminal_outcome", "")).strip(),
        "QFT-GR": str(dict(qft_gr.get("summary", {})).get("terminal_outcome", "")).strip(),
    }

    required_phase_j_outcome = str(synthesis_policy.get("required_phase_j_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        synthesis_policy.get("required_non_reopen_summary_outcome", "")
    ).strip()
    required_phase_d_selection_outcome = str(
        synthesis_policy.get("required_phase_d_selection_outcome", "")
    ).strip()
    required_legacy_lane_outcomes = dict(synthesis_policy.get("required_legacy_lane_outcomes", {}))
    required_legacy_coverage_ok = set(required_legacy_lane_outcomes.keys()) == _CANONICAL_LEGACY_LANES

    required_held_untouched_lane = str(synthesis_policy.get("required_held_untouched_lane", "")).strip()
    non_reopen_rule_enforced = bool(synthesis_policy.get("non_reopen_rule_enforced", False))
    recommend_resume_mode = str(synthesis_policy.get("recommend_resume_mode", "")).strip()
    criteria_axes = list(synthesis_policy.get("criteria_axes", []))

    legacy_lane_matches = {
        lane: legacy_lane_outcomes.get(lane, "") == str(required_legacy_lane_outcomes.get(lane, "")).strip()
        for lane in required_legacy_lane_outcomes
    }

    preconditions_ok = (
        phase_j_outcome == required_phase_j_outcome
        and phase_j_target_lane == required_held_untouched_lane
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and phase_d_selection_outcome == required_phase_d_selection_outcome
        and required_legacy_coverage_ok
        and all(legacy_lane_matches.values())
        and non_reopen_rule_enforced
        and bool(recommend_resume_mode)
        and len(criteria_axes) >= 3
    )

    allowed_outcomes = set(synthesis_contract.get("allowed_outcomes", []))
    default_outcome = str(
        synthesis_contract.get("default_outcome", "NEW_LANE_DESIGN_CRITERIA_EVIDENCE_INCOMPLETE")
    ).strip()

    if not required_legacy_coverage_ok:
        terminal_outcome = "HOLD_PENDING_SYNTHESIS_REPAIR"
        next_action = "REPAIR_CANONICAL_LEGACY_LANE_COVERAGE"
    elif not preconditions_ok:
        terminal_outcome = "NEW_LANE_DESIGN_CRITERIA_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_K_PRECONDITIONS_AND_RERUN"
    else:
        terminal_outcome = "NEW_LANE_DESIGN_CRITERIA_SYNTHESIZED_AND_LOCKED"
        next_action = "USE_SYNTHESIS_TO_SELECT_NEXT_RESUME_CATEGORY_WITHOUT_REOPEN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    design_criteria = {
        "discriminative_observable_strength": "Require explicit predeclared discriminator expected to move beyond valid-but-nonmoving in one bounded packet.",
        "external_comparator_path_clarity": "Require an explicit path from lane outputs to externally comparable form before packet authorization.",
        "declared_structure_sufficiency": "Require minimum structure declaration threshold that avoids deferred undeclared-structure routing.",
        "attack_family_mobility": "Require evidence that at least one attack-family transition plausibly changes outcome class, not only packet form.",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_j_outcome_match": phase_j_outcome == required_phase_j_outcome,
            "phase_j_target_lane_match": phase_j_target_lane == required_held_untouched_lane,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "phase_d_selection_outcome_match": phase_d_selection_outcome == required_phase_d_selection_outcome,
            "legacy_lane_coverage_ok": required_legacy_coverage_ok,
            "all_legacy_lane_outcomes_match": all(legacy_lane_matches.values()),
            "non_reopen_rule_enforced": non_reopen_rule_enforced,
            "single_terminal_outcome_rule_declared": str(
                synthesis_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_OUTCOME",
            "no_loop_rule_declared": str(synthesis_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "synthesis_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_j_outcome": phase_j_outcome,
                "required_phase_j_outcome": required_phase_j_outcome,
                "phase_j_target_lane": phase_j_target_lane,
                "required_held_untouched_lane": required_held_untouched_lane,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "phase_d_selection_outcome": phase_d_selection_outcome,
                "required_phase_d_selection_outcome": required_phase_d_selection_outcome,
                "legacy_lane_outcomes": legacy_lane_outcomes,
                "required_legacy_lane_outcomes": required_legacy_lane_outcomes,
                "legacy_lane_matches": legacy_lane_matches,
                "legacy_lane_coverage_ok": required_legacy_coverage_ok,
                "recommend_resume_mode": recommend_resume_mode,
                "criteria_axes": criteria_axes,
                "non_reopen_rule_enforced": non_reopen_rule_enforced,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "new_lane_design_criteria": design_criteria,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "recommend_resume_mode": recommend_resume_mode,
            "next_action": next_action,
            "single_layer_only": bool(synthesis_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(synthesis_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_j_untouched_lane_post_refinement_decision_report": _ptr(phase_j_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
            "science_phase_d_untouched_lane_selection_report": _ptr(phase_d_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "shared_model_class_post_refinement_decision_report": _ptr(shared_path),
            "qft_gr_post_refinement_decision_report": _ptr(qft_gr_path),
        },
        "non_claim_boundary": "Repository-local new-lane design criteria synthesis report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase K new-lane design criteria synthesis report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_k_new_lane_design_criteria_synthesis_20260412_v0.json",
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
        "science_phase_k_new_lane_design_criteria_synthesis_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" recommend_resume_mode={payload['summary']['recommend_resume_mode']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
