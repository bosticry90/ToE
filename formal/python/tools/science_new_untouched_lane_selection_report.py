from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
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
    selection_policy = dict(declaration.get("selection_policy", {}))
    selection_contract = dict(declaration.get("selection_contract", {}))

    preservation_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_preservation_record_report", "")
    ).strip()
    post_refinement_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_post_refinement_decision_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(
        required_inputs.get("gr_row_001_structural_gap_definition_report", "")
    ).strip()
    em_qft_path = REPO_ROOT / str(
        required_inputs.get("em_qft_higher_level_structure_review_report", "")
    ).strip()
    qm_stat_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_review_report", "")
    ).strip()

    preservation = _read_json(preservation_path)
    post_refinement = _read_json(post_refinement_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    preservation_outcome = str(
        dict(preservation.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    post_refinement_outcome = str(
        dict(post_refinement.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_preservation_outcome = str(
        selection_policy.get("required_preservation_outcome", "")
    ).strip()
    required_post_refinement_outcome = str(
        selection_policy.get("required_post_refinement_outcome", "")
    ).strip()
    qm_stat_required_review_outcome = str(
        selection_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(selection_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(selection_policy.get("em_qft_required_outcome", "")).strip()
    excluded_lanes = list(selection_policy.get("excluded_lanes", []))
    qft_gr_untouched = bool(selection_policy.get("qft_gr_untouched", False))
    cosmo_sr_untouched = bool(selection_policy.get("cosmo_sr_untouched", False))
    no_genuinely_untouched_lane = bool(selection_policy.get("no_genuinely_untouched_lane", False))

    preconditions_ok = (
        preservation_outcome == required_preservation_outcome
        and post_refinement_outcome == required_post_refinement_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and gr_frozen
        and em_qft_outcome == em_qft_required_outcome
        and em_qft_frozen
    )

    allowed_outcomes = set(selection_contract.get("allowed_outcomes", []))
    default_outcome = str(
        selection_contract.get(
            "default_outcome",
            "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
        )
    ).strip()

    if not preconditions_ok or no_genuinely_untouched_lane:
        terminal_outcome = "NO_GENUINELY_UNTOUCHED_LANE_AVAILABLE"
        selected_lane = None
        next_action = "HOLD_UNTIL_NEW_STANDARD_OR_NEW_EVIDENCE_PERMITS_LANE_OPENING"
    elif qft_gr_untouched:
        terminal_outcome = "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST"
        selected_lane = "QFT-GR"
        next_action = "OPEN_ONE_BOUNDED_QFT_GR_FIRST_TEST_PACKET"
    elif cosmo_sr_untouched:
        terminal_outcome = "ACTIVATE_COSMO_SR_UNTOUCHED_FIRST_TEST"
        selected_lane = "COSMO-SR"
        next_action = "OPEN_ONE_BOUNDED_COSMO_SR_FIRST_TEST_PACKET"
    else:
        terminal_outcome = "ACTIVATE_OTHER_UNTOUCHED_LANE"
        selected_lane = "OTHER"
        next_action = "OPEN_ONE_BOUNDED_FIRST_TEST_PACKET_FOR_OTHER_UNTOUCHED_LANE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "preservation_outcome_match": preservation_outcome == required_preservation_outcome,
            "post_refinement_outcome_match": post_refinement_outcome == required_post_refinement_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "excluded_lanes_confirmed": excluded_lanes,
            "single_terminal_outcome_rule_declared": str(
                selection_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_OUTCOME",
            "no_loop_rule_declared": str(selection_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "selection_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "preservation_outcome": preservation_outcome,
                "required_preservation_outcome": required_preservation_outcome,
                "post_refinement_outcome": post_refinement_outcome,
                "required_post_refinement_outcome": required_post_refinement_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "excluded_lanes": excluded_lanes,
                "qft_gr_untouched": qft_gr_untouched,
                "cosmo_sr_untouched": cosmo_sr_untouched,
                "no_genuinely_untouched_lane": no_genuinely_untouched_lane,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "selected_lane": selected_lane,
            "next_action": next_action,
            "single_layer_only": bool(selection_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(selection_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_frontier_preservation_record_report": _ptr(preservation_path),
            "shared_model_class_post_refinement_decision_report": _ptr(post_refinement_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local science new-untouched-lane selection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate science new-untouched-lane selection report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_new_untouched_lane_selection_20260412_v0.json",
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
        "science_new_untouched_lane_selection_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" selected_lane={payload['summary']['selected_lane']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
