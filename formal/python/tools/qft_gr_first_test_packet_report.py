from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_FIRST_TEST_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_FIRST_TEST_PACKET_20260412_v0.json"
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
    test_policy = dict(declaration.get("test_policy", {}))
    test_contract = dict(declaration.get("test_contract", {}))

    lane_selection_path = REPO_ROOT / str(
        required_inputs.get("science_new_untouched_lane_selection_report", "")
    ).strip()
    preservation_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_preservation_record_report", "")
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

    lane_selection = _read_json(lane_selection_path)
    preservation = _read_json(preservation_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    lane_selection_outcome = str(
        dict(lane_selection.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    selected_lane = str(
        dict(lane_selection.get("summary", {})).get("selected_lane", "")
    ).strip()
    preservation_outcome = str(
        dict(preservation.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_lane_selection_outcome = str(
        test_policy.get("required_lane_selection_outcome", "")
    ).strip()
    required_selected_lane = str(test_policy.get("required_selected_lane", "")).strip()
    required_preservation_outcome = str(test_policy.get("required_preservation_outcome", "")).strip()
    qm_stat_required_review_outcome = str(
        test_policy.get("qm_stat_required_review_outcome", "")
    ).strip()
    gr_required_outcome = str(test_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(test_policy.get("em_qft_required_outcome", "")).strip()
    target_seam = str(test_policy.get("target_seam", "")).strip()
    single_attack_class = str(test_policy.get("single_attack_class", "")).strip()
    lane_borrows_no_authority = bool(
        test_policy.get("lane_borrows_no_authority_from_frozen_lanes", True)
    )
    movement_signal_detected = bool(test_policy.get("movement_signal_detected", False))

    preconditions_ok = (
        lane_selection_outcome == required_lane_selection_outcome
        and selected_lane == required_selected_lane
        and preservation_outcome == required_preservation_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and gr_frozen
        and em_qft_outcome == em_qft_required_outcome
        and em_qft_frozen
        and lane_borrows_no_authority
    )

    allowed_outcomes = set(test_contract.get("allowed_outcomes", []))
    default_outcome = str(
        test_contract.get("default_outcome", "QFT_GR_SEAM_SIGNAL_PRODUCED")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "QFT_GR_SEAM_PATH_FALSIFIED"
        next_action = "CLOSE_QFT_GR_LANE_AND_REASSESS_LANE_SELECTION"
    elif not movement_signal_detected:
        terminal_outcome = "QFT_GR_SEAM_VALID_BUT_NONMOVING"
        next_action = "HOLD_QFT_GR_LANE_VALID_BUT_NO_MOVEMENT"
    else:
        terminal_outcome = "QFT_GR_SEAM_SIGNAL_PRODUCED"
        next_action = "OPEN_ONE_BOUNDED_QFT_GR_POST_SIGNAL_INTERPRETATION_LAYER"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "lane_selection_outcome_match": lane_selection_outcome == required_lane_selection_outcome,
            "selected_lane_match": selected_lane == required_selected_lane,
            "preservation_outcome_match": preservation_outcome == required_preservation_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "lane_borrows_no_authority_from_frozen_lanes": lane_borrows_no_authority,
            "single_terminal_outcome_rule_declared": str(
                test_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_QFT_GR_FIRST_TEST_PACKET_OUTCOME",
            "no_loop_rule_declared": str(test_contract.get("no_loop_rule", "")).strip()
            == "ONE_QFT_GR_FIRST_TEST_PACKET_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "test_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "lane_selection_outcome": lane_selection_outcome,
                "required_lane_selection_outcome": required_lane_selection_outcome,
                "selected_lane": selected_lane,
                "required_selected_lane": required_selected_lane,
                "preservation_outcome": preservation_outcome,
                "required_preservation_outcome": required_preservation_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "target_seam": target_seam,
                "single_attack_class": single_attack_class,
                "lane_borrows_no_authority_from_frozen_lanes": lane_borrows_no_authority,
                "movement_signal_detected": movement_signal_detected,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_seam": target_seam,
            "single_attack_class": single_attack_class,
            "next_action": next_action,
            "single_layer_only": bool(test_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(test_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_new_untouched_lane_selection_report": _ptr(lane_selection_path),
            "science_frontier_preservation_record_report": _ptr(preservation_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local QFT-GR first-test packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QFT-GR first-test packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qft_gr_first_test_packet_20260412_v0.json",
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
        "qft_gr_first_test_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" target_seam={payload['summary']['target_seam']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
