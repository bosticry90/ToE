from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_QFT_NEXT_ATTACK_CLASS_SELECTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "EM_QFT_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
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

    decision_path = REPO_ROOT / str(required_inputs.get("em_qft_post_first_test_decision_report", "")).strip()
    first_test_path = REPO_ROOT / str(required_inputs.get("em_qft_seam_first_test_packet_report", "")).strip()
    gr_freeze_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    rebalance_path = REPO_ROOT / str(required_inputs.get("science_post_qm_stat_rebalance_report", "")).strip()

    decision = _read_json(decision_path)
    first_test = _read_json(first_test_path)
    gr_freeze = _read_json(gr_freeze_path)
    rebalance = _read_json(rebalance_path)

    decision_summary = dict(decision.get("summary", {}))
    first_test_summary = dict(first_test.get("summary", {}))
    gr_freeze_summary = dict(gr_freeze.get("summary", {}))
    rebalance_summary = dict(rebalance.get("summary", {}))

    decision_outcome = str(decision_summary.get("terminal_outcome", "")).strip()
    first_test_outcome = str(first_test_summary.get("terminal_outcome", "")).strip()
    target_seam = str(first_test_summary.get("target_seam", "")).strip()

    gr_row_frozen = bool(gr_freeze_summary.get("row_001_attack_class_cycling_frozen", False))
    qm_stat_bridge_state = str(rebalance_summary.get("qm_stat_bridge_state", "")).strip()

    required_decision_outcome = str(selection_policy.get("required_decision_outcome", "")).strip()
    required_first_test_outcome = str(selection_policy.get("required_first_test_outcome", "")).strip()
    required_target_seam = str(selection_policy.get("required_target_seam", "SEAM-EM-QFT")).strip()

    require_gr_row_001_frozen = bool(selection_policy.get("require_gr_row_001_frozen", True))
    require_qm_stat_hold_unchanged = bool(selection_policy.get("require_qm_stat_hold_unchanged", True))

    signal_refinement_priority = bool(selection_policy.get("signal_refinement_priority", False))
    subseam_reselection_priority = bool(selection_policy.get("subseam_reselection_priority", False))
    interface_alignment_priority = bool(selection_policy.get("interface_alignment_priority", False))
    require_rescoring = bool(selection_policy.get("require_rescoring", False))

    qm_hold_ok = qm_stat_bridge_state == "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"

    preconditions_ok = (
        decision_outcome == required_decision_outcome
        and first_test_outcome == required_first_test_outcome
        and target_seam == required_target_seam
        and (not require_gr_row_001_frozen or gr_row_frozen)
        and (not require_qm_stat_hold_unchanged or qm_hold_ok)
    )

    allowed_outcomes = set(selection_contract.get("allowed_outcomes", []))
    default_outcome = str(
        selection_contract.get("default_outcome", "HOLD_EM_QFT_AND_REQUIRE_RESCORING")
    ).strip()

    if not preconditions_ok or require_rescoring:
        selected_outcome = "HOLD_EM_QFT_AND_REQUIRE_RESCORING"
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_RESCORING_LAYER"
    elif interface_alignment_priority:
        selected_outcome = "EM_QFT_INTERFACE_ALIGNMENT_ATTACK"
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_INTERFACE_ALIGNMENT_PACKET"
    elif signal_refinement_priority:
        selected_outcome = "EM_QFT_SIGNAL_REFINEMENT_ATTACK"
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_SIGNAL_REFINEMENT_PACKET"
    elif subseam_reselection_priority:
        selected_outcome = "EM_QFT_SUBSEAM_TARGET_RESELECTION_ATTACK"
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_SUBSEAM_RESELECTION_PACKET"
    else:
        selected_outcome = default_outcome
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_RESCORING_LAYER"

    if selected_outcome not in allowed_outcomes:
        selected_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "decision_outcome_match": decision_outcome == required_decision_outcome,
            "first_test_outcome_match": first_test_outcome == required_first_test_outcome,
            "target_seam_match": target_seam == required_target_seam,
            "gr_row_001_frozen_match": gr_row_frozen,
            "qm_stat_hold_preserved": qm_hold_ok,
            "single_terminal_outcome_rule_declared": str(
                selection_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_EM_QFT_NEXT_ATTACK_CLASS_OUTCOME",
            "no_loop_rule_declared": str(selection_contract.get("no_loop_rule", "")).strip()
            == "ONE_EM_QFT_NEXT_ATTACK_CLASS_SELECTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": selected_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "decision_outcome": decision_outcome,
                "required_decision_outcome": required_decision_outcome,
                "first_test_outcome": first_test_outcome,
                "required_first_test_outcome": required_first_test_outcome,
                "target_seam": target_seam,
                "required_target_seam": required_target_seam,
                "gr_row_frozen": gr_row_frozen,
                "qm_stat_bridge_state": qm_stat_bridge_state,
                "signal_refinement_priority": signal_refinement_priority,
                "subseam_reselection_priority": subseam_reselection_priority,
                "interface_alignment_priority": interface_alignment_priority,
                "require_rescoring": require_rescoring,
            },
            "summary": {
                "all_criteria_satisfied": selected_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "selected_attack_class": selected_outcome,
            "target_seam": target_seam,
            "next_action": next_action,
            "single_selection_only": bool(selection_policy.get("single_selection_only", True)),
            "single_outcome_only": bool(selection_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "em_qft_post_first_test_decision_report": _ptr(decision_path),
            "em_qft_seam_first_test_packet_report": _ptr(first_test_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_freeze_path),
            "science_post_qm_stat_rebalance_report": _ptr(rebalance_path),
        },
        "non_claim_boundary": "Repository-local EM-QFT next attack-class selection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate EM-QFT next attack-class selection report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "em_qft_next_attack_class_selection_20260412_v0.json",
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
        "em_qft_next_attack_class_selection_report: "
        f"selected_attack_class={payload['summary']['selected_attack_class']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
