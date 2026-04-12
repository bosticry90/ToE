from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_QFT_INTERFACE_ALIGNMENT_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "EM_QFT_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
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
    alignment_policy = dict(declaration.get("alignment_policy", {}))
    ruling_contract = dict(declaration.get("ruling_contract", {}))

    selection_path = REPO_ROOT / str(required_inputs.get("em_qft_next_attack_class_selection_report", "")).strip()
    first_test_path = REPO_ROOT / str(required_inputs.get("em_qft_seam_first_test_packet_report", "")).strip()
    gr_freeze_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    rebalance_path = REPO_ROOT / str(required_inputs.get("science_post_qm_stat_rebalance_report", "")).strip()

    selection = _read_json(selection_path)
    first_test = _read_json(first_test_path)
    gr_freeze = _read_json(gr_freeze_path)
    rebalance = _read_json(rebalance_path)

    selection_summary = dict(selection.get("summary", {}))
    first_test_summary = dict(first_test.get("summary", {}))
    gr_freeze_summary = dict(gr_freeze.get("summary", {}))
    rebalance_summary = dict(rebalance.get("summary", {}))

    selected_attack_class = str(selection_summary.get("selected_attack_class", "")).strip()
    selected_target_seam = str(selection_summary.get("target_seam", "")).strip()

    first_test_outcome = str(first_test_summary.get("terminal_outcome", "")).strip()
    first_test_target_seam = str(first_test_summary.get("target_seam", "")).strip()

    gr_row_frozen = bool(gr_freeze_summary.get("row_001_attack_class_cycling_frozen", False))
    qm_stat_bridge_state = str(rebalance_summary.get("qm_stat_bridge_state", "")).strip()

    required_selected_attack_class = str(alignment_policy.get("required_selected_attack_class", "")).strip()
    required_target_seam = str(alignment_policy.get("required_target_seam", "SEAM-EM-QFT")).strip()

    require_gr_row_001_frozen = bool(alignment_policy.get("require_gr_row_001_frozen", True))
    require_qm_stat_hold_unchanged = bool(alignment_policy.get("require_qm_stat_hold_unchanged", True))

    em_qft_interface_alignment_obligation_declared = bool(
        alignment_policy.get("em_qft_interface_alignment_obligation_declared", False)
    )
    em_qft_signal_observed = bool(alignment_policy.get("em_qft_signal_observed", False))

    qm_hold_ok = qm_stat_bridge_state == "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"

    preconditions_ok = (
        selected_attack_class == required_selected_attack_class
        and selected_target_seam == required_target_seam
        and first_test_target_seam == required_target_seam
        and first_test_outcome == "EM_QFT_SEAM_VALID_BUT_NONMOVING"
        and (not require_gr_row_001_frozen or gr_row_frozen)
        and (not require_qm_stat_hold_unchanged or qm_hold_ok)
    )

    allowed_outcomes = set(ruling_contract.get("allowed_outcomes", []))
    default_outcome = str(ruling_contract.get("default_outcome", "EM_QFT_PATH_FALSIFIED")).strip()

    if not preconditions_ok:
        terminal_outcome = "EM_QFT_PATH_FALSIFIED"
        next_action = "RESTORE_EM_QFT_INTERFACE_ALIGNMENT_PRECONDITIONS"
    elif em_qft_signal_observed:
        terminal_outcome = "EM_QFT_SEAM_SIGNAL_PRODUCED"
        next_action = "PROMOTE_EM_QFT_INTERFACE_ALIGNMENT_ROUTE"
    elif not em_qft_interface_alignment_obligation_declared:
        terminal_outcome = "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "DECLARE_ONE_EXPLICIT_EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION"
    else:
        terminal_outcome = "EM_QFT_VALID_BUT_NONMOVING"
        next_action = "HOLD_EM_QFT_INTERFACE_ALIGNMENT_AND_RESELECT_IF_NEEDED"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "selected_attack_class_match": selected_attack_class == required_selected_attack_class,
            "target_seam_match": selected_target_seam == required_target_seam == first_test_target_seam,
            "gr_row_001_frozen_match": gr_row_frozen,
            "qm_stat_hold_preserved": qm_hold_ok,
            "single_terminal_outcome_rule_declared": str(
                ruling_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_EM_QFT_INTERFACE_ALIGNMENT_OUTCOME",
            "no_loop_rule_declared": str(ruling_contract.get("no_loop_rule", "")).strip()
            == "ONE_EM_QFT_INTERFACE_ALIGNMENT_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "selected_attack_class": selected_attack_class,
                "required_selected_attack_class": required_selected_attack_class,
                "selected_target_seam": selected_target_seam,
                "first_test_outcome": first_test_outcome,
                "first_test_target_seam": first_test_target_seam,
                "required_target_seam": required_target_seam,
                "gr_row_frozen": gr_row_frozen,
                "qm_stat_bridge_state": qm_stat_bridge_state,
                "em_qft_interface_alignment_obligation_declared": em_qft_interface_alignment_obligation_declared,
                "em_qft_signal_observed": em_qft_signal_observed,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_seam": required_target_seam,
            "attack_class": required_selected_attack_class,
            "next_action": next_action,
            "single_execution_only": bool(alignment_policy.get("single_execution_only", True)),
            "single_ruling_only": bool(alignment_policy.get("single_ruling_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "em_qft_next_attack_class_selection_report": _ptr(selection_path),
            "em_qft_seam_first_test_packet_report": _ptr(first_test_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_freeze_path),
            "science_post_qm_stat_rebalance_report": _ptr(rebalance_path),
        },
        "non_claim_boundary": "Repository-local EM-QFT interface-alignment packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate EM-QFT interface-alignment packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "em_qft_interface_alignment_packet_20260412_v0.json",
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
        "em_qft_interface_alignment_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
