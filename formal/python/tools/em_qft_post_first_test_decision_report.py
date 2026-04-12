from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_QFT_POST_FIRST_TEST_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "EM_QFT_POST_FIRST_TEST_DECISION_20260412_v0.json"
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
    decision_policy = dict(declaration.get("decision_policy", {}))
    decision_contract = dict(declaration.get("decision_contract", {}))

    first_test_path = REPO_ROOT / str(required_inputs.get("em_qft_seam_first_test_packet_report", "")).strip()
    gr_freeze_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    rebalance_path = REPO_ROOT / str(required_inputs.get("science_post_qm_stat_rebalance_report", "")).strip()

    first_test = _read_json(first_test_path)
    gr_freeze = _read_json(gr_freeze_path)
    rebalance = _read_json(rebalance_path)

    first_test_summary = dict(first_test.get("summary", {}))
    first_test_inputs = dict(dict(first_test.get("objective_quality", {})).get("inputs", {}))
    first_test_outcome = str(first_test_summary.get("terminal_outcome", "")).strip()
    target_seam = str(first_test_summary.get("target_seam", "")).strip()
    structure_sufficient = bool(first_test_inputs.get("em_qft_declared_structure_sufficient", False))

    gr_freeze_summary = dict(gr_freeze.get("summary", {}))
    gr_row_frozen = bool(gr_freeze_summary.get("row_001_attack_class_cycling_frozen", False))

    rebalance_summary = dict(rebalance.get("summary", {}))
    qm_stat_bridge_state = str(rebalance_summary.get("qm_stat_bridge_state", "")).strip()

    required_first_test_outcome = str(decision_policy.get("required_first_test_outcome", "")).strip()
    required_target_seam = str(decision_policy.get("required_target_seam", "SEAM-EM-QFT")).strip()
    require_gr_row_001_frozen = bool(decision_policy.get("require_gr_row_001_frozen", True))
    require_qm_stat_untouched_hold = bool(decision_policy.get("require_qm_stat_untouched_hold", True))

    packet_shape_refinement_viable = bool(decision_policy.get("packet_shape_refinement_viable", False))
    different_subseam_indicated = bool(decision_policy.get("different_subseam_indicated", False))
    require_rescoring = bool(decision_policy.get("require_rescoring", False))

    qm_stat_hold_ok = qm_stat_bridge_state == "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"

    preconditions_ok = (
        first_test_outcome == required_first_test_outcome
        and target_seam == required_target_seam
        and (not require_gr_row_001_frozen or gr_row_frozen)
        and (not require_qm_stat_untouched_hold or qm_stat_hold_ok)
        and structure_sufficient
    )

    allowed_outcomes = set(decision_contract.get("allowed_outcomes", []))
    default_outcome = str(
        decision_contract.get("default_outcome", "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "HOLD_EM_QFT_AND_REQUIRE_RESCORING"
        next_action = "RESTORE_EM_QFT_POST_FIRST_TEST_PRECONDITIONS"
    elif require_rescoring:
        terminal_outcome = "HOLD_EM_QFT_AND_REQUIRE_RESCORING"
        next_action = "RUN_ONE_BOUNDED_EM_QFT_RESCORING_LAYER"
    elif different_subseam_indicated:
        terminal_outcome = "ACTIVATE_EM_QFT_DIFFERENT_TARGET_SUBSEAM"
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_DIFFERENT_SUBSEAM_PACKET"
    elif packet_shape_refinement_viable:
        terminal_outcome = "ACTIVATE_EM_QFT_SIGNAL_REFINEMENT_PACKET"
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_SIGNAL_REFINEMENT_PACKET"
    else:
        terminal_outcome = "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS"
        next_action = "OPEN_ONE_BOUNDED_EM_QFT_ATTACK_CLASS_RESELECTION_LAYER"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "first_test_outcome_match": first_test_outcome == required_first_test_outcome,
            "target_seam_match": target_seam == required_target_seam,
            "gr_row_001_frozen_match": gr_row_frozen,
            "qm_stat_hold_preserved": qm_stat_hold_ok,
            "single_terminal_outcome_rule_declared": str(
                decision_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_EM_QFT_POST_FIRST_TEST_DECISION_OUTCOME",
            "no_loop_rule_declared": str(decision_contract.get("no_loop_rule", "")).strip()
            == "ONE_EM_QFT_POST_FIRST_TEST_DECISION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "first_test_outcome": first_test_outcome,
                "required_first_test_outcome": required_first_test_outcome,
                "target_seam": target_seam,
                "required_target_seam": required_target_seam,
                "structure_sufficient": structure_sufficient,
                "gr_row_frozen": gr_row_frozen,
                "qm_stat_bridge_state": qm_stat_bridge_state,
                "packet_shape_refinement_viable": packet_shape_refinement_viable,
                "different_subseam_indicated": different_subseam_indicated,
                "require_rescoring": require_rescoring,
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
            "next_action": next_action,
            "single_decision_only": bool(decision_policy.get("single_decision_only", True)),
            "single_outcome_only": bool(decision_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "em_qft_seam_first_test_packet_report": _ptr(first_test_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_freeze_path),
            "science_post_qm_stat_rebalance_report": _ptr(rebalance_path),
        },
        "non_claim_boundary": "Repository-local EM-QFT post-first-test decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate EM-QFT post-first-test decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "em_qft_post_first_test_decision_20260412_v0.json",
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
        "em_qft_post_first_test_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
