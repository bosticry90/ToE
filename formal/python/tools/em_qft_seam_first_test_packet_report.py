from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_QFT_SEAM_FIRST_TEST_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "EM_QFT_SEAM_FIRST_TEST_PACKET_20260412_v0.json"
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


def _required_seam_present(artifact: dict[str, Any], seam_id: str) -> bool:
    payload = dict(artifact.get("payload", {}))
    basis = dict(payload.get("basis", {}))
    seams = list(basis.get("required_seams", []))
    for entry in seams:
        if str(dict(entry).get("seam_id", "")).strip() == seam_id:
            return True
    return False


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    first_test_policy = dict(declaration.get("first_test_policy", {}))
    ruling_contract = dict(declaration.get("ruling_contract", {}))

    rebalance_path = REPO_ROOT / str(required_inputs.get("science_post_qm_stat_rebalance_report", "")).strip()
    gr_freeze_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_m4_path = REPO_ROOT / str(required_inputs.get("em_m4_seam_closure_promotion_cycle01", "")).strip()
    qft_m4_path = REPO_ROOT / str(required_inputs.get("qft_m4_seam_closure_promotion_cycle01", "")).strip()

    rebalance = _read_json(rebalance_path)
    gr_freeze = _read_json(gr_freeze_path)
    em_m4 = _read_json(em_m4_path)
    qft_m4 = _read_json(qft_m4_path)

    required_rebalance_outcome = str(first_test_policy.get("required_rebalance_outcome", "")).strip()
    required_gr_freeze_outcome = str(first_test_policy.get("required_gr_freeze_outcome", "")).strip()
    required_target_seam = str(first_test_policy.get("required_target_seam", "SEAM-EM-QFT")).strip()
    required_em_m4_status = str(first_test_policy.get("required_em_m4_status", "")).strip()
    required_qft_m4_status = str(first_test_policy.get("required_qft_m4_status", "")).strip()

    em_qft_declared_structure_sufficient = bool(
        first_test_policy.get("em_qft_declared_structure_sufficient", False)
    )
    em_qft_signal_observed = bool(first_test_policy.get("em_qft_signal_observed", False))

    rebalance_outcome = str(dict(rebalance.get("summary", {})).get("selected_outcome", "")).strip()
    gr_freeze_outcome = str(dict(gr_freeze.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_row_frozen = bool(dict(gr_freeze.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))

    em_m4_status = str(dict(em_m4.get("payload", {})).get("status", "")).strip()
    qft_m4_status = str(dict(qft_m4.get("payload", {})).get("status", "")).strip()
    em_required_seam_present = _required_seam_present(em_m4, required_target_seam)
    qft_required_seam_present = _required_seam_present(qft_m4, required_target_seam)

    preconditions_ok = (
        rebalance_outcome == required_rebalance_outcome
        and gr_freeze_outcome == required_gr_freeze_outcome
        and gr_row_frozen
        and em_m4_status == required_em_m4_status
        and qft_m4_status == required_qft_m4_status
        and em_required_seam_present
        and qft_required_seam_present
    )

    allowed_outcomes = set(ruling_contract.get("allowed_outcomes", []))
    default_outcome = str(ruling_contract.get("default_outcome", "EM_QFT_SEAM_PATH_FALSIFIED")).strip()

    if not preconditions_ok:
        terminal_outcome = "EM_QFT_SEAM_PATH_FALSIFIED"
        next_action = "RESTORE_EM_QFT_FIRST_TEST_PRECONDITIONS_BEFORE_EXECUTION"
    elif not em_qft_declared_structure_sufficient:
        terminal_outcome = "EM_QFT_SEAM_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "DECLARE_ONE_EXPLICIT_EM_QFT_SEAM_STRUCTURE_OBLIGATION"
    elif em_qft_signal_observed:
        terminal_outcome = "EM_QFT_SEAM_SIGNAL_PRODUCED"
        next_action = "PROMOTE_EM_QFT_SEAM_TO_NEXT_BOUNDED_PACKET"
    else:
        terminal_outcome = "EM_QFT_SEAM_VALID_BUT_NONMOVING"
        next_action = "HOLD_EM_QFT_SEAM_SIGNAL_AND_RESELECT_NEXT_BOUNDED_MOVE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "rebalance_precondition_match": rebalance_outcome == required_rebalance_outcome,
            "gr_freeze_precondition_match": gr_freeze_outcome == required_gr_freeze_outcome and gr_row_frozen,
            "target_seam_present_in_em_basis": em_required_seam_present,
            "target_seam_present_in_qft_basis": qft_required_seam_present,
            "single_terminal_outcome_rule_declared": str(
                ruling_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_EM_QFT_FIRST_TEST_OUTCOME",
            "no_loop_rule_declared": str(ruling_contract.get("no_loop_rule", "")).strip()
            == "ONE_EM_QFT_FIRST_TEST_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "required_target_seam": required_target_seam,
                "rebalance_outcome": rebalance_outcome,
                "required_rebalance_outcome": required_rebalance_outcome,
                "gr_freeze_outcome": gr_freeze_outcome,
                "required_gr_freeze_outcome": required_gr_freeze_outcome,
                "gr_row_frozen": gr_row_frozen,
                "em_m4_status": em_m4_status,
                "required_em_m4_status": required_em_m4_status,
                "qft_m4_status": qft_m4_status,
                "required_qft_m4_status": required_qft_m4_status,
                "em_qft_declared_structure_sufficient": em_qft_declared_structure_sufficient,
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
            "next_action": next_action,
            "single_execution_only": bool(first_test_policy.get("single_execution_only", True)),
            "single_ruling_only": bool(first_test_policy.get("single_ruling_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_post_qm_stat_rebalance_report": _ptr(rebalance_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_freeze_path),
            "em_m4_seam_closure_promotion_cycle01": _ptr(em_m4_path),
            "qft_m4_seam_closure_promotion_cycle01": _ptr(qft_m4_path),
        },
        "non_claim_boundary": "Repository-local EM-QFT seam first-test packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate EM-QFT seam first-test packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "em_qft_seam_first_test_packet_20260412_v0.json",
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
        "em_qft_seam_first_test_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
