from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_20260412_v0.json"
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
    authorized_candidate_contract = dict(declaration.get("authorized_candidate_contract", {}))
    authorized_candidate_outcome_contract = dict(
        declaration.get("authorized_candidate_outcome_contract", {})
    )

    phase_n_path = REPO_ROOT / str(
        required_inputs.get("science_phase_n_future_lane_candidate_screen_report", "")
    ).strip()
    phase_m_path = REPO_ROOT / str(
        required_inputs.get("science_phase_m_selection_policy_activation_criteria_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_n = _read_json(phase_n_path)
    phase_m = _read_json(phase_m_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_n_summary = dict(phase_n.get("summary", {}))
    phase_m_summary = dict(phase_m.get("summary", {}))

    phase_n_outcome = str(phase_n_summary.get("terminal_outcome", "")).strip()
    phase_n_authorized_lane_id = str(phase_n_summary.get("authorized_lane_id", "")).strip()
    phase_n_packet_authorization = bool(phase_n_summary.get("authorize_new_untouched_lane_packet", True))
    phase_m_outcome = str(phase_m_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_n_outcome = str(authorized_candidate_contract.get("required_phase_n_outcome", "")).strip()
    required_phase_n_authorized_lane_id = str(
        authorized_candidate_contract.get("required_phase_n_authorized_lane_id", "")
    ).strip()
    required_phase_n_packet_authorization = bool(
        authorized_candidate_contract.get("required_phase_n_packet_authorization", False)
    )
    required_phase_m_outcome = str(authorized_candidate_contract.get("required_phase_m_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        authorized_candidate_contract.get("required_non_reopen_summary_outcome", "")
    ).strip()
    forbid_reopen = bool(authorized_candidate_contract.get("forbid_closed_or_held_lane_reopen", False))

    evidence = dict(authorized_candidate_contract.get("authorized_candidate_evidence", {}))
    phase_m_criteria_satisfied = bool(evidence.get("phase_m_criteria_satisfied", False))
    non_aliasing_against_lane_end_family = bool(
        evidence.get("non_aliasing_against_lane_end_family", False)
    )
    observable_interface_specificity_complete = bool(
        evidence.get("observable_interface_specificity_complete", False)
    )
    first_attack_class_defined_without_underdefinition = bool(
        evidence.get("first_attack_class_defined_without_underdefinition", False)
    )
    risk_of_valid_but_nonmoving_repeat_bounded = bool(
        evidence.get("risk_of_valid_but_nonmoving_repeat_bounded", False)
    )

    evidence_shape_ok = all(
        key in evidence
        for key in [
            "phase_m_criteria_satisfied",
            "non_aliasing_against_lane_end_family",
            "observable_interface_specificity_complete",
            "first_attack_class_defined_without_underdefinition",
            "risk_of_valid_but_nonmoving_repeat_bounded",
        ]
    )

    preconditions_ok = (
        phase_n_outcome == required_phase_n_outcome
        and phase_n_authorized_lane_id == required_phase_n_authorized_lane_id
        and phase_n_packet_authorization == required_phase_n_packet_authorization
        and phase_m_outcome == required_phase_m_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and evidence_shape_ok
    )

    allowed_outcomes = set(authorized_candidate_outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        authorized_candidate_outcome_contract.get(
            "default_outcome", "AUTHORIZED_CANDIDATE_SELECTION_EVIDENCE_INCOMPLETE"
        )
    ).strip()

    if not evidence_shape_ok:
        terminal_outcome = "HOLD_PENDING_AUTHORIZED_CANDIDATE_SELECTION_REPAIR"
        next_action = "REPAIR_AUTHORIZED_CANDIDATE_EVIDENCE_SHAPE"
        first_test_packet_authorized = False
    elif not preconditions_ok:
        terminal_outcome = "AUTHORIZED_CANDIDATE_SELECTION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_O_PRECONDITIONS_AND_RERUN"
        first_test_packet_authorized = False
    elif not phase_m_criteria_satisfied or not non_aliasing_against_lane_end_family:
        terminal_outcome = "CANDIDATE_PATH_WITHDRAWN"
        next_action = "WITHDRAW_AUTHORIZED_CANDIDATE_AND_RETURN_TO_CANDIDATE_POOL_REVIEW"
        first_test_packet_authorized = False
    elif (
        observable_interface_specificity_complete
        and first_attack_class_defined_without_underdefinition
        and risk_of_valid_but_nonmoving_repeat_bounded
    ):
        terminal_outcome = "AUTHORIZE_LANE_THERMAL_BOUNDARY_FIRST_TEST_PACKET"
        next_action = "OPEN_FIRST_TEST_PACKET_FOR_LANE_THERMAL_BOUNDARY_001"
        first_test_packet_authorized = True
    elif observable_interface_specificity_complete or first_attack_class_defined_without_underdefinition:
        terminal_outcome = "REQUIRE_ONE_MORE_CANDIDATE_LEVEL_CLARIFICATION"
        next_action = "ADD_MISSING_OBSERVABLE_OR_ATTACK_CLASS_CLARIFICATION_BEFORE_PACKET"
        first_test_packet_authorized = False
    else:
        terminal_outcome = "HOLD_AUTHORIZED_CANDIDATE_AND_DO_NOT_OPEN_PACKET"
        next_action = "KEEP_AUTHORIZED_CANDIDATE_HELD_PENDING_SPECIFICATION_IMPROVEMENT"
        first_test_packet_authorized = False

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_n_outcome_match": phase_n_outcome == required_phase_n_outcome,
            "phase_n_authorized_lane_id_match": phase_n_authorized_lane_id == required_phase_n_authorized_lane_id,
            "phase_n_packet_authorization_match": phase_n_packet_authorization == required_phase_n_packet_authorization,
            "phase_m_outcome_match": phase_m_outcome == required_phase_m_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "authorized_candidate_evidence_shape_ok": evidence_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                authorized_candidate_outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_OUTCOME",
            "no_loop_rule_declared": str(
                authorized_candidate_outcome_contract.get("no_loop_rule", "")
            ).strip()
            == "ONE_SCIENCE_PHASE_O_AUTHORIZED_CANDIDATE_NEXT_STEP_SELECTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorized_candidate_selection_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_n_outcome": phase_n_outcome,
                "required_phase_n_outcome": required_phase_n_outcome,
                "phase_n_authorized_lane_id": phase_n_authorized_lane_id,
                "required_phase_n_authorized_lane_id": required_phase_n_authorized_lane_id,
                "phase_n_packet_authorization": phase_n_packet_authorization,
                "required_phase_n_packet_authorization": required_phase_n_packet_authorization,
                "phase_m_outcome": phase_m_outcome,
                "required_phase_m_outcome": required_phase_m_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "authorized_candidate_evidence": evidence,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_lane_id": required_phase_n_authorized_lane_id,
            "authorize_first_test_packet": first_test_packet_authorized,
            "next_action": next_action,
            "single_layer_only": bool(authorized_candidate_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(authorized_candidate_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_n_future_lane_candidate_screen_report": _ptr(phase_n_path),
            "science_phase_m_selection_policy_activation_criteria_report": _ptr(phase_m_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local authorized-candidate next-step selection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase O authorized-candidate next-step selection report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_o_authorized_candidate_next_step_selection_20260412_v0.json",
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
        "science_phase_o_authorized_candidate_next_step_selection_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorize_first_test_packet={payload['summary']['authorize_first_test_packet']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())