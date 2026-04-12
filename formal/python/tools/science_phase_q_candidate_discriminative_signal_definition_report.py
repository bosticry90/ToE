from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_20260412_v0.json"
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
    signal_contract = dict(declaration.get("discriminative_signal_contract", {}))
    signal_outcome_contract = dict(declaration.get("discriminative_signal_outcome_contract", {}))

    phase_p_path = REPO_ROOT / str(
        required_inputs.get("science_phase_p_authorized_candidate_specification_refinement_report", "")
    ).strip()
    phase_o_path = REPO_ROOT / str(
        required_inputs.get("science_phase_o_authorized_candidate_next_step_selection_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_p = _read_json(phase_p_path)
    phase_o = _read_json(phase_o_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_p_summary = dict(phase_p.get("summary", {}))
    phase_o_summary = dict(phase_o.get("summary", {}))

    phase_p_outcome = str(phase_p_summary.get("terminal_outcome", "")).strip()
    phase_p_authorized_lane_id = str(phase_p_summary.get("authorized_lane_id", "")).strip()
    phase_p_packet_authorization = bool(phase_p_summary.get("authorize_first_test_packet", True))
    phase_o_outcome = str(phase_o_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_p_outcome = str(signal_contract.get("required_phase_p_outcome", "")).strip()
    required_phase_p_authorized_lane_id = str(
        signal_contract.get("required_phase_p_authorized_lane_id", "")
    ).strip()
    required_phase_p_packet_authorization = bool(
        signal_contract.get("required_phase_p_packet_authorization", False)
    )
    required_phase_o_outcome = str(signal_contract.get("required_phase_o_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        signal_contract.get("required_non_reopen_summary_outcome", "")
    ).strip()
    forbid_reopen = bool(signal_contract.get("forbid_closed_or_held_lane_reopen", False))

    signal_definition = dict(signal_contract.get("discriminative_signal_definition", {}))
    observable_interface_measurement_named = bool(
        signal_definition.get("observable_interface_measurement_named", False)
    )
    nonmoving_threshold_defined = bool(signal_definition.get("nonmoving_threshold_defined", False))
    weakly_moving_threshold_defined = bool(signal_definition.get("weakly_moving_threshold_defined", False))
    signal_produced_threshold_defined = bool(
        signal_definition.get("signal_produced_threshold_defined", False)
    )
    remaining_phase_o_fields_resolved = bool(
        signal_definition.get("remaining_phase_o_fields_resolved", False)
    )

    definition_shape_ok = all(
        key in signal_definition
        for key in [
            "observable_interface_measurement_named",
            "nonmoving_threshold_defined",
            "weakly_moving_threshold_defined",
            "signal_produced_threshold_defined",
            "remaining_phase_o_fields_resolved",
        ]
    )

    preconditions_ok = (
        phase_p_outcome == required_phase_p_outcome
        and phase_p_authorized_lane_id == required_phase_p_authorized_lane_id
        and phase_p_packet_authorization == required_phase_p_packet_authorization
        and phase_o_outcome == required_phase_o_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and definition_shape_ok
    )

    allowed_outcomes = set(signal_outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        signal_outcome_contract.get(
            "default_outcome", "DISCRIMINATIVE_SIGNAL_DEFINITION_EVIDENCE_INCOMPLETE"
        )
    ).strip()

    if not definition_shape_ok:
        terminal_outcome = "HOLD_PENDING_DISCRIMINATIVE_SIGNAL_REPAIR"
        next_action = "REPAIR_DISCRIMINATIVE_SIGNAL_DEFINITION_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "DISCRIMINATIVE_SIGNAL_DEFINITION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_Q_PRECONDITIONS_AND_RERUN"
    elif not observable_interface_measurement_named:
        terminal_outcome = "CANDIDATE_REQUIRES_DIFFERENT_CANDIDATE_CLASS"
        next_action = "RETURN_TO_CANDIDATE_CLASS_SELECTION_WITH_MEASUREMENT_REQUIREMENT"
    elif not remaining_phase_o_fields_resolved:
        terminal_outcome = "DISCRIMINATIVE_SIGNAL_PARTIAL_HOLD"
        next_action = "RESOLVE_REMAINING_PHASE_O_FIELDS_ALONGSIDE_SIGNAL_DEFINITION"
    elif (
        nonmoving_threshold_defined
        and weakly_moving_threshold_defined
        and signal_produced_threshold_defined
    ):
        terminal_outcome = "DISCRIMINATIVE_SIGNAL_DEFINED_AND_LOCKED"
        next_action = "CARRY_LOCKED_SIGNAL_FORWARD_TO_PACKET_AUTHORIZATION_REVIEW"
    else:
        terminal_outcome = "DISCRIMINATIVE_SIGNAL_PARTIAL_HOLD"
        next_action = "DEFINE_SIGNAL_PRODUCED_THRESHOLD_AND_COMPLETE_DISCRIMINATIVE_BANDS"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_p_outcome_match": phase_p_outcome == required_phase_p_outcome,
            "phase_p_authorized_lane_id_match": phase_p_authorized_lane_id == required_phase_p_authorized_lane_id,
            "phase_p_packet_authorization_match": phase_p_packet_authorization == required_phase_p_packet_authorization,
            "phase_o_outcome_match": phase_o_outcome == required_phase_o_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "discriminative_signal_definition_shape_ok": definition_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                signal_outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_OUTCOME",
            "no_loop_rule_declared": str(
                signal_outcome_contract.get("no_loop_rule", "")
            ).strip()
            == "ONE_SCIENCE_PHASE_Q_CANDIDATE_DISCRIMINATIVE_SIGNAL_DEFINITION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "discriminative_signal_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_p_outcome": phase_p_outcome,
                "required_phase_p_outcome": required_phase_p_outcome,
                "phase_p_authorized_lane_id": phase_p_authorized_lane_id,
                "required_phase_p_authorized_lane_id": required_phase_p_authorized_lane_id,
                "phase_p_packet_authorization": phase_p_packet_authorization,
                "required_phase_p_packet_authorization": required_phase_p_packet_authorization,
                "phase_o_outcome": phase_o_outcome,
                "required_phase_o_outcome": required_phase_o_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "discriminative_signal_definition": signal_definition,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_lane_id": required_phase_p_authorized_lane_id,
            "authorize_first_test_packet": False,
            "next_action": next_action,
            "single_layer_only": bool(signal_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(signal_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_p_authorized_candidate_specification_refinement_report": _ptr(phase_p_path),
            "science_phase_o_authorized_candidate_next_step_selection_report": _ptr(phase_o_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local candidate discriminative-signal definition report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase Q candidate discriminative-signal definition report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_q_candidate_discriminative_signal_definition_20260412_v0.json",
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
        "science_phase_q_candidate_discriminative_signal_definition_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorize_first_test_packet={payload['summary']['authorize_first_test_packet']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())