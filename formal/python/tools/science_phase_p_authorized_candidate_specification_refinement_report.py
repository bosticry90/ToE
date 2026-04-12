from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_20260412_v0.json"
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
    specification_contract = dict(declaration.get("candidate_specification_contract", {}))
    specification_outcome_contract = dict(
        declaration.get("candidate_specification_outcome_contract", {})
    )

    phase_o_path = REPO_ROOT / str(
        required_inputs.get("science_phase_o_authorized_candidate_next_step_selection_report", "")
    ).strip()
    phase_m_path = REPO_ROOT / str(
        required_inputs.get("science_phase_m_selection_policy_activation_criteria_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_o = _read_json(phase_o_path)
    phase_m = _read_json(phase_m_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_o_summary = dict(phase_o.get("summary", {}))
    phase_m_summary = dict(phase_m.get("summary", {}))

    phase_o_outcome = str(phase_o_summary.get("terminal_outcome", "")).strip()
    phase_o_authorized_lane_id = str(phase_o_summary.get("authorized_lane_id", "")).strip()
    phase_o_packet_authorization = bool(phase_o_summary.get("authorize_first_test_packet", True))
    phase_m_outcome = str(phase_m_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_o_outcome = str(specification_contract.get("required_phase_o_outcome", "")).strip()
    required_phase_o_authorized_lane_id = str(
        specification_contract.get("required_phase_o_authorized_lane_id", "")
    ).strip()
    required_phase_o_packet_authorization = bool(
        specification_contract.get("required_phase_o_packet_authorization", False)
    )
    required_phase_m_outcome = str(specification_contract.get("required_phase_m_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        specification_contract.get("required_non_reopen_summary_outcome", "")
    ).strip()
    forbid_reopen = bool(specification_contract.get("forbid_closed_or_held_lane_reopen", False))

    refined_specification = dict(specification_contract.get("refined_specification", {}))
    observable_interface_target_named = bool(refined_specification.get("observable_interface_target_named", False))
    first_attack_class_admissible_and_named = bool(
        refined_specification.get("first_attack_class_admissible_and_named", False)
    )
    minimum_discriminative_signal_defined = bool(
        refined_specification.get("minimum_discriminative_signal_defined", False)
    )
    anti_alias_evidence_bundle_complete = bool(
        refined_specification.get("anti_alias_evidence_bundle_complete", False)
    )
    missing_phase_o_fields_resolved = bool(refined_specification.get("missing_phase_o_fields_resolved", False))

    specification_shape_ok = all(
        key in refined_specification
        for key in [
            "observable_interface_target_named",
            "first_attack_class_admissible_and_named",
            "minimum_discriminative_signal_defined",
            "anti_alias_evidence_bundle_complete",
            "missing_phase_o_fields_resolved",
        ]
    )

    preconditions_ok = (
        phase_o_outcome == required_phase_o_outcome
        and phase_o_authorized_lane_id == required_phase_o_authorized_lane_id
        and phase_o_packet_authorization == required_phase_o_packet_authorization
        and phase_m_outcome == required_phase_m_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and specification_shape_ok
    )

    allowed_outcomes = set(specification_outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        specification_outcome_contract.get(
            "default_outcome", "AUTHORIZED_CANDIDATE_SPECIFICATION_EVIDENCE_INCOMPLETE"
        )
    ).strip()

    if not specification_shape_ok:
        terminal_outcome = "HOLD_PENDING_AUTHORIZED_CANDIDATE_SPECIFICATION_REPAIR"
        next_action = "REPAIR_REFINED_SPECIFICATION_SHAPE"
        authorize_first_test_packet = False
    elif not preconditions_ok:
        terminal_outcome = "AUTHORIZED_CANDIDATE_SPECIFICATION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_P_PRECONDITIONS_AND_RERUN"
        authorize_first_test_packet = False
    elif not anti_alias_evidence_bundle_complete:
        terminal_outcome = "CANDIDATE_WITHDRAWN"
        next_action = "WITHDRAW_CANDIDATE_UNTIL_ANTI_ALIAS_EVIDENCE_IS_REBUILT"
        authorize_first_test_packet = False
    elif not observable_interface_target_named and not first_attack_class_admissible_and_named:
        terminal_outcome = "CANDIDATE_REQUIRES_DIFFERENT_CANDIDATE_CLASS"
        next_action = "RETURN_TO_HIGHER_LEVEL_SELECTION_POLICY_FOR_DIFFERENT_CANDIDATE_CLASS"
        authorize_first_test_packet = False
    elif (
        observable_interface_target_named
        and first_attack_class_admissible_and_named
        and minimum_discriminative_signal_defined
        and missing_phase_o_fields_resolved
    ):
        terminal_outcome = "CANDIDATE_SPECIFICATION_COMPLETE_PACKET_AUTHORIZATION_JUSTIFIED"
        next_action = "AUTHORIZE_FIRST_TEST_PACKET_FOR_LANE_THERMAL_BOUNDARY_001"
        authorize_first_test_packet = True
    else:
        terminal_outcome = "CANDIDATE_SPECIFICATION_PARTIAL_HOLD_REQUIRES_MORE_DEFINITION"
        next_action = "ADD_MISSING_DISCRIMINATIVE_SIGNAL_AND_RESOLVE_REMAINING_PHASE_O_GAPS"
        authorize_first_test_packet = False

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_o_outcome_match": phase_o_outcome == required_phase_o_outcome,
            "phase_o_authorized_lane_id_match": phase_o_authorized_lane_id == required_phase_o_authorized_lane_id,
            "phase_o_packet_authorization_match": phase_o_packet_authorization == required_phase_o_packet_authorization,
            "phase_m_outcome_match": phase_m_outcome == required_phase_m_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "refined_specification_shape_ok": specification_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                specification_outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_OUTCOME",
            "no_loop_rule_declared": str(
                specification_outcome_contract.get("no_loop_rule", "")
            ).strip()
            == "ONE_SCIENCE_PHASE_P_AUTHORIZED_CANDIDATE_SPECIFICATION_REFINEMENT_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorized_candidate_specification_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_o_outcome": phase_o_outcome,
                "required_phase_o_outcome": required_phase_o_outcome,
                "phase_o_authorized_lane_id": phase_o_authorized_lane_id,
                "required_phase_o_authorized_lane_id": required_phase_o_authorized_lane_id,
                "phase_o_packet_authorization": phase_o_packet_authorization,
                "required_phase_o_packet_authorization": required_phase_o_packet_authorization,
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
        "refined_specification": refined_specification,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_lane_id": required_phase_o_authorized_lane_id,
            "authorize_first_test_packet": authorize_first_test_packet,
            "next_action": next_action,
            "single_layer_only": bool(specification_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(specification_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_o_authorized_candidate_next_step_selection_report": _ptr(phase_o_path),
            "science_phase_m_selection_policy_activation_criteria_report": _ptr(phase_m_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local authorized-candidate specification refinement report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase P authorized-candidate specification refinement report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_p_authorized_candidate_specification_refinement_20260412_v0.json",
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
        "science_phase_p_authorized_candidate_specification_refinement_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorize_first_test_packet={payload['summary']['authorize_first_test_packet']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())