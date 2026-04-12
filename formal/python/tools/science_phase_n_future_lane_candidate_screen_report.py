from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_20260412_v0.json"
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


def _candidate_passes(candidate: dict[str, Any]) -> bool:
    return (
        bool(candidate.get("discriminativity_prerequisites_satisfied", False))
        and bool(candidate.get("attack_class_admissibility_satisfied", False))
        and bool(candidate.get("observable_interface_specificity_satisfied", False))
        and bool(candidate.get("anti_alias_confidence_satisfied", False))
        and str(candidate.get("closed_lane_alias_risk", "")).strip() == "LOW"
        and str(candidate.get("authorization_decision", "")).strip() == "AUTHORIZE"
    )


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    candidate_screen_contract = dict(declaration.get("candidate_screen_contract", {}))
    candidate_screen_outcome_contract = dict(
        declaration.get("candidate_screen_outcome_contract", {})
    )

    phase_m_path = REPO_ROOT / str(
        required_inputs.get("science_phase_m_selection_policy_activation_criteria_report", "")
    ).strip()
    phase_l_path = REPO_ROOT / str(
        required_inputs.get("science_phase_l_higher_level_selection_policy_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_m = _read_json(phase_m_path)
    phase_l = _read_json(phase_l_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_m_summary = dict(phase_m.get("summary", {}))
    phase_l_summary = dict(phase_l.get("summary", {}))

    phase_m_outcome = str(phase_m_summary.get("terminal_outcome", "")).strip()
    phase_m_authorize_packet = bool(phase_m_summary.get("authorize_new_untouched_lane_packet", True))
    phase_l_outcome = str(phase_l_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_m_outcome = str(candidate_screen_contract.get("required_phase_m_outcome", "")).strip()
    required_phase_m_authorize_packet = bool(
        candidate_screen_contract.get("required_phase_m_authorize_packet", False)
    )
    required_phase_l_outcome = str(candidate_screen_contract.get("required_phase_l_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        candidate_screen_contract.get("required_non_reopen_summary_outcome", "")
    ).strip()

    forbid_reopen = bool(candidate_screen_contract.get("forbid_closed_or_held_lane_reopen", False))
    authorize_at_most_one_candidate = bool(
        candidate_screen_contract.get("authorize_at_most_one_candidate", False)
    )
    candidate_lanes = list(candidate_screen_contract.get("candidate_lanes", []))

    passed_candidates = [candidate for candidate in candidate_lanes if _candidate_passes(candidate)]
    authorize_count = len(passed_candidates)
    candidate_shape_ok = len(candidate_lanes) >= 1 and all(
        bool(str(candidate.get("lane_id", "")).strip()) for candidate in candidate_lanes
    )

    preconditions_ok = (
        phase_m_outcome == required_phase_m_outcome
        and phase_m_authorize_packet == required_phase_m_authorize_packet
        and phase_l_outcome == required_phase_l_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and candidate_shape_ok
        and (not authorize_at_most_one_candidate or authorize_count <= 1)
    )

    allowed_outcomes = set(candidate_screen_outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        candidate_screen_outcome_contract.get(
            "default_outcome", "FUTURE_LANE_CANDIDATE_SCREEN_EVIDENCE_INCOMPLETE"
        )
    ).strip()

    if not candidate_shape_ok or (authorize_at_most_one_candidate and authorize_count > 1):
        terminal_outcome = "HOLD_PENDING_FUTURE_LANE_SCREEN_REPAIR"
        next_action = "REPAIR_CANDIDATE_SCREEN_SHAPE_OR_AUTHORIZATION_CARDINALITY"
        authorized_lane_id = None
    elif not preconditions_ok:
        terminal_outcome = "FUTURE_LANE_CANDIDATE_SCREEN_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_N_PRECONDITIONS_AND_RERUN"
        authorized_lane_id = None
    elif authorize_count == 1:
        terminal_outcome = "FUTURE_LANE_CANDIDATE_SCREEN_COMPLETE_ONE_AUTHORIZED"
        next_action = "AUTHORIZE_ONE_FUTURE_UNTOUCHED_LANE_FOR_NEXT_BOUNDED_SELECTION_STEP"
        authorized_lane_id = str(passed_candidates[0].get("lane_id", "")).strip()
    else:
        terminal_outcome = "FUTURE_LANE_CANDIDATE_SCREEN_COMPLETE_NONE_AUTHORIZED"
        next_action = "KEEP_AUTHORIZATION_DENY_AND_REFRESH_CANDIDATE_POOL"
        authorized_lane_id = None

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_m_outcome_match": phase_m_outcome == required_phase_m_outcome,
            "phase_m_authorize_packet_match": phase_m_authorize_packet == required_phase_m_authorize_packet,
            "phase_l_outcome_match": phase_l_outcome == required_phase_l_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "candidate_shape_ok": candidate_shape_ok,
            "authorize_at_most_one_candidate": not authorize_at_most_one_candidate or authorize_count <= 1,
            "single_terminal_outcome_rule_declared": str(
                candidate_screen_outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_OUTCOME",
            "no_loop_rule_declared": str(
                candidate_screen_outcome_contract.get("no_loop_rule", "")
            ).strip()
            == "ONE_SCIENCE_PHASE_N_FUTURE_LANE_CANDIDATE_SCREEN_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "candidate_screen_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_m_outcome": phase_m_outcome,
                "required_phase_m_outcome": required_phase_m_outcome,
                "phase_m_authorize_packet": phase_m_authorize_packet,
                "required_phase_m_authorize_packet": required_phase_m_authorize_packet,
                "phase_l_outcome": phase_l_outcome,
                "required_phase_l_outcome": required_phase_l_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "authorize_count": authorize_count,
                "candidate_count": len(candidate_lanes),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "candidate_screen": {
            "candidate_lanes": candidate_lanes,
            "authorized_lane_id": authorized_lane_id,
            "authorized_candidate_count": authorize_count,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_lane_id": authorized_lane_id,
            "authorize_new_untouched_lane_packet": False,
            "next_action": next_action,
            "single_layer_only": bool(candidate_screen_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(candidate_screen_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_m_selection_policy_activation_criteria_report": _ptr(phase_m_path),
            "science_phase_l_higher_level_selection_policy_report": _ptr(phase_l_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local future lane candidate screening report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase N future-lane candidate screen report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_n_future_lane_candidate_screen_20260412_v0.json",
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
        "science_phase_n_future_lane_candidate_screen_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorized_lane_id={payload['summary']['authorized_lane_id']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())