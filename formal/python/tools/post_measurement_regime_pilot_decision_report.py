from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_MEASUREMENT_REGIME_PILOT_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_MEASUREMENT_REGIME_PILOT_DECISION_20260411_v0.json"
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
    candidate_routes = list(declaration.get("candidate_routes", []))

    ruling_path = REPO_ROOT / str(
        required_inputs.get("bounded_measurement_regime_pilot_ruling_report", "")
    )
    execution_path = REPO_ROOT / str(
        required_inputs.get("bounded_measurement_regime_pilot_execution_report", "")
    )

    ruling_report = _read_json(ruling_path)
    execution_report = _read_json(execution_path)

    ruling_summary = dict(ruling_report.get("summary", {}))
    execution_summary = dict(execution_report.get("summary", {}))

    pilot_ruling = str(ruling_summary.get("pilot_ruling", "")).strip()
    execution_classification = str(ruling_summary.get("execution_classification", "")).strip()
    new_signal_fired = bool(ruling_summary.get("new_signal_fired", False))
    retained_signal_fired = bool(ruling_summary.get("retained_signal_fired", False))
    no_loop_rule_from_ruling = str(ruling_summary.get("no_loop_rule", "")).strip()

    # Policy flags
    specific_coupling_defect_identified = bool(
        decision_policy.get("specific_authority_coupling_defect_identified", False)
    )
    specific_coupling_defect_note = decision_policy.get("specific_authority_coupling_defect_note")
    bounded_coupling_refinement_packet = decision_policy.get("bounded_coupling_refinement_packet")
    bounded_coupling_defined = isinstance(bounded_coupling_refinement_packet, str) and bool(
        bounded_coupling_refinement_packet.strip()
    )

    no_loop_rule = str(decision_policy.get("no_loop_rule", "")).strip()
    no_further_pilot_loops_policy = str(
        decision_policy.get("no_further_pilot_loops_policy", "")
    ).strip()
    default_decision = str(decision_policy.get("default_decision", "")).strip()

    # Signal fitness assessment
    pilot_signal_not_fit = pilot_ruling == "REVISED_SIGNAL_NOT_FIT_FOR_PROMOTION_USE"
    pilot_valid_but_nonmoving = pilot_ruling == "REVISED_SIGNAL_VALID_BUT_NONMOVING"
    pilot_moved = pilot_ruling == "REVISED_SIGNAL_REVEALED_MEANINGFUL_MOVEMENT"

    # Decision logic
    coupling_refinement_route_supported = (
        specific_coupling_defect_identified and bounded_coupling_defined
    )
    rollback_route_supported = pilot_signal_not_fit

    if rollback_route_supported:
        decision = "ROLL_BACK_REVISED_SIGNAL_FOR_PROMOTION_USE"
        next_action = "DEPRECATE_REVISED_SIGNAL_AND_RESTORE_PRIOR_REGIME"
        revised_signal_disposition = "ROLL_BACK"
    elif coupling_refinement_route_supported:
        decision = "BOUNDED_AUTHORITY_COUPLING_REFINEMENT_JUSTIFIED"
        next_action = "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_PACKET_ONCE"
        revised_signal_disposition = "COUPLING_REFINEMENT"
    else:
        # Default: retain diagnostically — covers VALID_BUT_NONMOVING with no bounded coupling defect
        decision = "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY"
        next_action = "REGISTER_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY_AND_HOLD"
        revised_signal_disposition = "RETAIN_DIAGNOSTIC"

    candidate_route_assessment = [
        {
            "route_id": "ROLL_BACK_ROUTE",
            "supported": rollback_route_supported,
            "next_action": "DEPRECATE_REVISED_SIGNAL_AND_RESTORE_PRIOR_REGIME",
        },
        {
            "route_id": "RETAIN_DIAGNOSTIC_ROUTE",
            "supported": decision == "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY",
            "next_action": "REGISTER_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY_AND_HOLD",
        },
        {
            "route_id": "AUTHORITY_COUPLING_REFINEMENT_ROUTE",
            "supported": coupling_refinement_route_supported,
            "next_action": "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_PACKET_ONCE",
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "current_pilot_ruling": pilot_ruling,
        "criteria": {
            "pilot_ruling_materialized": pilot_ruling
            in {
                "REVISED_SIGNAL_VALID_BUT_NONMOVING",
                "REVISED_SIGNAL_REVEALED_MEANINGFUL_MOVEMENT",
                "REVISED_SIGNAL_NOT_FIT_FOR_PROMOTION_USE",
            },
            "new_signal_fired": new_signal_fired,
            "retained_signal_fired": retained_signal_fired,
            "rollback_route_supported": rollback_route_supported,
            "coupling_refinement_route_supported": coupling_refinement_route_supported,
            "specific_authority_coupling_defect_identified": specific_coupling_defect_identified,
            "no_loop_rule_declared": no_loop_rule == "ONE_POST_PILOT_DECISION_ONLY",
            "no_further_pilot_loops_enforced": (
                no_further_pilot_loops_policy
                == "NO_FURTHER_MEASUREMENT_REGIME_PILOT_LOOPS_UNTIL_DECISION_RESOLVED"
            ),
            "bounded_decision_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "rollback_route_assessed": True,
                "retain_diagnostic_route_assessed": True,
                "coupling_refinement_route_assessed": True,
                "decision_materialized": decision
                in {
                    "ROLL_BACK_REVISED_SIGNAL_FOR_PROMOTION_USE",
                    "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY",
                    "BOUNDED_AUTHORITY_COUPLING_REFINEMENT_JUSTIFIED",
                },
            },
            "inputs": {
                "candidate_routes": candidate_routes,
                "candidate_route_assessment": candidate_route_assessment,
                "pilot_ruling": pilot_ruling,
                "execution_classification": execution_classification,
                "new_signal_fired": new_signal_fired,
                "retained_signal_fired": retained_signal_fired,
                "specific_coupling_defect_identified": specific_coupling_defect_identified,
                "specific_coupling_defect_note": specific_coupling_defect_note,
                "bounded_coupling_refinement_packet": bounded_coupling_refinement_packet,
                "no_loop_rule": no_loop_rule,
                "no_further_pilot_loops_policy": no_further_pilot_loops_policy,
                "default_decision": default_decision,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "post_pilot_decision": decision,
            "revised_signal_disposition": revised_signal_disposition,
            "new_signal_fired": new_signal_fired,
            "retained_signal_fired": retained_signal_fired,
            "no_loop_rule": no_loop_rule,
            "no_further_pilot_loops_policy": no_further_pilot_loops_policy,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bounded_measurement_regime_pilot_ruling_report": _ptr(ruling_path),
            "bounded_measurement_regime_pilot_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local post-measurement-regime pilot decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-measurement-regime pilot decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "post_measurement_regime_pilot_decision_20260411_v0.json",
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
        "post_measurement_regime_pilot_decision_report: "
        f"decision={payload['summary']['post_pilot_decision']} "
        f"disposition={payload['summary']['revised_signal_disposition']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
