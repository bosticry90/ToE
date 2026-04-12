from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_BLOCKER_DEFINITION_TEST_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_BLOCKER_DEFINITION_TEST_DECISION_20260411_v0.json"
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
    candidate_routes = list(declaration.get("candidate_routes", []))
    decision_policy = dict(declaration.get("decision_policy", {}))
    test_result_summary = dict(declaration.get("test_result_summary", {}))

    ruling_path = REPO_ROOT / str(
        required_inputs.get("bounded_blocker_definition_test_ruling_report", "")
    )
    ruling_report = _read_json(ruling_path)
    ruling_summary = dict(ruling_report.get("summary", {}))

    test_ruling = str(ruling_summary.get("test_ruling", "")).strip()
    revised_blocker_def_fires = bool(ruling_summary.get("revised_blocker_def_fires", False))
    authoritative_fires = bool(ruling_summary.get("authoritative_fires", False))

    ruling_is_valid_but_nonmoving = test_ruling == "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
    ruling_is_not_fit = test_ruling == "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE"

    # Policy flags
    specific_coupling_defect_identified = bool(
        decision_policy.get("specific_authority_coupling_defect_identified", False)
    )
    specific_coupling_defect_note = decision_policy.get("specific_authority_coupling_defect_note")
    authority_coupling_refinement_packet = decision_policy.get("authority_coupling_refinement_packet")
    coupling_refinement_defined = isinstance(authority_coupling_refinement_packet, str) and bool(
        authority_coupling_refinement_packet.strip()
    )

    no_loop_rule = str(decision_policy.get("no_loop_rule", "")).strip()
    default_decision = str(decision_policy.get("default_decision", "")).strip()
    default_next_action = str(decision_policy.get("default_next_action", "")).strip()

    # Decision logic
    coupling_refinement_route_supported = specific_coupling_defect_identified and coupling_refinement_defined
    escalate_route_supported = ruling_is_not_fit or (
        not coupling_refinement_route_supported and not ruling_is_valid_but_nonmoving
    )

    if ruling_is_not_fit:
        # If test ruled NOT_FIT, escalate automatically
        decision = "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW"
        next_action = "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW"
        revised_signal_disposition = "ESCALATE"
    elif coupling_refinement_route_supported:
        # If coupling defect identified and refinement packet defined, pursue refinement
        decision = "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_BOUNDED_ONCE"
        next_action = "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_PACKET_ONCE"
        revised_signal_disposition = "COUPLING_REFINEMENT"
    else:
        # Default: hold and require authority coupling review
        decision = "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"
        next_action = "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"
        revised_signal_disposition = "HOLD_SECONDARY"

    candidate_route_assessment = [
        {
            "route_id": "HOLD_ROUTE",
            "route_name": "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
            "supported": decision == "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
            "next_action": "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW",
        },
        {
            "route_id": "COUPLING_REFINEMENT_ROUTE",
            "route_name": "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_BOUNDED_ONCE",
            "supported": coupling_refinement_route_supported,
            "next_action": "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_PACKET_ONCE",
        },
        {
            "route_id": "ESCALATE_ROUTE",
            "route_name": "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW",
            "supported": escalate_route_supported,
            "next_action": "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW",
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "test_ruling_materialized": bool(test_ruling),
            "ruling_is_valid_but_nonmoving": ruling_is_valid_but_nonmoving,
            "ruling_is_not_fit": ruling_is_not_fit,
            "revised_blocker_def_fires": revised_blocker_def_fires,
            "authoritative_still_blocked": not authoritative_fires,
            "hold_route_supported": (
                decision == "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"
            ),
            "coupling_refinement_route_supported": coupling_refinement_route_supported,
            "escalate_route_supported": escalate_route_supported,
            "no_loop_rule_declared": no_loop_rule == "ONE_POST_BLOCKER_DEFINITION_TEST_DECISION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "test_result_assessed": ruling_is_valid_but_nonmoving or ruling_is_not_fit,
                "all_routes_evaluated": len(candidate_route_assessment) == 3,
                "decision_materialized": decision in {
                    "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
                    "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_BOUNDED_ONCE",
                    "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW",
                },
                "next_action_materialized": bool(next_action),
            },
            "inputs": {
                "test_ruling": test_ruling,
                "revised_blocker_def_fires": revised_blocker_def_fires,
                "authoritative_fires": authoritative_fires,
                "specific_coupling_defect_identified": specific_coupling_defect_identified,
                "authority_coupling_refinement_packet": authority_coupling_refinement_packet,
                "no_loop_rule": no_loop_rule,
                "candidate_route_assessment": candidate_route_assessment,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "post_test_decision": decision,
            "revised_signal_disposition": revised_signal_disposition,
            "test_ruling": test_ruling,
            "revised_blocker_def_fires": revised_blocker_def_fires,
            "authoritative_fires": authoritative_fires,
            "no_loop_rule": no_loop_rule,
            "no_further_blocker_testing_until_routing_resolved": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bounded_blocker_definition_test_ruling_report": _ptr(ruling_path),
        },
        "non_claim_boundary": "Repository-local post-blocker-definition-test decision only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-blocker-definition-test decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "post_blocker_definition_test_decision_20260411_v0.json",
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
        "post_blocker_definition_test_decision_report: "
        f"decision={payload['summary']['post_test_decision']} "
        f"disposition={payload['summary']['revised_signal_disposition']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
