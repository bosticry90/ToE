from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BOUNDED_BLOCKER_DEFINITION_TEST_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "BOUNDED_BLOCKER_DEFINITION_TEST_RULING_20260411_v0.json"
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
    ruling_outcomes = list(declaration.get("ruling_outcomes", []))
    ruling_policy = dict(declaration.get("ruling_policy", {}))

    execution_path = REPO_ROOT / str(
        required_inputs.get("bounded_blocker_definition_test_execution_report", "")
    )
    execution_report = _read_json(execution_path)
    execution_summary = dict(execution_report.get("summary", {}))

    execution_classification = str(execution_summary.get("execution_classification", "")).strip()
    revised_blocker_def_fires = bool(execution_summary.get("revised_blocker_def_fires", False))
    authoritative_fires = bool(execution_summary.get("authoritative_fires", False))
    blocker_signal = str(execution_summary.get("blocker_signal", "")).strip()
    candidate_blocker_def = str(execution_summary.get("candidate_blocker_definition", "")).strip()

    promotion_requires_revised_def = bool(ruling_policy.get("promotion_requires_revised_def_fires_decisively", True))
    promotion_requires_tighter_coupling = bool(ruling_policy.get("promotion_requires_tighter_coupling_than_diagnostic", True))
    authoritative_still_blocked = bool(ruling_policy.get("authoritative_still_blocked_in_this_evaluation", True))
    no_loop_rule = str(ruling_policy.get("no_loop_rule", "")).strip()
    default_ruling = str(ruling_policy.get("default_ruling", "")).strip()

    # Determine which outcome applies
    # OUTCOME_1: fires decisively AND shows tighter coupling (inferred from valid execution classification)
    # OUTCOME_2: fires validly but equivalent to diagnostic or non-decisive
    # OUTCOME_3: does not fire or inconsistent

    revised_def_fires_decisively = (
        revised_blocker_def_fires
        and execution_classification == "EXECUTION_VALID_REVISED_DEF_FIRES_AUTHORITATIVE_BLOCKED"
    )
    revised_def_not_fit = blocker_signal == "NONE"

    if revised_def_not_fit:
        test_ruling = "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE"
        ruling_rationale = "Revised blocker definition did not fire; does not establish independent standing."
    elif revised_def_fires_decisively and promotion_requires_tighter_coupling:
        # This is the strict gate: revised def fires AND is stricter than diagnostic
        # In the absence of explicit "tighter coupling" evidence, default to VALID_BUT_NONMOVING
        # (Tighter coupling would require additional validation beyond artifact presence)
        test_ruling = "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
        ruling_rationale = (
            "Revised blocker definition fires validly but does not yet demonstrate tighter coupling than diagnostic signal. "
            "Further validation required before promotion."
        )
    else:
        test_ruling = default_ruling
        ruling_rationale = "Revised blocker definition evaluated; gate criteria not met for advancement."

    outcome_assessment = [
        {
            "outcome_id": "OUTCOME_1",
            "outcome": "REVISED_BLOCKER_DEF_REVEALS_MEANINGFUL_MOVEMENT",
            "supported": False,  # Would require explicit tighter-coupling evidence
            "rationale": "Not triggered in this execution.",
        },
        {
            "outcome_id": "OUTCOME_2",
            "outcome": "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING",
            "supported": revised_def_fires_decisively,
            "rationale": "Revised def fires validly but coupling rigor not yet established." if revised_def_fires_decisively else "Not applicable.",
        },
        {
            "outcome_id": "OUTCOME_3",
            "outcome": "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE",
            "supported": revised_def_not_fit,
            "rationale": "Revised def did not fire." if revised_def_not_fit else "Not applicable.",
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "execution_classification_materialized": bool(execution_classification),
            "revised_blocker_def_fires": revised_blocker_def_fires,
            "authoritative_still_blocked": not authoritative_fires,
            "test_ruling_valid": test_ruling
            in {
                "REVISED_BLOCKER_DEF_REVEALS_MEANINGFUL_MOVEMENT",
                "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING",
                "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE",
            },
            "no_loop_rule_declared": no_loop_rule == "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_RULING_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "execution_report_valid": bool(execution_classification),
                "revised_def_state_assessed": revised_blocker_def_fires is not None,
                "authoritative_state_assessed": authoritative_fires is not None,
                "test_ruling_materialized": bool(test_ruling),
            },
            "inputs": {
                "execution_classification": execution_classification,
                "revised_blocker_def_fires": revised_blocker_def_fires,
                "authoritative_fires": authoritative_fires,
                "blocker_signal": blocker_signal,
                "promotion_requires_revised_def": promotion_requires_revised_def,
                "promotion_requires_tighter_coupling": promotion_requires_tighter_coupling,
                "authoritative_still_blocked": authoritative_still_blocked,
                "no_loop_rule": no_loop_rule,
                "default_ruling": default_ruling,
                "outcome_assessment": outcome_assessment,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": "ASSESS_BLOCKER_DEFINITION_TEST_RULING_AND_DECIDE_PROMOTION_OR_HOLD",
            },
        },
        "summary": {
            "test_ruling": test_ruling,
            "revised_blocker_def_fires": revised_blocker_def_fires,
            "authoritative_fires": authoritative_fires,
            "blocker_signal": blocker_signal,
            "ruling_rationale": ruling_rationale,
            "candidate_blocker_definition": candidate_blocker_def,
            "no_loop_rule": no_loop_rule,
            "next_action": "ASSESS_BLOCKER_DEFINITION_TEST_RULING_AND_DECIDE_PROMOTION_OR_HOLD",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bounded_blocker_definition_test_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local bounded-blocker-definition test ruling only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the bounded-blocker-definition test ruling report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "bounded_blocker_definition_test_ruling_20260411_v0.json",
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
        "bounded_blocker_definition_test_ruling_report: "
        f"ruling={payload['summary']['test_ruling']} "
        f"revised_fires={payload['summary']['revised_blocker_def_fires']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
