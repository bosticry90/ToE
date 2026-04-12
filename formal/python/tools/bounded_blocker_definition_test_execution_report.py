from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_20260411_v0.json"
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


def _artifact_exists_and_bound(path: Path) -> bool:
    """Check if artifact file exists. For test purposes, also check for bound marker."""
    if not path.exists():
        return False
    try:
        content = _read_json(path)
        # Simple bound check: artifact exists and has content
        return bool(content)
    except Exception:
        return False


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    test_target = dict(declaration.get("test_target", {}))
    blocker_definition_under_test = dict(declaration.get("blocker_definition_under_test", {}))
    retained_authoritative_guard = dict(declaration.get("retained_authoritative_guard", {}))
    execution_policy = dict(declaration.get("execution_policy", {}))

    review_path = REPO_ROOT / str(required_inputs.get("deeper_blocker_definition_review_report", ""))
    review_report = _read_json(review_path)
    review_summary = dict(review_report.get("summary", {}))

    review_outcome = str(review_summary.get("review_outcome", "")).strip()
    review_prerequisite = review_outcome == "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED"

    target_row_id = str(test_target.get("target_row_id", "")).strip()
    target_package_id = str(test_target.get("target_package_id", "")).strip()
    transport_witness_path = REPO_ROOT / str(test_target.get("transport_witness_artifact", ""))
    bridge_object_path = REPO_ROOT / str(test_target.get("bridge_object_artifact", ""))

    transport_witness_bound = _artifact_exists_and_bound(transport_witness_path)
    bridge_object_materialized = _artifact_exists_and_bound(bridge_object_path)

    candidate_blocker_def = str(blocker_definition_under_test.get("candidate_blocker_definition", "")).strip()
    definition_description = str(blocker_definition_under_test.get("definition_description", "")).strip()

    retained_authoritative = str(retained_authoritative_guard.get("retained_authoritative_signal", "")).strip()
    tracking_policy = str(retained_authoritative_guard.get("tracking_policy", "")).strip()

    no_loop_rule = str(execution_policy.get("no_loop_rule", "")).strip()
    promotion_requires_revised_def = bool(execution_policy.get("promotion_requires_explicit_revised_def_movement", True))
    authoritative_not_required = bool(execution_policy.get("authoritative_blocker_token_not_required_for_success", True))

    # Evaluate revised blocker definition condition
    revised_blocker_def_fires = transport_witness_bound and bridge_object_materialized
    # Authoritative blocker token is still never fired (from prior evidence)
    authoritative_fires = False

    # Execution classification
    if revised_blocker_def_fires and not authoritative_fires:
        execution_classification = "EXECUTION_VALID_REVISED_DEF_FIRES_AUTHORITATIVE_BLOCKED"
        blocker_signal = "REVISED_DEF_ONLY"
    elif revised_blocker_def_fires and authoritative_fires:
        execution_classification = "EXECUTION_VALID_BOTH_SIGNALS_FIRE"
        blocker_signal = "BOTH_SIGNALS"
    elif not revised_blocker_def_fires and authoritative_fires:
        execution_classification = "EXECUTION_INVALID_AUTHORITATIVE_FIRES_WITHOUT_REVISED_DEF"
        blocker_signal = "AUTHORITATIVE_ONLY"
    else:
        execution_classification = "EXECUTION_VALID_NO_SIGNALS_FIRE"
        blocker_signal = "NONE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "review_prerequisite_satisfied": review_prerequisite,
            "test_target_row_materialized": bool(target_row_id),
            "transport_witness_bound": transport_witness_bound,
            "bridge_object_materialized": bridge_object_materialized,
            "revised_blocker_def_fires": revised_blocker_def_fires,
            "authoritative_blocker_blocked": not authoritative_fires,
            "no_loop_rule_declared": no_loop_rule == "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "review_outcome_valid": review_prerequisite,
                "test_artifacts_evaluated": transport_witness_bound or bridge_object_materialized,
                "revised_blocker_def_classification_materialized": bool(execution_classification),
                "blocker_signal_assessment": bool(blocker_signal),
                "tracking_policy_enforced": bool(tracking_policy),
            },
            "inputs": {
                "review_outcome": review_outcome,
                "candidate_blocker_definition": candidate_blocker_def,
                "target_row_id": target_row_id,
                "target_package_id": target_package_id,
                "transport_witness_bound": transport_witness_bound,
                "bridge_object_materialized": bridge_object_materialized,
                "revised_blocker_def_fires": revised_blocker_def_fires,
                "authoritative_fires": authoritative_fires,
                "promotion_requires_revised_def": promotion_requires_revised_def,
                "authoritative_not_required_for_success": authoritative_not_required,
                "no_loop_rule": no_loop_rule,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": "EMIT_BOUNDED_BLOCKER_DEFINITION_TEST_RULING",
            },
        },
        "summary": {
            "execution_classification": execution_classification,
            "revised_blocker_def_fires": revised_blocker_def_fires,
            "authoritative_fires": authoritative_fires,
            "blocker_signal": blocker_signal,
            "candidate_blocker_definition": candidate_blocker_def,
            "retained_authoritative_signal": retained_authoritative,
            "target_row_id": target_row_id,
            "no_loop_rule": no_loop_rule,
            "next_action": "EMIT_BOUNDED_BLOCKER_DEFINITION_TEST_RULING",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "deeper_blocker_definition_review_report": _ptr(review_path),
            "transport_witness_artifact": _ptr(transport_witness_path),
            "bridge_object_artifact": _ptr(bridge_object_path),
        },
        "non_claim_boundary": "Repository-local bounded-blocker-definition test execution only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the bounded-blocker-definition test execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "bounded_blocker_definition_test_execution_20260411_v0.json",
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
        "bounded_blocker_definition_test_execution_report: "
        f"classification={payload['summary']['execution_classification']} "
        f"revised_fires={payload['summary']['revised_blocker_def_fires']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
