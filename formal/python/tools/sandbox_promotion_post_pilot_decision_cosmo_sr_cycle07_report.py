from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SANDBOX_PROMOTION_POST_PILOT_DECISION_COSMO_SR_CYCLE07_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SANDBOX_PROMOTION_POST_PILOT_DECISION_COSMO_SR_CYCLE07_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


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

    governed_report_path = REPO_ROOT / str(required_inputs.get("governed_review_report", "")).strip()
    wrapper_path = REPO_ROOT / str(required_inputs.get("governed_review_wrapper", "")).strip()
    pilot_binding_path = REPO_ROOT / str(required_inputs.get("pilot_binding", "")).strip()
    phase2_phase6_path = REPO_ROOT / str(required_inputs.get("phase2_phase6_declaration", "")).strip()

    governed_report = _read_json(governed_report_path)
    _read_json(wrapper_path)
    pilot_binding = _read_json(pilot_binding_path)
    phase2_phase6_text = _read_text(phase2_phase6_path)

    summary = dict(governed_report.get("summary", {}))
    objective_summary = dict(governed_report.get("objective_quality", {}).get("summary", {}))
    binding = dict(pilot_binding.get("pilot_binding", {}))

    governed_hold = (
        summary.get("terminal_outcome") == str(decision_policy.get("required_hold_terminal_outcome", "")).strip()
        and summary.get("governed_decision") == str(decision_policy.get("required_hold_decision", "")).strip()
        and summary.get("canonical_mutation_emitted") is False
        and summary.get("artifact_adjudication") == str(decision_policy.get("required_artifact_adjudication_for_nonwidened_hold", "")).strip()
    )
    governed_promote = (
        summary.get("terminal_outcome") == "SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED"
        and summary.get("governed_decision") == "promote"
        and summary.get("canonical_mutation_emitted") is True
    )
    governed_reject = (
        summary.get("terminal_outcome") == "SANDBOX_PROMOTION_GOVERNED_REVIEW_REJECT_DECISION_EMITTED"
        and summary.get("governed_decision") == "reject"
        and summary.get("canonical_mutation_emitted") is False
    )
    no_loop_rule = str(decision_policy.get("no_loop_rule", "")).strip()
    no_further_widening_policy = str(decision_policy.get("no_further_widening_policy", "")).strip()

    if governed_hold:
        decision = "RETAIN_BOUNDED_PILOT_NONWIDENED_AFTER_GOVERNED_HOLD"
        disposition = "HOLD_NONWIDENED"
        next_action = "IMPLEMENT_AUTHORITY_OWNERSHIP_HARDENING_TRANCHE_BEFORE_ANY_WIDENING_OR_RETIREMENT"
    elif governed_promote:
        decision = "AUTHORIZE_NEXT_BOUNDED_PROMOTION_WIDENING_REVIEW"
        disposition = "WIDEN_CANDIDATE"
        next_action = "DECLARE_NEXT_BOUNDED_PROMOTION_WIDENING_TRANCHE"
    elif governed_reject:
        decision = "RETURN_PILOT_TO_SANDBOX_ONLY_STATUS"
        disposition = "RETIRE_TO_SANDBOX_ONLY"
        next_action = "RETURN_PILOT_TO_SANDBOX_ONLY_STATUS_AND_DECLARE_RETIREMENT_REVIEW_IF_NEEDED"
    else:
        decision = "POST_PILOT_DECISION_EVIDENCE_INCOMPLETE"
        disposition = "EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PILOT_DECISION_INPUTS_AND_RERUN"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "governed_review_report_present": governed_report.get("schema_id")
            == "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_REPORT_20260419_v0",
            "pilot_binding_present": binding.get("pilot_track_id") == "SANDBOX_PROMOTION_PILOT_COSMO_SR_CYCLE07",
            "phase2_phase6_declaration_present": "Phase 2 completion and Phase 6 bounded audit kickoff" in phase2_phase6_text,
            "hold_nonwidened_route_supported": governed_hold,
            "widen_route_supported": governed_promote,
            "retire_route_supported": governed_reject,
            "no_loop_rule_declared": no_loop_rule == "ONE_SANDBOX_PROMOTION_POST_PILOT_DECISION_ONLY",
            "no_further_widening_policy_declared": no_further_widening_policy
            == "NO_WIDENING_OR_RETIREMENT_BEFORE_POST_PILOT_DECISION_IS_FORMALIZED",
            "bounded_decision_materialized": decision != "POST_PILOT_DECISION_EVIDENCE_INCOMPLETE",
        },
        "objective_quality": {
            "criteria": {
                "hold_route_assessed": True,
                "widen_route_assessed": True,
                "retire_route_assessed": True,
                "decision_materialized": decision != "POST_PILOT_DECISION_EVIDENCE_INCOMPLETE",
            },
            "inputs": {
                "pilot_track_id": binding.get("pilot_track_id"),
                "target_row_id": binding.get("target_row_id"),
                "target_seam_id": binding.get("target_seam_id"),
                "governed_terminal_outcome": summary.get("terminal_outcome"),
                "governed_decision": summary.get("governed_decision"),
                "artifact_adjudication": summary.get("artifact_adjudication"),
                "prior_next_action": objective_summary.get("next_action"),
                "no_loop_rule": no_loop_rule,
                "no_further_widening_policy": no_further_widening_policy,
                "candidate_routes": candidate_routes,
            },
            "summary": {
                "all_criteria_satisfied": decision != "POST_PILOT_DECISION_EVIDENCE_INCOMPLETE",
                "phase_status": "COMPLETE" if decision != "POST_PILOT_DECISION_EVIDENCE_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "post_pilot_decision": decision,
            "pilot_disposition": disposition,
            "target_row_id": binding.get("target_row_id"),
            "target_seam_id": binding.get("target_seam_id"),
            "governed_terminal_outcome": summary.get("terminal_outcome"),
            "governed_decision": summary.get("governed_decision"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "governed_review_report": _ptr(governed_report_path),
            "governed_review_wrapper": _ptr(wrapper_path),
            "pilot_binding": _ptr(pilot_binding_path),
            "phase2_phase6_declaration": _ptr(phase2_phase6_path),
        },
        "non_claim_boundary": "Repository-local post-pilot decision report only; no scientific adequacy, canonical promotion, or widening claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the sandbox-promotion post-pilot decision report for COSMO-SR Cycle07.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
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
        "sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_report: "
        f"decision={payload['summary']['post_pilot_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())