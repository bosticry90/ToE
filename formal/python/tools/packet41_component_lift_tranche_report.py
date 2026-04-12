from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PACKET41_COMPONENT_LIFT_TRANCHE_20260411_v0"

DECOMP_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_review_layer_clearance_decomposition_20260411_v0.json"
)
ELIGIBILITY_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0.json"
TARGETED_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_targeted_justification_review_checkpoint_v0.json"
FORK_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_hold_fork_decision_checkpoint_v0.json"
RETRO_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0.json"
ELIGIBILITY_EVIDENCE_INJECTION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_eligibility_evidence_injection_tranche_20260411_v0.json"
)
TARGETED_EVIDENCE_INJECTION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_targeted_justification_evidence_injection_tranche_20260411_v0.json"
)
HOLD_FORK_EVIDENCE_INJECTION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_hold_fork_evidence_injection_tranche_20260411_v0.json"
)

COMPONENTS = {
    "packet41_eligibility_review_pass": ELIGIBILITY_PATH,
    "packet41_targeted_justification_review_pass": TARGETED_PATH,
    "packet41_hold_fork_release_condition_pass": FORK_PATH,
    "retrospective_cumulative_delta_audit_release_condition_pass": RETRO_PATH,
}


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


def _component_current_status(component: str, decomp: dict[str, Any]) -> bool:
    status = decomp.get("decomposition", {}).get("component_status", {})
    return bool(status.get(component, False))


def _component_diagnosis(component: str, checkpoint_payload: dict[str, Any]) -> str:
    p = checkpoint_payload.get("payload", {})
    if component == "packet41_eligibility_review_pass":
        return str(p.get("disposition_decision", {}).get("review_decision_rationale", "missing_eligibility_rationale"))
    if component == "packet41_targeted_justification_review_pass":
        return str(p.get("review_outcome", {}).get("hold_retention_rationale", "missing_targeted_rationale"))
    if component == "packet41_hold_fork_release_condition_pass":
        return str(p.get("decision_rationale", {}).get("rationale_summary", "missing_hold_fork_rationale"))
    if component == "retrospective_cumulative_delta_audit_release_condition_pass":
        return str(p.get("disposition_alignment", {}).get("audit_disposition_outcome", "missing_retro_audit_outcome"))
    return "unknown_component"


def _followup_for(component: str) -> str:
    if component == "packet41_eligibility_review_pass":
        return "ADD_EXPLICIT_REVIEW_LAYER_CLEARANCE_EVIDENCE_TO_ELIGIBILITY_REVIEW"
    if component == "packet41_targeted_justification_review_pass":
        return "ADD_TARGETED_JUSTIFICATION_CLEARANCE_EVIDENCE_WITH_THRESHOLD4_BINDING"
    if component == "packet41_hold_fork_release_condition_pass":
        return "SATISFY_HOLD_FORK_RELEASE_CONDITIONS_WITH_CLEARANCE_PROOF"
    return "RESOLVE_RETROSPECTIVE_AUDIT_RELEASE_ALIGNMENT_FOR_PACKET41"


def build_report(component: str, captured_at_utc: str | None) -> dict[str, Any]:
    if component not in COMPONENTS:
        raise ValueError(f"Unsupported component target: {component}")

    decomp = _read_json(DECOMP_PATH)
    checkpoint_path = COMPONENTS[component]
    checkpoint = _read_json(checkpoint_path)

    current_status = _component_current_status(component, decomp)
    pass_count = int(decomp.get("decomposition", {}).get("pass_count", 0) or 0)
    target_count = int(decomp.get("decomposition", {}).get("target_count", 4) or 4)

    success = current_status is True
    diagnosis = _component_diagnosis(component, checkpoint)
    followup = _followup_for(component)

    evidence_injection_used = False
    evidence_injection_ready = False
    if component == "packet41_eligibility_review_pass" and ELIGIBILITY_EVIDENCE_INJECTION_PATH.exists():
        injected = _read_json(ELIGIBILITY_EVIDENCE_INJECTION_PATH)
        evidence_injection_used = True
        evidence_injection_ready = bool(injected.get("evidence_injection_ready", False))
        if not success and evidence_injection_ready:
            diagnosis = "eligibility evidence injection materialized, but component status remains false; upstream review-layer state unchanged"
            followup = "LIFT_PACKET41_TARGETED_JUSTIFICATION_REVIEW_PASS_NEXT"

    if component == "packet41_targeted_justification_review_pass" and TARGETED_EVIDENCE_INJECTION_PATH.exists():
        injected = _read_json(TARGETED_EVIDENCE_INJECTION_PATH)
        evidence_injection_used = True
        evidence_injection_ready = bool(injected.get("evidence_injection_ready", False))
        if not success and evidence_injection_ready:
            component_status = decomp.get("decomposition", {}).get("component_status", {})
            hold_fork_pass = bool(component_status.get("packet41_hold_fork_release_condition_pass", False))
            retro_pass = bool(component_status.get("retrospective_cumulative_delta_audit_release_condition_pass", False))
            if (not hold_fork_pass) and (not retro_pass):
                diagnosis = "targeted-justification evidence injection materialized, but hold-fork and retrospective release components remain false"
                followup = "LIFT_PACKET41_HOLD_FORK_RELEASE_CONDITION_PASS_NEXT"
            elif hold_fork_pass and (not retro_pass):
                diagnosis = "targeted-justification lift still blocked by retrospective cumulative-delta audit release component"
                followup = "LIFT_PACKET41_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_PASS_NEXT"
            elif (not hold_fork_pass) and retro_pass:
                diagnosis = "targeted-justification lift still blocked by hold-fork release condition component"
                followup = "LIFT_PACKET41_HOLD_FORK_RELEASE_CONDITION_PASS_NEXT"
            else:
                diagnosis = "targeted-justification evidence injection materialized, but component status remains false"
                followup = "RECHECK_TARGETED_JUSTIFICATION_DECISION_BINDING"

    if component == "packet41_hold_fork_release_condition_pass" and HOLD_FORK_EVIDENCE_INJECTION_PATH.exists():
        injected = _read_json(HOLD_FORK_EVIDENCE_INJECTION_PATH)
        evidence_injection_used = True
        evidence_injection_ready = bool(injected.get("evidence_injection_ready", False))
        if not success and evidence_injection_ready:
            component_status = decomp.get("decomposition", {}).get("component_status", {})
            retro_pass = bool(component_status.get("retrospective_cumulative_delta_audit_release_condition_pass", False))
            if not retro_pass:
                diagnosis = "hold-fork evidence injection materialized, but retrospective cumulative-delta audit release component remains false"
                followup = "LIFT_PACKET41_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_PASS_NEXT"
            else:
                diagnosis = "hold-fork evidence injection materialized, but hold-fork component remains false with retrospective gate already true"
                followup = "RECHECK_HOLD_FORK_DECISION_BINDING"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target_component": component,
        "target": "PACKET41_REVIEW_LAYER_SINGLE_COMPONENT_LIFT",
        "expected_state_change": "REVIEW_LAYER_PASS_COUNT_INCREASE_BY_AT_LEAST_1",
        "inputs": {
            "pass_count_before_or_current": pass_count,
            "target_count": target_count,
            "component_current_status": current_status,
        },
        "criteria": {
            "single_component_targeted": True,
            "component_exists_in_decomposition": component in decomp.get("decomposition", {}).get("required_components", []),
            "packet41_only_lane_required": True,
        },
        "summary": {
            "component_lift_observed": success,
            "outcome": "SUCCESS" if success else "NO_LIFT",
            "failure_diagnosis": None if success else diagnosis,
            "narrow_followup_action": None if success else followup,
            "next_action": "RECOMPUTE_BLOCKER_STATE" if success else "RUN_NEXT_PACKET41_SINGLE_COMPONENT_LIFT_TRANCHE",
            "evidence_injection_used": evidence_injection_used,
            "evidence_injection_ready": evidence_injection_ready,
            "stop_rule": {
                "active": component == "packet41_hold_fork_release_condition_pass",
                "triggered": bool(component == "packet41_hold_fork_release_condition_pass" and (not success)),
                "rule": "after_hold_fork_no_lift_issue_branch_decision",
                "branch_recommendation": (
                    "DEFER_OR_RECLASSIFY_PACKET41_NEAR_TERM_BLOCKER_BURN_LANE"
                    if component == "packet41_hold_fork_release_condition_pass" and (not success)
                    else None
                ),
            },
        },
        "source_bundle": {
            "decomposition_report": _ptr(DECOMP_PATH),
            "component_checkpoint": _ptr(checkpoint_path),
        },
        "non_claim_boundary": "Repository-local Packet41 component lift tranche artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Packet41 single-component lift tranche report.")
    parser.add_argument("--component", default="packet41_eligibility_review_pass", choices=sorted(COMPONENTS.keys()))
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "packet41_component_lift_tranche_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(component=ns.component, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "packet41_component_lift_tranche_report: "
        f"component={payload['target_component']} "
        f"outcome={payload['summary']['outcome']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())