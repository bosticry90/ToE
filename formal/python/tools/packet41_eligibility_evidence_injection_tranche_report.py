from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PACKET41_ELIGIBILITY_EVIDENCE_INJECTION_TRANCHE_20260411_v0"

ELIGIBILITY_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0.json"
TARGETED_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_targeted_justification_review_checkpoint_v0.json"
FORK_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_hold_fork_decision_checkpoint_v0.json"
RETRO_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0.json"
SCORECARD_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json"
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


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    eligibility = _read_json(ELIGIBILITY_PATH)
    targeted = _read_json(TARGETED_PATH)
    fork = _read_json(FORK_PATH)
    retro = _read_json(RETRO_PATH)
    scorecard = _read_json(SCORECARD_PATH)

    e_payload = eligibility.get("payload", {})
    t_payload = targeted.get("payload", {})
    f_payload = fork.get("payload", {})
    r_payload = retro.get("payload", {})
    s_payload = scorecard.get("payload", {})

    required_conditions = e_payload.get("required_conditions_to_exit_hold", {})
    rationale = str(e_payload.get("disposition_decision", {}).get("review_decision_rationale", "")).strip()
    targeted_rationale = str(t_payload.get("review_outcome", {}).get("hold_retention_rationale", "")).strip()
    fork_release_rule = str(
        f_payload.get("decision_output", {}).get("release_from_hold_requires", "")
    ).strip()
    retrospective_alignment = str(
        r_payload.get("disposition_alignment", {}).get("audit_disposition_outcome", "")
    ).strip()

    threshold = s_payload.get("threshold_pass", {})
    review_layer = s_payload.get("review_layer_pass", {})

    evidence_bundle = {
        "eligibility_required_conditions_to_exit_hold": required_conditions,
        "eligibility_hold_rationale": rationale,
        "targeted_justification_hold_rationale": targeted_rationale,
        "hold_fork_release_requirement": fork_release_rule,
        "retrospective_audit_alignment": retrospective_alignment,
        "cycle02_threshold_profile": {
            "threshold_1_pass": threshold.get("threshold_1_pass"),
            "threshold_2_pass": threshold.get("threshold_2_pass"),
            "threshold_3_pass": threshold.get("threshold_3_pass"),
            "threshold_4_pass": threshold.get("threshold_4_pass"),
            "auto_fail_reason": threshold.get("auto_fail_reason"),
        },
        "cycle02_review_layer_pass": review_layer,
    }

    criteria = {
        "required_conditions_materialized": isinstance(required_conditions, dict) and len(required_conditions) >= 4,
        "eligibility_rationale_materialized": bool(rationale),
        "cross_review_rationales_materialized": bool(targeted_rationale) and bool(fork_release_rule) and bool(retrospective_alignment),
        "threshold4_review_layer_failure_explicit": (
            bool(threshold.get("threshold_4_pass", False)) is False
            and str(threshold.get("auto_fail_reason", "")) == "REVIEW_LAYER_STACK_NOT_CLEARED_v0"
        ),
    }

    evidence_injection_ready = all(criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target_component": "packet41_eligibility_review_pass",
        "target": "PACKET41_ELIGIBILITY_REVIEW_EVIDENCE_INJECTION",
        "criteria": criteria,
        "evidence_injection_ready": evidence_injection_ready,
        "evidence_bundle": evidence_bundle,
        "summary": {
            "outcome": "EVIDENCE_INJECTED" if evidence_injection_ready else "EVIDENCE_INCOMPLETE",
            "next_action": "RERUN_PACKET41_SINGLE_COMPONENT_LIFT_TRANCHE",
        },
        "source_bundle": {
            "eligibility_checkpoint": _ptr(ELIGIBILITY_PATH),
            "targeted_checkpoint": _ptr(TARGETED_PATH),
            "hold_fork_checkpoint": _ptr(FORK_PATH),
            "retrospective_checkpoint": _ptr(RETRO_PATH),
            "scorecard_cycle02_checkpoint": _ptr(SCORECARD_PATH),
        },
        "non_claim_boundary": "Repository-local eligibility evidence-injection artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Packet41 eligibility evidence-injection tranche report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "packet41_eligibility_evidence_injection_tranche_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "packet41_eligibility_evidence_injection_tranche_report: "
        f"outcome={payload['summary']['outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())