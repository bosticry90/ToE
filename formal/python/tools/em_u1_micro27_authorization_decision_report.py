from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_U1_MICRO27_AUTHORIZATION_DECISION_20260418_v0"
DEFAULT_OUT_RELATIVE_PATH = (
    "formal/output/reports/em_u1_micro27_authorization_decision_20260418_v0.json"
)

MICRO26_CLOSEOUT_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "em_u1_micro26_double_divergence_binding_theorem_closeout_decision_20260417_v0.json"
)
PHYSICS_PROGRESS_LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
CONTRADICTION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_maturity_contradiction_report_20260416_v0.json"
)
MICRO27_TARGET_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_27_BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_v0.md"
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


def _em_live_theorem_gap_entry(entries: list[dict[str, Any]], key: str) -> dict[str, Any]:
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        if str(entry.get("row_id", "")).strip() != "ROW-PILLAR-EM-001":
            continue
        if str(entry.get(key, "")).strip() not in {
            "PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP",
            "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP",
        }:
            continue
        return entry
    return {}


def build_report(*, captured_at_utc: str | None) -> dict[str, Any]:
    micro26_closeout = _read_json(MICRO26_CLOSEOUT_REPORT_PATH)
    physics_progress = _read_json(PHYSICS_PROGRESS_LEDGER_PATH)
    contradiction_report = _read_json(CONTRADICTION_REPORT_PATH)

    micro26_summary = dict(micro26_closeout.get("summary", {}))
    contradiction_summary = dict(contradiction_report.get("summary", {}))
    contradictions = contradiction_report.get("contradictions", [])
    if not isinstance(contradictions, list):
        contradictions = []
    modeled_observations = contradiction_report.get("modeled_observations", [])
    if not isinstance(modeled_observations, list):
        modeled_observations = []

    micro27_target_pinned = MICRO27_TARGET_DOC_PATH.exists()
    progress_classification = str(physics_progress.get("progress_classification", "")).strip()
    closeout_requires_explicit_authorization = (
        str(micro26_summary.get("decision", "")).strip() == "RETAIN_MICRO26_BOUNDED_ENDPOINT_v0"
        and str(micro26_summary.get("handoff_status", "")).strip() == "READY_FOR_NEXT_AUTHORIZED_LANE_ONLY_v0"
        and str(micro26_summary.get("next_action", "")).strip()
        == "STOP_AT_MICRO26_CLOSEOUT_PENDING_EXPLICIT_MICRO27_AUTHORIZATION"
        and str(micro26_summary.get("authorized_follow_on", "")).strip() == "MICRO27_ONLY_IF_EXPLICITLY_AUTHORIZED"
    )
    em_theorem_gap_entry = _em_live_theorem_gap_entry(contradictions, "contradiction_type")
    if not em_theorem_gap_entry:
        em_theorem_gap_entry = _em_live_theorem_gap_entry(modeled_observations, "observation_type")
    em_row_still_live_theorem_gap = bool(em_theorem_gap_entry)

    if closeout_requires_explicit_authorization and em_row_still_live_theorem_gap:
        decision = "KEEP_MICRO27_CLOSED_v0"
        authorization_status = "NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0"
        next_action = "OPEN_DISTINCT_MICRO27_AUTHORIZATION_SURFACE_IF_EM_IS_NEXT_BLOCKER_FACING_LANE"
        decision_basis = "GLOBAL_PROGRESS_NONLOCAL_AND_ROW_PILLAR_EM_001_REMAINS_LIVE_THEOREM_GAP"
    elif closeout_requires_explicit_authorization:
        decision = "HOLD_MICRO27_AUTHORIZATION_REVIEW_v0"
        authorization_status = "NOT_AUTHORIZED_PENDING_EM_LOCAL_REVIEW_v0"
        next_action = "REVIEW_EM_LOCAL_BLOCKER_STATE_BEFORE_ANY_MICRO27_DECISION"
        decision_basis = "MICRO26_CLOSEOUT_STILL_REQUIRES_EXPLICIT_AUTHORIZATION"
    else:
        decision = "MICRO27_AUTHORIZATION_BASIS_CHANGED_v0"
        authorization_status = "REVIEW_REQUIRED_v0"
        next_action = "REVIEW_MICRO27_AUTHORIZATION_BASIS_BEFORE_ANY_LANE_ACTIVATION"
        decision_basis = "MICRO26_CLOSEOUT_CONTRACT_NO_LONGER_MATCHES_EXPECTED_BOUNDARY"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "EM_U1_MICRO27_AUTHORIZATION_DECISION_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "micro26_closeout_requires_explicit_authorization": closeout_requires_explicit_authorization,
            "current_progress_classification_is_progress": progress_classification == "PROGRESS",
            "micro27_target_doc_pinned": micro27_target_pinned,
            "em_row_still_live_theorem_gap": em_row_still_live_theorem_gap,
            "distinct_authorization_surface_materialized": True,
        },
        "summary": {
            "decision": decision,
            "decision_basis": decision_basis,
            "authorization_status": authorization_status,
            "automatic_activation_from_global_progress": False,
            "current_progress_classification": progress_classification,
            "em_row_id": "ROW-PILLAR-EM-001",
            "next_action": next_action,
            "required_authorization_basis": "EM_LOCAL_BLOCKER_EVENT_OR_EXPLICIT_MICRO27_AUTHORIZATION_TRANCHE",
        },
        "target_context": {
            "target_id": "TARGET-EM-U1-MICRO-27-BINDING-ASSUMPTIONS-DISCHARGE-FROM-SMOOTHNESS-v0",
            "target_doc": _ptr(MICRO27_TARGET_DOC_PATH),
            "live_em_theorem_gap_entry": em_theorem_gap_entry,
            "contradictions_total": contradiction_summary.get("contradictions_total"),
        },
        "source_bundle": {
            "micro26_closeout_decision_report": _ptr(MICRO26_CLOSEOUT_REPORT_PATH),
            "physics_progress_ledger": _ptr(PHYSICS_PROGRESS_LEDGER_PATH),
            "science_maturity_contradiction_report": _ptr(CONTRADICTION_REPORT_PATH),
            "micro27_target_doc": _ptr(MICRO27_TARGET_DOC_PATH),
        },
        "non_claim_boundary": "Repository-local EM Micro-27 authorization decision report only; no Micro-27 activation, no theorem discharge claim, and no external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the EM U1 Micro-27 authorization decision report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / DEFAULT_OUT_RELATIVE_PATH,
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "em_u1_micro27_authorization_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())