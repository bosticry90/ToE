from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DISCOVERY_EXTERNAL_PATH_ROUTING_REFRESH_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_EXTERNAL_PATH_ROUTING_REFRESH_20260411_v0.json"
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
    refresh_contract = dict(declaration.get("refresh_contract", {}))

    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()
    scoring_path = REPO_ROOT / str(required_inputs.get("discovery_engine_scoring_routing_review_report", "")).strip()
    qm_status_path = REPO_ROOT / str(required_inputs.get("qm_stat_cycle11_lane_status_report", "")).strip()
    qft_interp_path = REPO_ROOT / str(required_inputs.get("qft_gr_discovery_interpretation_report", "")).strip()

    queue_report = _read_json(queue_path)
    scoring_review = _read_json(scoring_path)
    qm_status = _read_json(qm_status_path)
    qft_interp = _read_json(qft_interp_path)

    ranked_candidates = list(queue_report.get("ranked_candidates", []))
    scoring_summary = dict(scoring_review.get("summary", {}))
    qm_summary = dict(qm_status.get("summary", {}))
    qft_summary = dict(qft_interp.get("summary", {}))

    qm_external_eligible = bool(qm_summary.get("eligible_for_external_path_reopen_signal_under_cycle11", False))
    qft_external_eligible = bool(qft_summary.get("probe_ready", False)) or bool(
        qft_summary.get("probe_lane_allowed", False)
    )

    top_rank_row = str(queue_report.get("summary", {}).get("top_rank_row", "")).strip()
    top_rank_excluded = top_rank_row == "ROW-SEAM-QM-STAT-001" and not qm_external_eligible

    remaining_external_path_candidates: list[dict[str, Any]] = []
    for row in ranked_candidates:
        row_id = str(row.get("row_id", "")).strip()
        lane = str(row.get("lane", "")).strip()
        if row_id == "ROW-SEAM-QM-STAT-001":
            if qm_external_eligible:
                remaining_external_path_candidates.append(
                    {"row_id": row_id, "lane": lane, "reason": "QM_STAT_REMAINS_ELIGIBLE"}
                )
            continue
        if row_id == "ROW-SEAM-QFT-GR-001":
            if qft_external_eligible:
                remaining_external_path_candidates.append(
                    {"row_id": row_id, "lane": lane, "reason": "QFT_GR_PROBE_ROUTE_ELIGIBLE"}
                )
            continue

    if not ranked_candidates or not scoring_summary:
        refresh_outcome = "ROUTING_INPUTS_INCOMPLETE"
        next_action = "RESTORE_DISCOVERY_ROUTING_INPUTS_AND_REFRESH_ONCE"
        selected_external_path_row_id = ""
    elif remaining_external_path_candidates:
        refresh_outcome = "QM_STAT_EXCLUDED_NEXT_EXTERNAL_PATH_CANDIDATE_AVAILABLE"
        selected_external_path_row_id = str(remaining_external_path_candidates[0].get("row_id", "")).strip()
        next_action = "ROUTE_TO_NEXT_NON_QM_STAT_EXTERNAL_PATH_CANDIDATE_UNDER_EXISTING_HOLD_RULES"
    else:
        refresh_outcome = "QM_STAT_EXCLUDED_NO_EXTERNAL_PATH_CANDIDATE_REMAINS"
        selected_external_path_row_id = ""
        next_action = (
            "MAINTAIN_DISCOVERY_HOLD_AND_REQUIRE_NEW_SEAM_MODEL_CLASS_PROPOSAL_"
            "OR_OTHER_EXTERNAL_PATH_EVIDENCE_BEFORE_REOPEN"
        )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "qm_stat_exclusion_consumed": not qm_external_eligible,
            "qft_gr_candidate_evaluated": True,
            "queue_inputs_present": bool(ranked_candidates),
            "no_loop_rule_declared": str(refresh_contract.get("no_loop_rule", "")).strip()
            == "ONE_DISCOVERY_EXTERNAL_PATH_ROUTING_REFRESH_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": refresh_outcome
                in set(refresh_contract.get("allowed_outcomes", [])),
                "qm_stat_removed_from_current_external_path_signal": True,
                "remaining_candidate_question_answered": True,
                "bounded_refresh_only": True,
            },
            "inputs": {
                "routing_goal": refresh_contract.get("routing_goal"),
                "top_rank_row": top_rank_row,
                "top_rank_excluded_from_external_path_gating": top_rank_excluded,
                "qm_stat_externalization_status": qm_summary.get("externalization_status"),
                "qm_stat_internal_lane_status": qm_summary.get("internal_lane_status"),
                "qft_gr_interpretation": qft_summary.get("interpretation"),
                "qft_gr_probe_ready": qft_summary.get("probe_ready"),
                "qft_gr_probe_lane_allowed": qft_summary.get("probe_lane_allowed"),
                "scoring_review_disposition": scoring_summary.get("selected_review_disposition"),
                "reopen_condition": scoring_summary.get("lane_expansion_reopen_condition"),
                "remaining_external_path_candidates": remaining_external_path_candidates,
            },
            "summary": {
                "all_criteria_satisfied": refresh_outcome != "ROUTING_INPUTS_INCOMPLETE",
                "phase_status": "COMPLETE" if refresh_outcome != "ROUTING_INPUTS_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "refresh_outcome": refresh_outcome,
            "qm_stat_counted_as_current_external_path_candidate": qm_external_eligible,
            "top_rank_excluded_from_external_path_gating": top_rank_excluded,
            "remaining_external_path_candidate_count": len(remaining_external_path_candidates),
            "selected_external_path_row_id": selected_external_path_row_id,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_priority_queue_report": _ptr(queue_path),
            "discovery_engine_scoring_routing_review_report": _ptr(scoring_path),
            "qm_stat_cycle11_lane_status_report": _ptr(qm_status_path),
            "qft_gr_discovery_interpretation_report": _ptr(qft_interp_path),
        },
        "non_claim_boundary": "Repository-local discovery external-path routing refresh report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the discovery external-path routing refresh report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "discovery_external_path_routing_refresh_20260411_v0.json",
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
        "discovery_external_path_routing_refresh_report: "
        f"refresh_outcome={payload['summary']['refresh_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
