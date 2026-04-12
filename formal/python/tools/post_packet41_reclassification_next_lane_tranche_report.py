from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PACKET41_RECLASSIFICATION_NEXT_LANE_TRANCHE_20260411_v0"

PACKET41_BRANCH_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_branch_decision_tranche_20260411_v0.json"
)
CLOSURE_MAP_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
)
SINGLE_ROW_TRANCHE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_SINGLE_ROW_EXECUTION_TRANCHE_20260411_v0.json"
)


NEXT_LANE_ROW_ID = "ROW-PILLAR-QM-001"
NEXT_LANE_BLOCKER_CLASS = "THEOREM_GAP"
NEXT_LANE_TRANCHE_ID = "R4-SINGLE-ROW-QM-001"


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
    packet41_branch = _read_json(PACKET41_BRANCH_DECISION_PATH)
    closure_map = _read_json(CLOSURE_MAP_PATH)
    single_row_tranche = _read_json(SINGLE_ROW_TRANCHE_PATH)

    packet41_decision = str(packet41_branch.get("summary", {}).get("decision", ""))
    packet41_deferred = packet41_decision == "DEFER_OR_RECLASSIFY_PACKET41_NEAR_TERM_BLOCKER_BURN_LANE"

    row = None
    for candidate in closure_map.get("mappings", []):
        if str(candidate.get("row_id", "")) == NEXT_LANE_ROW_ID:
            row = candidate
            break

    selected_row_present = row is not None
    selected_row_blocker_ok = (
        selected_row_present
        and str(row.get("blocker_class", "")) == NEXT_LANE_BLOCKER_CLASS
    )

    tranche_target_row = str(single_row_tranche.get("target_row", ""))
    tranche_blocker = str(single_row_tranche.get("blocker_class", ""))
    success_threshold = str(single_row_tranche.get("success_threshold", ""))
    fail_closed_route = str(
        single_row_tranche.get("no_change_fail_closed_policy", {}).get("route_token", "")
    )

    criteria = {
        "packet41_near_term_deferred": packet41_deferred,
        "next_lane_row_selected": selected_row_present and selected_row_blocker_ok,
        "next_lane_single_row_contract_bound": (
            tranche_target_row == NEXT_LANE_ROW_ID and tranche_blocker == NEXT_LANE_BLOCKER_CLASS
        ),
        "measurable_success_threshold_declared": success_threshold
        == "THEOREM_GAP_DELTA_LT_0_AND_ROW_SUCCESS_COUNT_GT_0",
        "fail_closed_route_declared": fail_closed_route == "ROUTE_TO_THEOREM_GAP_REWORK",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target": "POST_PACKET41_RECLASSIFICATION_AND_NEXT_BLOCKER_BURN_LANE_SELECTION",
        "packet41_reclassification": {
            "near_term_blocker_burn_status": (
                "DEFERRED" if packet41_deferred else "UNRESOLVED"
            ),
            "decision": packet41_decision,
            "decision_reason": packet41_branch.get("summary", {}).get("decision_reason"),
            "next_action": packet41_branch.get("summary", {}).get("next_action"),
        },
        "next_active_lane": {
            "lane_class": "THEOREM_GAP_SINGLE_ROW_EXECUTION",
            "tranche_id": NEXT_LANE_TRANCHE_ID,
            "target_row": NEXT_LANE_ROW_ID,
            "blocker_class": NEXT_LANE_BLOCKER_CLASS,
            "owning_lane": None if row is None else row.get("owning_lane"),
            "required_closure_artifact": None if row is None else row.get("required_closure_artifact"),
            "closure_gate": None if row is None else row.get("closure_gate"),
            "success_threshold": success_threshold,
            "failure_route": fail_closed_route,
        },
        "criteria": criteria,
        "summary": {
            "outcome": "NEXT_LANE_SELECTED" if all(criteria.values()) else "SELECTION_INCOMPLETE",
            "next_action": (
                "RUN_THEOREM_GAP_SINGLE_ROW_AND_QM_SUBTARGET_TRANCHES"
                if all(criteria.values())
                else "RESOLVE_PACKET41_RECLASSIFICATION_OR_NEXT_LANE_BINDING_GAPS"
            ),
        },
        "source_bundle": {
            "packet41_branch_decision": _ptr(PACKET41_BRANCH_DECISION_PATH),
            "closure_map": _ptr(CLOSURE_MAP_PATH),
            "single_row_tranche": _ptr(SINGLE_ROW_TRANCHE_PATH),
        },
        "non_claim_boundary": "Repository-local post-Packet41 reclassification and lane-selection artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate post-Packet41 reclassification and next blocker-burn lane selection report."
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "post_packet41_reclassification_next_lane_tranche_20260411_v0.json",
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
        "post_packet41_reclassification_next_lane_tranche_report: "
        f"outcome={payload['summary']['outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
