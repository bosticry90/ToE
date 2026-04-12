from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_QM_RECLASSIFICATION_NEXT_LANE_TRANCHE_20260411_v0"

QM_STOP_RULE_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_bounded_stop_rule_decision_20260411_v0.json"
)
CLOSURE_MAP_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
)

EXCLUDED_ROW = "ROW-PILLAR-QM-001"
PREFERRED_ORDER = [
    "ROW-PILLAR-GR-001",
    "ROW-PILLAR-STAT-001",
    "ROW-PILLAR-COSMO-001",
    "ROW-PILLAR-EM-001",
    "ROW-PILLAR-QFT-001",
    "ROW-PILLAR-SR-001",
    "ROW-SEAM-QFT-GR-001",
    "ROW-SEAM-QM-STAT-001",
    "ROW-SEAM-COSMO-SR-001",
]


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


def _pick_next_non_qm_lane(mappings: list[dict[str, Any]]) -> dict[str, Any] | None:
    by_row = {str(m.get("row_id", "")): m for m in mappings}
    for row_id in PREFERRED_ORDER:
        if row_id == EXCLUDED_ROW:
            continue
        candidate = by_row.get(row_id)
        if candidate is None:
            continue
        if str(candidate.get("blocker_class", "")) in {"THEOREM_GAP", "SEAM_INTEGRATION_GAP", "PARITY_DRIFT"}:
            return candidate
    for candidate in mappings:
        row_id = str(candidate.get("row_id", ""))
        if row_id == EXCLUDED_ROW:
            continue
        if str(candidate.get("blocker_class", "")) in {"THEOREM_GAP", "SEAM_INTEGRATION_GAP", "PARITY_DRIFT"}:
            return candidate
    return None


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    qm_decision = _read_json(QM_STOP_RULE_DECISION_PATH)
    closure_map = _read_json(CLOSURE_MAP_PATH)

    decision = str(qm_decision.get("summary", {}).get("decision", ""))
    qm_deferred = decision == "DEFER_OR_RECLASSIFY_QM_NEAR_TERM_BLOCKER_BURN_LANE"

    selected = _pick_next_non_qm_lane(list(closure_map.get("mappings", [])))
    selected_present = selected is not None

    criteria = {
        "qm_near_term_deferred": qm_deferred,
        "next_non_qm_lane_selected": selected_present,
        "selected_lane_is_not_qm": selected_present and str(selected.get("row_id", "")) != EXCLUDED_ROW,
        "selected_lane_is_blocker_bearing": selected_present and str(selected.get("blocker_class", "")) in {"THEOREM_GAP", "SEAM_INTEGRATION_GAP", "PARITY_DRIFT"},
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target": "POST_QM_RECLASSIFICATION_AND_NEXT_NON_QM_BLOCKER_BEARING_LANE_SELECTION",
        "qm_reclassification": {
            "near_term_blocker_burn_status": "DEFERRED" if qm_deferred else "UNRESOLVED",
            "decision": decision,
            "decision_reason": qm_decision.get("summary", {}).get("failure_diagnosis"),
            "next_action": qm_decision.get("summary", {}).get("next_action"),
        },
        "next_active_lane": (
            {
                "row_id": selected.get("row_id"),
                "domain": selected.get("domain"),
                "blocker_class": selected.get("blocker_class"),
                "owning_lane": selected.get("owning_lane"),
                "closure_gate": selected.get("closure_gate"),
                "required_closure_artifact": selected.get("required_closure_artifact"),
                "exit_criterion": selected.get("exit_criterion"),
                "success_threshold": "BLOCKER_STATE_CHANGE_OBSERVED_FOR_SELECTED_ROW",
                "failure_route": "ROUTE_TO_BLOCKER_CLASS_REWORK",
            }
            if selected_present
            else None
        ),
        "criteria": criteria,
        "summary": {
            "outcome": "NEXT_NON_QM_LANE_SELECTED" if all(criteria.values()) else "SELECTION_INCOMPLETE",
            "next_action": (
                "RUN_SELECTED_NON_QM_BLOCKER_BURN_TRANCHE"
                if all(criteria.values())
                else "RESOLVE_QM_RECLASSIFICATION_OR_SELECTION_GAPS"
            ),
        },
        "source_bundle": {
            "qm_stop_rule_decision": _ptr(QM_STOP_RULE_DECISION_PATH),
            "closure_map": _ptr(CLOSURE_MAP_PATH),
        },
        "non_claim_boundary": "Repository-local post-QM reclassification and lane-selection artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate post-QM reclassification and next non-QM lane selection report."
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "post_qm_reclassification_next_lane_tranche_20260411_v0.json",
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
        "post_qm_reclassification_next_lane_tranche_report: "
        f"outcome={payload['summary']['outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
