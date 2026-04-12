from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_ATTACK_STYLE_RETHINK_DECISION_20260411_v0"

PACKET41_BRANCH_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_branch_decision_tranche_20260411_v0.json"
)
QM_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_bounded_stop_rule_decision_20260411_v0.json"
)
GR_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json"
)
STAT_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_stat_bounded_stop_rule_decision_20260411_v0.json"
)
COSMO_BOUNDED_STOP_RULE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_cosmo_bounded_stop_rule_decision_20260411_v0.json"
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
    packet41 = _read_json(PACKET41_BRANCH_DECISION_PATH)
    qm = _read_json(QM_BOUNDED_STOP_RULE_PATH)
    gr = _read_json(GR_BOUNDED_STOP_RULE_PATH)
    stat = _read_json(STAT_BOUNDED_STOP_RULE_PATH)
    cosmo = _read_json(COSMO_BOUNDED_STOP_RULE_PATH)

    packet41_flat = (
        str(packet41.get("summary", {}).get("decision", ""))
        == "DEFER_OR_RECLASSIFY_PACKET41_NEAR_TERM_BLOCKER_BURN_LANE"
    )
    qm_flat = bool(qm.get("summary", {}).get("stop_rule_triggered", False))
    gr_flat = bool(gr.get("summary", {}).get("stop_rule_triggered", False))
    stat_flat = bool(stat.get("summary", {}).get("stop_rule_triggered", False))
    cosmo_flat = bool(cosmo.get("summary", {}).get("stop_rule_triggered", False))

    all_flat = packet41_flat and qm_flat and gr_flat and stat_flat and cosmo_flat

    if all_flat:
        decision = "CURRENT_ROW_BY_ROW_BLOCKER_BURN_STRATEGY_IS_NONPRODUCTIVE"
        next_action = "SELECT_AND_EXECUTE_ONE_NEW_SCIENTIFIC_ATTACK_CLASS_PROGRAM"
        selected_attack_class = "SIMULATION_FIRST_FALSIFICATION_CAMPAIGN"
    else:
        decision = "ROW_ROTATION_STRATEGY_NOT_YET_EXHAUSTED"
        next_action = "CONTINUE_BOUNDED_ROW_EXECUTION_UNTIL_EXHAUSTION_CRITERIA_MET"
        selected_attack_class = None

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet41_no_movement_deferred": packet41_flat,
            "qm_no_movement_stop_rule_triggered": qm_flat,
            "gr_no_movement_stop_rule_triggered": gr_flat,
            "stat_no_movement_stop_rule_triggered": stat_flat,
            "cosmo_no_movement_stop_rule_triggered": cosmo_flat,
        },
        "summary": {
            "decision": decision,
            "all_five_lanes_flat": all_flat,
            "next_action": next_action,
            "selected_attack_class": selected_attack_class,
            "available_attack_classes": [
                "BROADER_SEAM_PACKAGE_REDESIGN",
                "EXTERNAL_DISCRIMINATIVE_BENCHMARK_PROGRAM",
                "PROOF_DEBT_FIRST_FORMAL_DERIVATION_CAMPAIGN",
                "SIMULATION_FIRST_FALSIFICATION_CAMPAIGN"
            ],
        },
        "source_bundle": {
            "packet41_branch_decision": _ptr(PACKET41_BRANCH_DECISION_PATH),
            "qm_bounded_stop_rule": _ptr(QM_BOUNDED_STOP_RULE_PATH),
            "gr_bounded_stop_rule": _ptr(GR_BOUNDED_STOP_RULE_PATH),
            "stat_bounded_stop_rule": _ptr(STAT_BOUNDED_STOP_RULE_PATH),
            "cosmo_bounded_stop_rule": _ptr(COSMO_BOUNDED_STOP_RULE_PATH),
        },
        "non_claim_boundary": "Repository-local strategy-rethink decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate higher-level scientific attack-style rethink decision report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_attack_style_rethink_decision_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"science_attack_style_rethink_decision_report: decision={payload['summary']['decision']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
