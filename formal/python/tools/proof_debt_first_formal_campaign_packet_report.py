from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_PACKET_20260411_v0.json"
)
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
RETHINK_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "fundamental_attack_strategy_rethink_decision_20260411_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


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


def _open_proof_debt_rows(inventory_text: str) -> int:
    return inventory_text.count("OPEN_PROOF_DEBT")


def _gate_paths_exist(paths: list[str]) -> bool:
    for p in paths:
        fp = REPO_ROOT / p
        if not fp.exists():
            return False
    return True


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    inventory_text = _read_text(INVENTORY_PATH)
    trend = _read_json(TREND_PATH)
    ledger = _read_json(LEDGER_PATH)
    rethink = _read_json(RETHINK_DECISION_PATH)

    proof_debt_objects = declaration.get("proof_debt_objects", [])
    object_model_complete = isinstance(proof_debt_objects, list) and all(
        isinstance(item, dict)
        and str(item.get("debt_id", ""))
        and str(item.get("affected_claim_or_gate", ""))
        and str(item.get("authority_lane_affected", ""))
        and str(item.get("blocker_linkage", ""))
        and str(item.get("discharge_criterion", ""))
        and isinstance(item.get("evidence_needed_for_retirement", []), list)
        and str(item.get("failure_consequence_if_unresolved", ""))
        for item in proof_debt_objects
    )

    bounded_plan = declaration.get("bounded_execution_plan", {})
    discharge_tests = bounded_plan.get("discharge_tests", []) if isinstance(bounded_plan, dict) else []
    discharge_tests_pinned = isinstance(discharge_tests, list) and len(discharge_tests) > 0
    discharge_tests_exist = _gate_paths_exist([str(x) for x in discharge_tests]) if discharge_tests_pinned else False

    cluster = declaration.get("top_proof_debt_cluster_selection", {})
    single_cluster_selected = str(cluster.get("cluster_id", "")) != "" and str(cluster.get("bounded_scope", "")) == "single_cluster_only"

    mapping = declaration.get("blocker_to_proof_debt_mapping", {})
    blocker_mapping_present = isinstance(mapping, dict) and len(mapping) > 0

    theorem_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0) or 0)
    theorem_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_prior) or theorem_prior)
    seam_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("SEAM_INTEGRATION_GAP", 0) or 0)
    seam_current = int(trend.get("blocker_counts", {}).get("current", {}).get("SEAM_INTEGRATION_GAP", seam_prior) or seam_prior)

    theorem_delta = theorem_current - theorem_prior
    seam_delta = seam_current - seam_prior

    blocker_movement = theorem_delta < 0 or seam_delta < 0
    formal_gap_closed_tied_to_blocker = False
    route_falsification_of_blocker_removal_path = False

    open_proof_debt_rows = _open_proof_debt_rows(inventory_text)

    rethink_selected = str(rethink.get("summary", {}).get("selected_next_experimental_class", ""))
    rethink_alignment = rethink_selected == "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN"

    packet_ready = (
        object_model_complete
        and single_cluster_selected
        and blocker_mapping_present
        and discharge_tests_pinned
        and discharge_tests_exist
        and rethink_alignment
    )

    if not packet_ready:
        packet_outcome = "INCONCLUSIVE_PACKET_DEFINITION_OR_INPUTS_INCOMPLETE"
        scientific_state_change = False
    elif blocker_movement or formal_gap_closed_tied_to_blocker or route_falsification_of_blocker_removal_path:
        packet_outcome = "PROOF_DEBT_PACKET_PRODUCTIVE"
        scientific_state_change = True
    else:
        packet_outcome = "PROOF_DEBT_PACKET_READY_NO_BLOCKER_MOVEMENT_YET"
        scientific_state_change = True

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "proof_debt_object_model_complete": object_model_complete,
            "single_cluster_selected": single_cluster_selected,
            "blocker_to_proof_debt_mapping_present": blocker_mapping_present,
            "discharge_tests_pinned_and_present": discharge_tests_pinned and discharge_tests_exist,
            "rethink_alignment_confirmed": rethink_alignment,
        },
        "objective_quality": {
            "criteria": {
                "scientific_state_change_observed": scientific_state_change,
                "blocker_facing_movement_observed": blocker_movement,
                "formal_gap_closed_tied_to_blocker": formal_gap_closed_tied_to_blocker,
                "route_falsification_of_blocker_removal_path": route_falsification_of_blocker_removal_path,
            },
            "inputs": {
                "packet_outcome": packet_outcome,
                "selected_cluster_id": cluster.get("cluster_id"),
                "selected_cluster_name": cluster.get("cluster_name"),
                "proof_debt_object_count": len(proof_debt_objects) if isinstance(proof_debt_objects, list) else 0,
                "open_proof_debt_rows": open_proof_debt_rows,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "seam_integration_gap_prior": seam_prior,
                "seam_integration_gap_current": seam_current,
                "seam_integration_gap_delta": seam_delta,
                "progress_classification": ledger.get("progress_classification"),
            },
            "summary": {
                "all_criteria_satisfied": packet_ready,
                "phase_status": "COMPLETE" if packet_ready else "INCOMPLETE",
                "next_action": (
                    "EXECUTE_BOUNDED_PROOF_DEBT_DISCHARGE_TRANCHE"
                    if packet_ready
                    else "REPAIR_PROOF_DEBT_PACKET_DEFINITION"
                ),
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "selected_cluster_id": cluster.get("cluster_id"),
            "proof_debt_object_count": len(proof_debt_objects) if isinstance(proof_debt_objects, list) else 0,
            "open_proof_debt_rows": open_proof_debt_rows,
            "blocker_facing_movement_observed": blocker_movement,
            "formal_gap_closed_tied_to_blocker": formal_gap_closed_tied_to_blocker,
            "route_falsification_of_blocker_removal_path": route_falsification_of_blocker_removal_path,
            "theorem_gap_delta": theorem_delta,
            "seam_integration_gap_delta": seam_delta,
            "next_action": (
                "EXECUTE_BOUNDED_PROOF_DEBT_DISCHARGE_TRANCHE"
                if packet_ready
                else "REPAIR_PROOF_DEBT_PACKET_DEFINITION"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "inventory": _ptr(INVENTORY_PATH),
            "trend": _ptr(TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
            "fundamental_rethink_decision": _ptr(RETHINK_DECISION_PATH),
        },
        "non_claim_boundary": "Repository-local proof-debt-first campaign packet report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate proof-debt-first formal campaign packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_packet_report_20260411_v0.json",
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
        "proof_debt_first_formal_campaign_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
