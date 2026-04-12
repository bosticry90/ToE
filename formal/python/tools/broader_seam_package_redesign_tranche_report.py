from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "BROADER_SEAM_PACKAGE_REDESIGN_TRANCHE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "BROADER_SEAM_PACKAGE_REDESIGN_TRANCHE_20260411_v0.json"
)
BLOCKER_CLOSURE_MAP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
ROW_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"


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


def _find_row(mappings: list[dict[str, Any]], row_id: str) -> dict[str, Any] | None:
    for m in mappings:
        if str(m.get("row_id", "")) == row_id:
            return m
    return None


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    closure_map = _read_json(BLOCKER_CLOSURE_MAP_PATH)
    trend = _read_json(TREND_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    ledger = _read_json(LEDGER_PATH)

    target = declaration.get("target_seam_package", {})
    row_id = str(target.get("row_id", ""))
    named_blocker = str(target.get("blocker_class", "SEAM_INTEGRATION_GAP"))

    mappings = closure_map.get("mappings", [])
    target_mapping = _find_row(mappings if isinstance(mappings, list) else [], row_id)

    prior = trend.get("blocker_counts", {}).get("prior", {})
    current = trend.get("blocker_counts", {}).get("current", {})

    seam_prior = int(prior.get("SEAM_INTEGRATION_GAP", 0) or 0)
    seam_current = int(current.get("SEAM_INTEGRATION_GAP", seam_prior) or seam_prior)
    seam_delta = seam_current - seam_prior

    theorem_prior = int(prior.get("THEOREM_GAP", 0) or 0)
    theorem_current = int(current.get("THEOREM_GAP", theorem_prior) or theorem_prior)
    theorem_delta = theorem_current - theorem_prior

    named_prior = int(prior.get(named_blocker, 0) or 0)
    named_current = int(current.get(named_blocker, named_prior) or named_prior)
    named_delta = named_current - named_prior

    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    global_row_success = sum(int((v or {}).get("success", 0) or 0) for v in row_counts.values()) if isinstance(row_counts, dict) else 0

    seam_delta_improved = seam_delta < 0
    theorem_delta_improved = theorem_delta < 0
    row_success_observed = global_row_success > 0
    named_blocker_state_changed = named_delta != 0
    blocker_movement = seam_delta_improved or theorem_delta_improved or row_success_observed or named_blocker_state_changed

    if target_mapping is None:
        outcome = "INCONCLUSIVE_TARGET_SEAM_PACKAGE_MAPPING_MISSING"
        scientific_state_change = False
    elif blocker_movement:
        outcome = "SEAM_REDESIGN_BLOCKER_MOVEMENT_OBSERVED"
        scientific_state_change = True
    else:
        outcome = "SEAM_REDESIGN_NO_BLOCKER_MOVEMENT"
        scientific_state_change = False

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "tranche_id": declaration.get("tranche_id"),
        "criteria": {
            "target_seam_package_mapped": target_mapping is not None,
            "structural_hypothesis_declared": bool(declaration.get("structural_redesign_hypothesis", {}).get("statement")),
            "blocker_success_contract_declared": bool(declaration.get("blocker_facing_success_contract", {}).get("success")),
            "blocker_state_recompute_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "scientific_state_change_observed": scientific_state_change,
                "blocker_facing_movement_observed": blocker_movement,
                "named_blocker_class_changed_state": named_blocker_state_changed,
            },
            "inputs": {
                "packet_outcome": outcome,
                "target_row_id": row_id,
                "target_mapping_present": target_mapping is not None,
                "named_blocker_class": named_blocker,
                "seam_integration_gap_prior": seam_prior,
                "seam_integration_gap_current": seam_current,
                "seam_integration_gap_delta": seam_delta,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "global_row_success_count": global_row_success,
                "named_blocker_prior": named_prior,
                "named_blocker_current": named_current,
                "named_blocker_delta": named_delta,
                "progress_classification": ledger.get("progress_classification"),
            },
            "summary": {
                "all_criteria_satisfied": blocker_movement,
                "phase_status": "COMPLETE" if target_mapping is not None else "INCOMPLETE",
                "next_action": (
                    "RECOMPUTE_BLOCKER_STATE_AND_CONFIRM_REDUCTION"
                    if blocker_movement
                    else "ESCALATE_TO_DIFFERENT_ATTACK_CLASS"
                ),
            },
        },
        "summary": {
            "packet_outcome": outcome,
            "target_seam_package": target.get("name"),
            "target_row_id": row_id,
            "structural_change_proposed": declaration.get("structural_redesign_hypothesis", {}).get("proposed_structural_change"),
            "blocker_facing_movement_observed": blocker_movement,
            "seam_integration_gap_delta": seam_delta,
            "theorem_gap_delta": theorem_delta,
            "global_row_success_count": global_row_success,
            "named_blocker_class_changed_state": named_blocker_state_changed,
            "next_action": (
                "RECOMPUTE_BLOCKER_STATE_AND_CONFIRM_REDUCTION"
                if blocker_movement
                else "ESCALATE_TO_DIFFERENT_ATTACK_CLASS"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "blocker_closure_map": _ptr(BLOCKER_CLOSURE_MAP_PATH),
            "trend": _ptr(TREND_PATH),
            "row_outcome_trend": _ptr(ROW_TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local broader seam package redesign tranche report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate broader seam package redesign tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "broader_seam_package_redesign_tranche_report_20260411_v0.json",
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
    print(f"broader_seam_package_redesign_tranche_report: packet_outcome={payload['summary']['packet_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
