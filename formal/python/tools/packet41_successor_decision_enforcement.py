from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PACKET41_SUCCESSOR_DECISION_ENFORCEMENT_20260411_v0"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PACKET41_SUCCESSOR_DECISION_ENFORCEMENT_20260411_v0.md"
SUCCESSOR_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0.json"
CYCLE01_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json"
CYCLE02_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json"
MEASUREMENT_PROTOCOL_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_numeric_threshold_measurement_protocol_checkpoint_v0.json"


REQUIRED_POLICY_TOKENS = [
    "PACKET41_NUMERIC_CLEARANCE_THRESHOLD_v0",
    "PACKET41_REEVALUATION_DEADLINE_UTC_v0",
    "PACKET41_STATE_TRANSITION_RULE_v0",
    "PACKET41_STATUS_ROUTE_v0",
]


def _read(path: Path) -> str:
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


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    inventory = _read(INVENTORY_PATH)
    policy = _read(POLICY_PATH)
    successor_checkpoint = _read_json(SUCCESSOR_CHECKPOINT_PATH)
    cycle01 = _read_json(CYCLE01_PATH)
    cycle02 = _read_json(CYCLE02_PATH)
    measurement_protocol = _read_json(MEASUREMENT_PROTOCOL_PATH)

    cycle01_payload = cycle01.get("payload", {})
    cycle02_payload = cycle02.get("payload", {})
    cycle01_threshold = cycle01_payload.get("threshold_pass", {})
    cycle02_threshold = cycle02_payload.get("threshold_pass", {})
    cycle02_values = cycle02_payload.get("scorecard_values", {})
    successor_readiness = successor_checkpoint.get("payload", {}).get("numeric_measurement_readiness", {})
    successor_hold_alignment = successor_checkpoint.get("payload", {}).get("hold_policy_alignment", {})
    protocol_hold_policy = measurement_protocol.get("payload", {}).get("hold_policy", {})

    cycle01_outcome = str(cycle01_payload.get("evaluation_outcome", ""))
    cycle02_outcome = str(cycle02_payload.get("evaluation_outcome", ""))
    outcome_transition = f"{cycle01_outcome} -> {cycle02_outcome}"

    cycle02_required_value_keys = (
        "D_prev",
        "A_prev",
        "O_prev",
        "D_curr",
        "A_curr",
        "O_curr",
        "N_curr",
        "G_prev",
        "G_curr",
        "S_value",
        "M_value",
        "Streak3_value",
    )

    criteria = {
        "inventory_has_packet41_hold_row": "INV-PHYS-QFT-GR-PACKET41-HOLD" in inventory,
        "inventory_has_packet41_successor_row": "INV-PHYS-QFT-GR-PACKET41-SUCCESSOR-PACKAGE-v0" in inventory,
        "policy_has_required_tokens": all(token in policy for token in REQUIRED_POLICY_TOKENS),
        "policy_has_transition_path": "HOLD -> REEVALUATE -> PROMOTABLE_OR_REJECTED" in policy,
        "successor_checkpoint_present": successor_checkpoint.get("artifact_id")
        == "toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0",
        "cycle02_scorecard_present": cycle02.get("artifact_id")
        == "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0",
    }
    all_satisfied = all(criteria.values())

    objective_criteria = {
        "cycle_outcome_transition_evidenced": (
            cycle01_outcome == "HOLD_RETAINED_DUE_TO_MISSING_ADMISSIBLE_NUMERIC_INPUTS_v0"
            and cycle02_outcome == "HOLD_RETAINED_DUE_TO_REVIEW_LAYER_FAILURE_v0"
        ),
        "cycle02_numeric_values_materialized": all(
            cycle02_values.get(key) is not None for key in cycle02_required_value_keys
        ),
        "cycle02_threshold_profile_consistent": (
            cycle02_threshold.get("threshold_1_pass") is True
            and cycle02_threshold.get("threshold_2_pass") is True
            and cycle02_threshold.get("threshold_3_pass") is True
            and cycle02_threshold.get("threshold_4_pass") is False
            and cycle02_threshold.get("auto_fail_reason") == "REVIEW_LAYER_STACK_NOT_CLEARED_v0"
        ),
        "hold_alignment_with_review_failure": (
            successor_readiness.get("scorecard_cycle02_outcome_status")
            == "HOLD_RETAINED_DUE_TO_REVIEW_LAYER_FAILURE_v0"
            and successor_readiness.get("release_clearance_status")
            == "NOT_CLEARED_REVIEW_LAYER_STACK_PENDING_v0"
            and successor_hold_alignment.get("packet41_authorization_freeze_status")
            == "ENFORCED_v0"
            and protocol_hold_policy.get("automatic_release_without_threshold_4_pass")
            == "FORBIDDEN_v0"
            and cycle02_payload.get("authorization_artifact_creation") == "FORBIDDEN_v0"
        ),
        "cycle01_to_cycle02_admissibility_improved": (
            cycle01_threshold.get("auto_fail_reason")
            == "MISSING_REQUIRED_NUMERIC_FIELDS_FROM_ADMISSIBLE_CHECKPOINTS_v0"
            and cycle02_threshold.get("auto_fail_reason")
            == "REVIEW_LAYER_STACK_NOT_CLEARED_v0"
        ),
    }
    objective_all_satisfied = all(objective_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "cycle01_outcome": cycle01_outcome,
                "cycle02_outcome": cycle02_outcome,
                "outcome_transition": outcome_transition,
                "cycle02_threshold_profile": {
                    "threshold_1_pass": cycle02_threshold.get("threshold_1_pass"),
                    "threshold_2_pass": cycle02_threshold.get("threshold_2_pass"),
                    "threshold_3_pass": cycle02_threshold.get("threshold_3_pass"),
                    "threshold_4_pass": cycle02_threshold.get("threshold_4_pass"),
                    "auto_fail_reason": cycle02_threshold.get("auto_fail_reason"),
                },
                "cycle02_required_value_keys": list(cycle02_required_value_keys),
            },
            "summary": {
                "all_criteria_satisfied": objective_all_satisfied,
                "phase_status": "COMPLETE" if objective_all_satisfied else "INCOMPLETE",
                "next_action": (
                    "PHASE_D_GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION"
                    if objective_all_satisfied
                    else "RESTORE_PACKET41_TRANSITION_EVIDENCE"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "phase_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": "PHASE_D_GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION" if all_satisfied else "PIN_PACKET41_DECISION_FIELDS",
        },
        "source_bundle": {
            "inventory": _ptr(INVENTORY_PATH),
            "policy": _ptr(POLICY_PATH),
            "successor_checkpoint": _ptr(SUCCESSOR_CHECKPOINT_PATH),
            "scorecard_cycle01": _ptr(CYCLE01_PATH),
            "scorecard_cycle02": _ptr(CYCLE02_PATH),
            "measurement_protocol": _ptr(MEASUREMENT_PROTOCOL_PATH),
        },
        "non_claim_boundary": "Repository-local Packet41 decision enforcement artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Packet41 successor decision enforcement report.")
    parser.add_argument("--out", type=Path, default=REPO_ROOT / "formal" / "output" / "reports" / "packet41_successor_decision_enforcement_20260411_v0.json")
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"packet41_successor_decision_enforcement: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
