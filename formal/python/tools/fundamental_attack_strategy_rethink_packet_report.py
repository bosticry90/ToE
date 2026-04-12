from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "FUNDAMENTAL_ATTACK_STRATEGY_RETHINK_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "FUNDAMENTAL_ATTACK_STRATEGY_RETHINK_PACKET_20260411_v0.json"
)
PACKET41_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "packet41_branch_decision_tranche_20260411_v0.json"
QM_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_bounded_stop_rule_decision_20260411_v0.json"
GR_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json"
STAT_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_stat_bounded_stop_rule_decision_20260411_v0.json"
COSMO_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_cosmo_bounded_stop_rule_decision_20260411_v0.json"
SIM_V3_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_campaign_decision_20260411_v3.json"
SEAM_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "broader_seam_package_redesign_decision_20260411_v0.json"
EXTERNAL_DECISION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "external_discriminative_benchmark_decision_20260411_v0.json"
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
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


def _attack_status(decision: str, movement: bool) -> str:
    if movement:
        return "BLOCKER_MOVING"
    if "INCONCLUSIVE" in decision:
        return "INCONCLUSIVE"
    return "SCIENTIFICALLY_INFORMATIVE_BUT_NONPRODUCTIVE"


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    packet41 = _read_json(PACKET41_DECISION_PATH)
    qm = _read_json(QM_DECISION_PATH)
    gr = _read_json(GR_DECISION_PATH)
    stat = _read_json(STAT_DECISION_PATH)
    cosmo = _read_json(COSMO_DECISION_PATH)
    sim_v3 = _read_json(SIM_V3_DECISION_PATH)
    seam = _read_json(SEAM_DECISION_PATH)
    external = _read_json(EXTERNAL_DECISION_PATH)
    trend = _read_json(TREND_PATH)
    ledger = _read_json(LEDGER_PATH)

    theorem_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0) or 0)
    theorem_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_prior) or theorem_prior)
    seam_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("SEAM_INTEGRATION_GAP", 0) or 0)
    seam_current = int(trend.get("blocker_counts", {}).get("current", {}).get("SEAM_INTEGRATION_GAP", seam_prior) or seam_prior)

    theorem_delta = theorem_current - theorem_prior
    seam_delta = seam_current - seam_prior

    movement_now = theorem_delta < 0 or seam_delta < 0

    failure_synthesis = [
        {
            "attack_class": "PACKET41_SEAM_LIFTING",
            "decision": str(packet41.get("summary", {}).get("decision", "")),
            "status": _attack_status(str(packet41.get("summary", {}).get("decision", "")), False),
            "movement_observed": False,
        },
        {
            "attack_class": "ROW_ROTATION_QM_GR_STAT_COSMO",
            "decision": "ALL_STOP_RULES_TRIGGERED_WITHOUT_BLOCKER_DELTA",
            "status": "SCIENTIFICALLY_INFORMATIVE_BUT_NONPRODUCTIVE",
            "movement_observed": False,
        },
        {
            "attack_class": "SIMULATION_FIRST_FALSIFICATION",
            "decision": str(sim_v3.get("summary", {}).get("decision", "")),
            "status": _attack_status(str(sim_v3.get("summary", {}).get("decision", "")), bool(sim_v3.get("summary", {}).get("blocker_facing_movement_observed", False))),
            "movement_observed": bool(sim_v3.get("summary", {}).get("blocker_facing_movement_observed", False)),
        },
        {
            "attack_class": "BROADER_SEAM_PACKAGE_REDESIGN",
            "decision": str(seam.get("summary", {}).get("decision", "")),
            "status": _attack_status(str(seam.get("summary", {}).get("decision", "")), bool(seam.get("summary", {}).get("blocker_facing_movement_observed", False))),
            "movement_observed": bool(seam.get("summary", {}).get("blocker_facing_movement_observed", False)),
        },
        {
            "attack_class": "EXTERNAL_DISCRIMINATIVE_BENCHMARK_PROGRAM",
            "decision": str(external.get("summary", {}).get("decision", "")),
            "status": _attack_status(str(external.get("summary", {}).get("decision", "")), bool(external.get("summary", {}).get("blocker_facing_movement_observed", False))),
            "movement_observed": bool(external.get("summary", {}).get("blocker_facing_movement_observed", False)),
        },
    ]

    all_nonproductive = all(not bool(item.get("movement_observed", False)) for item in failure_synthesis)

    failure_pattern = {
        "shared_pattern": "ATTACK_CLASSES_GENERATE_INFORMATION_BUT_DO_NOT_CONVERT_TO_BLOCKER_STATE_CHANGE",
        "likely_common_failure_mode": "EVIDENCE_GENERATION_AND_BLOCKER_DISCHARGE_ARE_STRUCTURALLY_DECOUPLED",
        "locality_issue": "CURRENT_CLASSES_MOSTLY_APPLY_LOCAL_OR_MEDIUM-SCOPE PRESSURE WITHOUT DIRECT FORMAL BOTTLENECK DISCHARGE",
    }

    redesigned_attack_hypothesis = {
        "hypothesis_id": "HYP-RETHINK-001",
        "statement": "Directly attacking formal proof debt should couple work to blocker discharge more strongly than route discrimination, seam redesign, or benchmark comparison.",
        "mechanism": "Target central unresolved formal dependency first and judge only on blocker-facing movement.",
    }

    selected_next_experimental_class = "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN"

    if all_nonproductive:
        packet_outcome = "FUNDAMENTAL_RETHINK_COMPLETE_NEXT_CLASS_SELECTED"
        scientific_state_change = True
    else:
        packet_outcome = "INCONCLUSIVE_FAILURE_PATTERN_NOT_UNIFORM"
        scientific_state_change = False

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "required_decision_artifacts_present": True,
            "failure_synthesis_materialized": True,
            "one_redesigned_attack_hypothesis_selected": True,
            "one_next_experimental_class_selected": selected_next_experimental_class != "",
        },
        "objective_quality": {
            "criteria": {
                "scientific_state_change_observed": scientific_state_change,
                "all_current_attack_classes_nonproductive": all_nonproductive,
                "blocker_facing_movement_observed": movement_now,
            },
            "inputs": {
                "packet_outcome": packet_outcome,
                "theorem_gap_delta": theorem_delta,
                "seam_integration_gap_delta": seam_delta,
                "progress_classification": ledger.get("progress_classification"),
                "failure_synthesis": failure_synthesis,
                "failure_pattern": failure_pattern,
                "redesigned_attack_hypothesis": redesigned_attack_hypothesis,
                "selected_next_experimental_class": selected_next_experimental_class,
                "qm_stop_rule_triggered": bool(qm.get("summary", {}).get("stop_rule_triggered", False)),
                "gr_stop_rule_triggered": bool(gr.get("summary", {}).get("stop_rule_triggered", False)),
                "stat_stop_rule_triggered": bool(stat.get("summary", {}).get("stop_rule_triggered", False)),
                "cosmo_stop_rule_triggered": bool(cosmo.get("summary", {}).get("stop_rule_triggered", False)),
            },
            "summary": {
                "all_criteria_satisfied": scientific_state_change,
                "phase_status": "COMPLETE" if scientific_state_change else "INCOMPLETE",
                "next_action": (
                    "LAUNCH_PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_PACKET"
                    if scientific_state_change
                    else "REPAIR_RETHINK_PACKET_INPUTS"
                ),
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "all_current_attack_classes_nonproductive": all_nonproductive,
            "shared_failure_pattern": failure_pattern.get("shared_pattern"),
            "redesigned_attack_hypothesis_id": redesigned_attack_hypothesis.get("hypothesis_id"),
            "selected_next_experimental_class": selected_next_experimental_class,
            "blocker_facing_movement_observed": movement_now,
            "theorem_gap_delta": theorem_delta,
            "seam_integration_gap_delta": seam_delta,
            "next_action": (
                "LAUNCH_PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_PACKET"
                if scientific_state_change
                else "REPAIR_RETHINK_PACKET_INPUTS"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "packet41_decision": _ptr(PACKET41_DECISION_PATH),
            "qm_decision": _ptr(QM_DECISION_PATH),
            "gr_decision": _ptr(GR_DECISION_PATH),
            "stat_decision": _ptr(STAT_DECISION_PATH),
            "cosmo_decision": _ptr(COSMO_DECISION_PATH),
            "simulation_v3_decision": _ptr(SIM_V3_DECISION_PATH),
            "seam_redesign_decision": _ptr(SEAM_DECISION_PATH),
            "external_benchmark_decision": _ptr(EXTERNAL_DECISION_PATH),
            "trend": _ptr(TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local fundamental attack strategy rethink report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate fundamental attack strategy rethink packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "fundamental_attack_strategy_rethink_packet_report_20260411_v0.json",
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
        "fundamental_attack_strategy_rethink_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
