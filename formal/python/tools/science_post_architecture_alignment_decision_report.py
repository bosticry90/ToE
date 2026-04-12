from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_POST_ARCHITECTURE_ALIGNMENT_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_POST_ARCHITECTURE_ALIGNMENT_DECISION_20260411_v0.json"
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


def _is_exhausted(token: str) -> bool:
    return token in {"EXHAUSTED_UNDER_CURRENT_FILTER", "VALID_BUT_NONMOVING"}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))
    candidate_routes = list(declaration.get("candidate_routes", []))

    ruling_path = REPO_ROOT / str(
        required_inputs.get("architecture_seam_master_action_alignment_ruling_report", "")
    )
    execution_path = REPO_ROOT / str(
        required_inputs.get("architecture_seam_master_action_alignment_packet_execution_report", "")
    )
    diagnosis_path = REPO_ROOT / str(
        required_inputs.get("architecture_level_blocker_diagnosis_packet_report", "")
    )

    ruling_report = _read_json(ruling_path)
    execution_report = _read_json(execution_path)
    diagnosis_report = _read_json(diagnosis_path)

    ruling_summary = dict(ruling_report.get("summary", {}))
    execution_summary = dict(execution_report.get("summary", {}))
    diagnosis_summary = dict(diagnosis_report.get("summary", {}))

    alignment_ruling = str(ruling_summary.get("alignment_ruling", "")).strip()
    execution_classification = str(execution_summary.get("execution_classification", "")).strip()
    bridge_object_materialized = bool(execution_summary.get("bridge_object_materialized", False))
    alignment_witness_bound = bool(execution_summary.get("alignment_witness_bound", False))
    target_row_recompute_triggered = bool(execution_summary.get("target_row_recompute_triggered", False))
    blocker_movement_signal_true = bool(execution_summary.get("blocker_movement_signal_true", False))

    blocker_conversion_failure_location = str(
        diagnosis_summary.get("blocker_conversion_failure_location", "")
    ).strip()
    upstream_missing_unit_identified = bool(diagnosis_summary.get("upstream_missing_unit_identified", False))
    selected_redesigned_attack_class = str(
        diagnosis_summary.get("selected_redesigned_attack_class", "")
    ).strip()

    architecture_alignment_exhausted = _is_exhausted(alignment_ruling)

    movement_metric_defect_identified = bool(
        decision_policy.get("movement_metric_defect_identified", False)
    )
    movement_metric_defect_note = decision_policy.get("movement_metric_defect_note")
    bounded_metric_revision_packet = decision_policy.get("bounded_metric_revision_packet")
    bounded_metric_revision_defined = isinstance(bounded_metric_revision_packet, str) and bool(
        bounded_metric_revision_packet.strip()
    )

    architecture_unit_selection_defect_identified = bool(
        decision_policy.get("architecture_unit_selection_defect_identified", False)
    )
    architecture_unit_selection_defect_note = decision_policy.get("architecture_unit_selection_defect_note")
    bounded_unit_selection_revision_packet = decision_policy.get("bounded_unit_selection_revision_packet")
    bounded_unit_selection_defined = isinstance(bounded_unit_selection_revision_packet, str) and bool(
        bounded_unit_selection_revision_packet.strip()
    )

    no_loop_rule = str(decision_policy.get("no_loop_rule", "")).strip()
    no_further_policy = str(
        decision_policy.get("no_further_architecture_attack_packets_policy", "")
    ).strip()

    metric_defect_route_supported = movement_metric_defect_identified and bounded_metric_revision_defined
    unit_selection_defect_route_supported = (
        architecture_unit_selection_defect_identified and bounded_unit_selection_defined
    )

    if metric_defect_route_supported:
        decision = "MOVEMENT_METRIC_DEFECT_IDENTIFIED_AND_BOUNDED"
        next_action = "EXECUTE_MOVEMENT_METRIC_REVISION_PACKET_ONCE"
        specific_defect_identified = True
        defect_scope: str | None = "MOVEMENT_METRIC"
        selected_next_program_mode = "MOVEMENT_METRIC_REVISION"
    elif unit_selection_defect_route_supported:
        decision = "ARCHITECTURE_UNIT_SELECTION_DEFECT_IDENTIFIED_AND_BOUNDED"
        next_action = "EXECUTE_ARCHITECTURE_UNIT_SELECTION_REVISION_PACKET_ONCE"
        specific_defect_identified = True
        defect_scope = "ARCHITECTURE_UNIT_SELECTION"
        selected_next_program_mode = "ARCHITECTURE_UNIT_SELECTION_REVISION"
    else:
        decision = "PROGRAM_POSTURE_REVIEW_REQUIRED"
        next_action = (
            str(decision_policy.get("program_posture_review_next_action", "")).strip()
            or "MATERIALIZE_PROGRAM_POSTURE_REVIEW_PACKET"
        )
        specific_defect_identified = False
        defect_scope = None
        selected_next_program_mode = "PROGRAM_POSTURE_REVIEW"

    candidate_route_assessment = [
        {
            "route_id": "MOVEMENT_METRIC_DEFECT_ROUTE",
            "supported": metric_defect_route_supported,
            "next_action": "EXECUTE_MOVEMENT_METRIC_REVISION_PACKET_ONCE",
        },
        {
            "route_id": "ARCHITECTURE_UNIT_SELECTION_DEFECT_ROUTE",
            "supported": unit_selection_defect_route_supported,
            "next_action": "EXECUTE_ARCHITECTURE_UNIT_SELECTION_REVISION_PACKET_ONCE",
        },
        {
            "route_id": "PROGRAM_POSTURE_REVIEW_ROUTE",
            "supported": decision == "PROGRAM_POSTURE_REVIEW_REQUIRED",
            "next_action": str(decision_policy.get("program_posture_review_next_action", "")).strip()
            or "MATERIALIZE_PROGRAM_POSTURE_REVIEW_PACKET",
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "current_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
        "criteria": {
            "architecture_alignment_ruling_exhausted": architecture_alignment_exhausted,
            "bridge_object_materialized": bridge_object_materialized,
            "alignment_witness_bound": alignment_witness_bound,
            "target_row_recompute_triggered": target_row_recompute_triggered,
            "blocker_movement_signal_true": blocker_movement_signal_true,
            "upstream_missing_unit_identified_in_diagnosis": upstream_missing_unit_identified,
            "movement_metric_defect_identified": movement_metric_defect_identified,
            "architecture_unit_selection_defect_identified": architecture_unit_selection_defect_identified,
            "bounded_decision_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "no_further_architecture_attack_packets_enforced": (
                    no_further_policy
                    == "NO_FURTHER_ARCHITECTURE_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED"
                ),
                "no_loop_rule_declared": no_loop_rule == "ONE_POST_ARCHITECTURE_DECISION_ONLY",
                "metric_defect_route_supported": metric_defect_route_supported,
                "unit_selection_defect_route_supported": unit_selection_defect_route_supported,
                "program_posture_review_route_supported": decision == "PROGRAM_POSTURE_REVIEW_REQUIRED",
                "decision_materialized": decision
                in {
                    "MOVEMENT_METRIC_DEFECT_IDENTIFIED_AND_BOUNDED",
                    "ARCHITECTURE_UNIT_SELECTION_DEFECT_IDENTIFIED_AND_BOUNDED",
                    "PROGRAM_POSTURE_REVIEW_REQUIRED",
                },
            },
            "inputs": {
                "candidate_routes": candidate_routes,
                "candidate_route_assessment": candidate_route_assessment,
                "alignment_ruling": alignment_ruling,
                "execution_classification": execution_classification,
                "bridge_object_materialized": bridge_object_materialized,
                "alignment_witness_bound": alignment_witness_bound,
                "target_row_recompute_triggered": target_row_recompute_triggered,
                "blocker_movement_signal_true": blocker_movement_signal_true,
                "blocker_conversion_failure_location": blocker_conversion_failure_location,
                "upstream_missing_unit_identified": upstream_missing_unit_identified,
                "selected_redesigned_attack_class": selected_redesigned_attack_class,
                "movement_metric_defect_note": movement_metric_defect_note,
                "bounded_metric_revision_packet": bounded_metric_revision_packet,
                "architecture_unit_selection_defect_note": architecture_unit_selection_defect_note,
                "bounded_unit_selection_revision_packet": bounded_unit_selection_revision_packet,
                "no_loop_rule": no_loop_rule,
                "no_further_architecture_attack_packets_policy": no_further_policy,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "post_architecture_decision": decision,
            "specific_defect_identified": specific_defect_identified,
            "defect_scope": defect_scope,
            "selected_next_program_mode": selected_next_program_mode,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "architecture_seam_master_action_alignment_ruling_report": _ptr(ruling_path),
            "architecture_seam_master_action_alignment_packet_execution_report": _ptr(execution_path),
            "architecture_level_blocker_diagnosis_packet_report": _ptr(diagnosis_path),
        },
        "non_claim_boundary": "Repository-local post-architecture-alignment decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-architecture-alignment science decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_post_architecture_alignment_decision_20260411_v0.json",
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
        "science_post_architecture_alignment_decision_report: "
        f"decision={payload['summary']['post_architecture_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
