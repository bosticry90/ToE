from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET_20260411_v0.json"
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


def _alignment_failure_mode(
    *,
    diagnosis_failure_location: str,
    direct_seam_blocker: str,
    target_row_match: bool,
) -> str:
    if not target_row_match:
        return "ROW_SEAM_TARGET_ALIGNMENT_MISMATCH"
    if diagnosis_failure_location == "MASTER_ACTION_RESIDUAL_EXTRACTION":
        if direct_seam_blocker == "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE":
            return "MASTER_ACTION_RESIDUAL_INTERFACE_NOT_BOUND_TO_SEAM_TRANSPORT_WITNESS"
        return "MASTER_ACTION_RESIDUAL_EXTRACTION_INTERFACE_UNSPECIFIED"
    return "ARCHITECTURE_ALIGNMENT_FAILURE_UNSPECIFIED"


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    alignment_scope = dict(declaration.get("bounded_alignment_scope", {}))
    alignment_policy = dict(declaration.get("alignment_policy", {}))
    measurement = dict(declaration.get("success_failure_measurement", {}))

    diagnosis_path = REPO_ROOT / str(required_inputs.get("architecture_level_blocker_diagnosis_packet_report", ""))
    science_post_path = REPO_ROOT / str(required_inputs.get("science_post_direct_attack_class_decision_report", ""))
    direct_packet_path = REPO_ROOT / str(
        required_inputs.get("direct_master_action_residual_transport_attack_class_packet_report", "")
    )
    qm_stat_ruling_path = REPO_ROOT / str(required_inputs.get("qm_stat_transport_residual_ruling_report", ""))

    diagnosis = _read_json(diagnosis_path)
    science_post = _read_json(science_post_path)
    direct_packet = _read_json(direct_packet_path)
    qm_stat_ruling = _read_json(qm_stat_ruling_path)

    diagnosis_summary = dict(diagnosis.get("summary", {}))
    science_summary = dict(science_post.get("summary", {}))
    direct_summary = dict(direct_packet.get("summary", {}))
    direct_target = dict(direct_packet.get("single_bounded_target", {}))
    qm_stat_summary = dict(qm_stat_ruling.get("summary", {}))

    diagnosis_packet_outcome = str(diagnosis_summary.get("packet_outcome", "")).strip()
    diagnosis_failure_location = str(diagnosis_summary.get("blocker_conversion_failure_location", "")).strip()
    diagnosis_selected_attack_class = str(diagnosis_summary.get("selected_redesigned_attack_class", "")).strip()
    diagnosis_upstream_missing_unit_identified = bool(diagnosis_summary.get("upstream_missing_unit_identified", False))

    required_diagnosis_outcome = str(alignment_policy.get("required_diagnosis_outcome", "")).strip()
    required_failure_location = str(alignment_policy.get("required_failure_location", "")).strip()
    required_redesigned_attack_class = str(alignment_policy.get("required_redesigned_attack_class", "")).strip()
    required_hold_policy = str(alignment_policy.get("required_hold_policy", "")).strip()

    hold_policy = str(science_summary.get("local_attack_packet_hold_policy", "")).strip()

    target_row_id = str(alignment_scope.get("target_row_id", "")).strip()
    target_package_id = str(alignment_scope.get("target_package_id", "")).strip()

    direct_target_row = str(direct_summary.get("selected_target_row", "")).strip()
    direct_target_package_id = str(direct_summary.get("selected_target_package_id", "")).strip()
    qm_stat_target_row = str(qm_stat_summary.get("row_id", "")).strip()

    target_row_match = target_row_id != "" and direct_target_row == target_row_id and qm_stat_target_row == target_row_id
    target_package_match = target_package_id != "" and direct_target_package_id == target_package_id

    direct_seam_blocker = str(direct_target.get("seam_physics_blocker", "")).strip()
    alignment_failure_mode = _alignment_failure_mode(
        diagnosis_failure_location=diagnosis_failure_location,
        direct_seam_blocker=direct_seam_blocker,
        target_row_match=target_row_match,
    )

    missing_bridge_object = str(
        alignment_policy.get("default_missing_bridge_object", "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0")
    ).strip()
    minimal_upstream_unit_to_materialize = str(
        alignment_policy.get("default_minimal_upstream_unit", "MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0")
    ).strip()

    one_bounded_execution_target = {
        "alignment_obligation": alignment_scope.get("single_alignment_obligation"),
        "residual_extraction_interface": alignment_scope.get("single_residual_extraction_interface"),
        "transport_witness": alignment_scope.get("single_transport_witness"),
        "row_id": target_row_id,
        "target_package_id": target_package_id,
        "selection_reason": alignment_scope.get("selection_reason"),
    }

    preconditions_satisfied = (
        diagnosis_packet_outcome == required_diagnosis_outcome
        and diagnosis_failure_location == required_failure_location
        and diagnosis_selected_attack_class == required_redesigned_attack_class
        and diagnosis_upstream_missing_unit_identified
        and hold_policy == required_hold_policy
        and target_row_match
        and target_package_match
    )

    if preconditions_satisfied:
        packet_outcome = "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED"
        next_action = str(
            alignment_policy.get("next_action_if_complete", "EXECUTE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_ONCE")
        ).strip()
    else:
        packet_outcome = "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_INCOMPLETE"
        next_action = "REVIEW_ARCHITECTURE_ALIGNMENT_PACKET_PRECONDITIONS_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "architecture_diagnosis_packet_complete": diagnosis_packet_outcome == required_diagnosis_outcome,
            "failure_location_matches_required": diagnosis_failure_location == required_failure_location,
            "selected_redesigned_attack_class_matches_required": (
                diagnosis_selected_attack_class == required_redesigned_attack_class
            ),
            "upstream_missing_unit_identified": diagnosis_upstream_missing_unit_identified,
            "local_attack_hold_policy_enforced": hold_policy == required_hold_policy,
            "bounded_row_target_alignment_satisfied": target_row_match,
            "bounded_package_target_alignment_satisfied": target_package_match,
            "bounded_decision_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "single_alignment_obligation_selected": bool(alignment_scope.get("single_alignment_obligation")),
                "single_residual_interface_selected": bool(alignment_scope.get("single_residual_extraction_interface")),
                "single_transport_witness_selected": bool(alignment_scope.get("single_transport_witness")),
                "single_next_action_materialized": bool(next_action),
            },
            "inputs": {
                "diagnosis_packet_outcome": diagnosis_packet_outcome,
                "diagnosis_failure_location": diagnosis_failure_location,
                "diagnosis_selected_redesigned_attack_class": diagnosis_selected_attack_class,
                "diagnosis_next_action": diagnosis_summary.get("next_action"),
                "science_decision": science_summary.get("decision"),
                "science_hold_policy": hold_policy,
                "direct_packet_outcome": direct_summary.get("packet_outcome"),
                "direct_target_row": direct_target_row,
                "qm_stat_target_row": qm_stat_target_row,
                "direct_target_package_id": direct_target_package_id,
                "direct_seam_physics_blocker": direct_seam_blocker,
                "alignment_failure_mode": alignment_failure_mode,
                "missing_bridge_object": missing_bridge_object,
                "minimal_upstream_unit_to_materialize": minimal_upstream_unit_to_materialize,
                "one_bounded_execution_target": one_bounded_execution_target,
            },
            "summary": {
                "all_criteria_satisfied": packet_outcome == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED",
                "phase_status": "COMPLETE"
                if packet_outcome == "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_MATERIALIZED"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "alignment_failure_mode": alignment_failure_mode,
            "missing_bridge_object": missing_bridge_object,
            "minimal_upstream_unit_to_materialize": minimal_upstream_unit_to_materialize,
            "one_bounded_execution_target": one_bounded_execution_target,
            "success_rule": measurement.get("success_rule"),
            "no-loop failure rule": measurement.get("no_loop_failure_rule"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "architecture_level_blocker_diagnosis_packet_report": _ptr(diagnosis_path),
            "science_post_direct_attack_class_decision_report": _ptr(science_post_path),
            "direct_master_action_residual_transport_attack_class_packet_report": _ptr(direct_packet_path),
            "qm_stat_transport_residual_ruling_report": _ptr(qm_stat_ruling_path),
        },
        "non_claim_boundary": "Repository-local architecture seam/master-action alignment attack-class packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate architecture seam/master-action alignment attack-class packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json",
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
        "architecture_seam_master_action_alignment_attack_class_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
