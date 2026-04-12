from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_20260411_v0.json"
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


def _is_nonmoving(token: str) -> bool:
    return token in {"EXHAUSTED_UNDER_CURRENT_FILTER", "VALID_BUT_NONMOVING"}


def _select_failure_location(
    *,
    direct_target_row: str,
    qm_stat_target_row: str,
    direct_packet_outcome: str,
    qm_stat_ruling: str,
    fallback: str,
) -> str:
    if not direct_target_row:
        return "TARGET_SELECTION"
    if qm_stat_target_row and qm_stat_target_row != direct_target_row:
        return "ROW_SEAM_COUPLING"
    if direct_packet_outcome == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED" and _is_nonmoving(qm_stat_ruling):
        return "MASTER_ACTION_RESIDUAL_EXTRACTION"
    return fallback


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    diagnosis_policy = dict(declaration.get("diagnosis_policy", {}))

    science_post_path = REPO_ROOT / str(required_inputs.get("science_post_direct_attack_class_decision_report", ""))
    proof_debt_path = REPO_ROOT / str(required_inputs.get("proof_debt_program_exhaustion_decision_report", ""))
    qm_path = REPO_ROOT / str(required_inputs.get("qm_blocker_moving_ruling_report", ""))
    qm_stat_path = REPO_ROOT / str(required_inputs.get("qm_stat_transport_residual_ruling_report", ""))
    direct_packet_path = REPO_ROOT / str(
        required_inputs.get("direct_master_action_residual_transport_attack_class_packet_report", "")
    )

    science_post = _read_json(science_post_path)
    proof_debt = _read_json(proof_debt_path)
    qm_ruling = _read_json(qm_path)
    qm_stat = _read_json(qm_stat_path)
    direct_packet = _read_json(direct_packet_path)

    science_summary = dict(science_post.get("summary", {}))
    proof_debt_summary = dict(proof_debt.get("summary", {}))
    qm_summary = dict(qm_ruling.get("summary", {}))
    qm_stat_summary = dict(qm_stat.get("summary", {}))
    direct_summary = dict(direct_packet.get("summary", {}))

    decision = str(science_summary.get("decision", "")).strip()
    selected_attack_class = str(science_summary.get("selected_next_attack_class", "")).strip()
    hold_policy = str(science_summary.get("local_attack_packet_hold_policy", "")).strip()
    filter_revision_status = str(science_summary.get("filter_revision_status", "")).strip()

    proof_debt_exhausted = (
        str(proof_debt_summary.get("program_state", "")).strip()
        == "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
    )
    qm_nonmoving = _is_nonmoving(str(qm_summary.get("qm_ruling", "")).strip())
    qm_stat_nonmoving = _is_nonmoving(str(qm_stat_summary.get("qm_stat_ruling", "")).strip())

    direct_packet_outcome = str(direct_summary.get("packet_outcome", "")).strip()
    direct_target_row = str(direct_summary.get("selected_target_row", "")).strip()
    qm_stat_target_row = str(qm_stat_summary.get("row_id", "")).strip()

    required_classes = [
        str(item).strip()
        for item in diagnosis_policy.get("required_prior_nonmoving_attack_classes", [])
        if str(item).strip()
    ]
    observed_classes = [
        "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN" if proof_debt_exhausted else "",
        "QM_BLOCKER_MOVING_TRANCHE" if qm_nonmoving else "",
        "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS" if qm_stat_nonmoving else "",
    ]
    observed_classes = [item for item in observed_classes if item]
    required_classes_present = all(item in observed_classes for item in required_classes)

    decision_is_architecture = decision == "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
    hold_policy_enforced = (
        hold_policy
        == str(diagnosis_policy.get("local_attack_hold_policy", "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED"))
    )
    movement_filter_defect_identified = filter_revision_status == "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"

    blocker_conversion_failure_location = _select_failure_location(
        direct_target_row=direct_target_row,
        qm_stat_target_row=qm_stat_target_row,
        direct_packet_outcome=direct_packet_outcome,
        qm_stat_ruling=str(qm_stat_summary.get("qm_stat_ruling", "")).strip(),
        fallback=str(
            diagnosis_policy.get("default_blocker_conversion_failure_location", "MASTER_ACTION_RESIDUAL_EXTRACTION")
        ),
    )

    upstream_missing_unit = str(
        diagnosis_policy.get("default_upstream_missing_unit", "ARCHITECTURE_LEVEL_BLOCKER_CONVERSION_UNIT")
    ).strip()
    upstream_missing_unit_identified = (
        decision_is_architecture
        and required_classes_present
        and hold_policy_enforced
        and not movement_filter_defect_identified
    )

    selected_redesigned_attack_class = str(
        diagnosis_policy.get(
            "default_selected_redesigned_attack_class",
            "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
        )
    ).strip()

    if upstream_missing_unit_identified and blocker_conversion_failure_location:
        packet_outcome = "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE"
        next_action = str(
            diagnosis_policy.get(
                "next_action_if_complete",
                "MATERIALIZE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET",
            )
        ).strip()
    else:
        packet_outcome = "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_INCOMPLETE"
        next_action = "REVIEW_ARCHITECTURE_LEVEL_DIAGNOSIS_PRECONDITIONS_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "science_post_direct_decision_is_architecture_level_diagnosis": decision_is_architecture,
            "required_prior_nonmoving_attack_classes_present": required_classes_present,
            "local_attack_hold_policy_enforced": hold_policy_enforced,
            "proof_debt_exhausted_under_current_filter": proof_debt_exhausted,
            "qm_route_nonmoving_under_current_filter": qm_nonmoving,
            "direct_master_action_qm_stat_route_nonmoving_under_current_filter": qm_stat_nonmoving,
            "bounded_decision_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "diagnosis_scoped_to_architecture_level": decision_is_architecture,
                "movement_filter_vs_architecture_decided_explicitly": True,
                "single_redesigned_attack_class_selected": bool(selected_redesigned_attack_class),
                "single_next_action_materialized": bool(next_action),
            },
            "inputs": {
                "diagnosis_questions": declaration.get("diagnosis_questions", []),
                "science_post_direct_decision": decision,
                "science_selected_next_attack_class": selected_attack_class,
                "science_next_action": science_summary.get("next_action"),
                "science_hold_policy": hold_policy,
                "science_filter_revision_status": filter_revision_status,
                "proof_debt_program_state": proof_debt_summary.get("program_state"),
                "qm_ruling": qm_summary.get("qm_ruling"),
                "qm_stat_ruling": qm_stat_summary.get("qm_stat_ruling"),
                "direct_packet_outcome": direct_packet_outcome,
                "direct_selected_target_row": direct_target_row,
                "qm_stat_target_row": qm_stat_target_row,
                "required_prior_nonmoving_attack_classes": required_classes,
                "observed_nonmoving_attack_classes": observed_classes,
            },
            "summary": {
                "all_criteria_satisfied": packet_outcome == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE",
                "phase_status": "COMPLETE"
                if packet_outcome == "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE"
                else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "diagnosis_answers": {
            "blocker_conversion_failure_location": blocker_conversion_failure_location,
            "smallest_upstream_unit": upstream_missing_unit,
            "movement_filter_vs_architecture": (
                "FILTER_DEFECT_IDENTIFIED"
                if movement_filter_defect_identified
                else "ARCHITECTURE_UNDERPOWERED"
            ),
            "selected_redesigned_attack_class": selected_redesigned_attack_class,
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "blocker_conversion_failure_location": blocker_conversion_failure_location,
            "movement_filter_defect_identified": movement_filter_defect_identified,
            "upstream_missing_unit_identified": upstream_missing_unit_identified,
            "selected_redesigned_attack_class": selected_redesigned_attack_class,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_post_direct_attack_class_decision_report": _ptr(science_post_path),
            "proof_debt_program_exhaustion_decision_report": _ptr(proof_debt_path),
            "qm_blocker_moving_ruling_report": _ptr(qm_path),
            "qm_stat_transport_residual_ruling_report": _ptr(qm_stat_path),
            "direct_master_action_residual_transport_attack_class_packet_report": _ptr(direct_packet_path),
        },
        "non_claim_boundary": "Repository-local architecture-level blocker diagnosis packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate architecture-level blocker diagnosis packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "architecture_level_blocker_diagnosis_packet_20260411_v0.json",
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
        "architecture_level_blocker_diagnosis_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
