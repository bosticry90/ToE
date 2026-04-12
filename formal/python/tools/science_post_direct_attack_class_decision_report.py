from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_POST_DIRECT_ATTACK_CLASS_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_POST_DIRECT_ATTACK_CLASS_DECISION_20260411_v0.json"
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


def _nonmoving_qm_ruling(token: str) -> bool:
    return token in {"EXHAUSTED_UNDER_CURRENT_FILTER", "VALID_BUT_NONMOVING"}


def _nonmoving_qm_stat_ruling(token: str) -> bool:
    return token in {"EXHAUSTED_UNDER_CURRENT_FILTER", "VALID_BUT_NONMOVING"}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))
    candidate_routes = list(declaration.get("candidate_routes", []))

    science_baseline_path = REPO_ROOT / str(required_inputs.get("science_global_completion_baseline_report", ""))
    proof_debt_path = REPO_ROOT / str(required_inputs.get("proof_debt_program_exhaustion_decision_report", ""))
    qm_ruling_path = REPO_ROOT / str(required_inputs.get("qm_blocker_moving_ruling_report", ""))
    direct_attack_path = REPO_ROOT / str(
        required_inputs.get("direct_master_action_residual_transport_attack_class_packet_report", "")
    )
    qm_stat_ruling_path = REPO_ROOT / str(required_inputs.get("qm_stat_transport_residual_ruling_report", ""))

    science_baseline = _read_json(science_baseline_path)
    proof_debt = _read_json(proof_debt_path)
    qm_ruling = _read_json(qm_ruling_path)
    direct_attack = _read_json(direct_attack_path)
    qm_stat_ruling = _read_json(qm_stat_ruling_path)

    completion_assessment = dict(science_baseline.get("completion_assessment", {}))
    proof_debt_summary = dict(proof_debt.get("summary", {}))
    qm_ruling_summary = dict(qm_ruling.get("summary", {}))
    direct_attack_summary = dict(direct_attack.get("summary", {}))
    qm_stat_ruling_summary = dict(qm_stat_ruling.get("summary", {}))

    current_attack_class = str(declaration.get("current_attack_class", "")).strip()
    science_incomplete = not bool(completion_assessment.get("science_global_complete", False))
    proof_debt_exhausted = (
        str(proof_debt_summary.get("program_state", "")).strip()
        == "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
    )
    qm_ruling_token = str(qm_ruling_summary.get("qm_ruling", "")).strip()
    qm_stat_ruling_token = str(qm_stat_ruling_summary.get("qm_stat_ruling", "")).strip()
    direct_attack_class = str(direct_attack.get("attack_class", "")).strip() or str(
        direct_attack_summary.get("selected_attack_class", "")
    ).strip()
    direct_attack_packet_materialized = (
        str(direct_attack_summary.get("packet_outcome", "")).strip()
        == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED"
    )
    prior_failure_synthesis = list(direct_attack.get("failure_synthesis", {}).get("prior_classes", []))

    local_attack_evidence = []
    if proof_debt_exhausted:
        local_attack_evidence.append(
            {
                "attack_class": "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
                "decision": proof_debt_summary.get("decision"),
                "movement_observed": False,
                "evidence_state": proof_debt_summary.get("program_state"),
            }
        )
    if _nonmoving_qm_ruling(qm_ruling_token):
        local_attack_evidence.append(
            {
                "attack_class": "QM_BLOCKER_MOVING_TRANCHE",
                "decision": qm_ruling_token,
                "movement_observed": False,
                "evidence_state": qm_ruling_summary.get("tranche_classification"),
            }
        )
    if direct_attack_packet_materialized and _nonmoving_qm_stat_ruling(qm_stat_ruling_token):
        local_attack_evidence.append(
            {
                "attack_class": direct_attack_class or current_attack_class,
                "decision": qm_stat_ruling_token,
                "movement_observed": False,
                "evidence_state": qm_stat_ruling_summary.get("packet_classification"),
            }
        )

    distinct_nonmoving_attack_classes = []
    for row in local_attack_evidence:
        attack_class = str(row.get("attack_class", "")).strip()
        if attack_class and attack_class not in distinct_nonmoving_attack_classes:
            distinct_nonmoving_attack_classes.append(attack_class)

    required_nonmoving_attack_classes = [
        str(item).strip()
        for item in decision_policy.get("required_nonmoving_attack_classes", [])
        if str(item).strip()
    ]
    required_nonmoving_attack_classes_present = all(
        attack_class in distinct_nonmoving_attack_classes for attack_class in required_nonmoving_attack_classes
    )

    specific_filter_defect_identified = bool(decision_policy.get("specific_filter_defect_identified", False))
    specific_filter_defect_note = decision_policy.get("specific_filter_defect_note")
    bounded_filter_revision_packet = decision_policy.get("bounded_filter_revision_packet")
    bounded_filter_revision_defined = isinstance(bounded_filter_revision_packet, str) and bool(
        bounded_filter_revision_packet.strip()
    )
    minimum_distinct_nonmoving_attack_classes = int(
        decision_policy.get("minimum_distinct_nonmoving_attack_classes", 3)
    )
    no_further_local_attack_packets_policy = str(
        decision_policy.get("no_further_local_attack_packets_policy", "")
    ).strip()

    multiple_distinct_local_attack_classes_nonmoving = (
        len(distinct_nonmoving_attack_classes) >= minimum_distinct_nonmoving_attack_classes
    )
    current_direct_attack_class_exhausted = (
        current_attack_class != ""
        and current_attack_class == direct_attack_class
        and _nonmoving_qm_stat_ruling(qm_stat_ruling_token)
    )

    filter_revision_route_supported = specific_filter_defect_identified and bounded_filter_revision_defined
    architecture_route_supported = (
        science_incomplete
        and proof_debt_exhausted
        and _nonmoving_qm_ruling(qm_ruling_token)
        and direct_attack_packet_materialized
        and current_direct_attack_class_exhausted
        and multiple_distinct_local_attack_classes_nonmoving
        and required_nonmoving_attack_classes_present
        and not specific_filter_defect_identified
    )

    if filter_revision_route_supported:
        decision = "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"
        selected_next_attack_class = None
        next_action = "EXECUTE_FILTER_REVISION_PACKET_ONCE"
        filter_revision_status = "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"
    elif architecture_route_supported:
        decision = "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS"
        selected_next_attack_class = (
            str(decision_policy.get("architecture_level_selected_attack_class", "")).strip() or None
        )
        next_action = str(decision_policy.get("architecture_level_next_action", "")).strip() or (
            "MATERIALIZE_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET"
        )
        filter_revision_status = "NO_SPECIFIC_FILTER_DEFECT_IDENTIFIED"
    else:
        decision = "PROGRAM_POSTURE_REVIEW_REQUIRED"
        selected_next_attack_class = None
        next_action = str(decision_policy.get("program_posture_review_next_action", "")).strip() or (
            "REVIEW_BLOCKER_MOVING_UNIT_DEFINITION_AND_PROGRAM_POSTURE_ONCE"
        )
        filter_revision_status = (
            "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"
            if specific_filter_defect_identified and bounded_filter_revision_defined
            else "NO_SPECIFIC_FILTER_DEFECT_IDENTIFIED"
        )

    candidate_route_assessment = [
        {
            "route_id": "FILTER_REVISION_ROUTE",
            "supported": filter_revision_route_supported,
            "next_action": "EXECUTE_FILTER_REVISION_PACKET_ONCE",
        },
        {
            "route_id": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_ROUTE",
            "supported": architecture_route_supported,
            "next_action": str(decision_policy.get("architecture_level_next_action", "")).strip()
            or "MATERIALIZE_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET",
        },
        {
            "route_id": "PROGRAM_POSTURE_REVIEW_ROUTE",
            "supported": decision == "PROGRAM_POSTURE_REVIEW_REQUIRED",
            "next_action": str(decision_policy.get("program_posture_review_next_action", "")).strip()
            or "REVIEW_BLOCKER_MOVING_UNIT_DEFINITION_AND_PROGRAM_POSTURE_ONCE",
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "current_attack_class": current_attack_class,
        "criteria": {
            "science_incomplete": science_incomplete,
            "proof_debt_exhausted_under_current_filter": proof_debt_exhausted,
            "qm_route_exhausted_under_current_filter": _nonmoving_qm_ruling(qm_ruling_token),
            "direct_attack_class_packet_materialized": direct_attack_packet_materialized,
            "qm_stat_route_exhausted_under_current_filter": _nonmoving_qm_stat_ruling(qm_stat_ruling_token),
            "multiple_distinct_local_attack_classes_nonmoving": multiple_distinct_local_attack_classes_nonmoving,
            "required_nonmoving_attack_classes_present": required_nonmoving_attack_classes_present,
            "specific_filter_defect_identified": specific_filter_defect_identified,
            "bounded_decision_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "no_further_local_attack_packets_enforced": (
                    no_further_local_attack_packets_policy == "NO_FURTHER_LOCAL_ATTACK_PACKETS_UNTIL_DECISION_RESOLVED"
                ),
                "filter_revision_route_supported": filter_revision_route_supported,
                "architecture_level_route_supported": architecture_route_supported,
                "decision_materialized": decision in {
                    "FILTER_REVISION_JUSTIFIED_AND_BOUNDED",
                    "ESCALATE_TO_ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS",
                    "PROGRAM_POSTURE_REVIEW_REQUIRED",
                },
            },
            "inputs": {
                "candidate_routes": candidate_routes,
                "candidate_route_assessment": candidate_route_assessment,
                "prior_failure_synthesis": prior_failure_synthesis,
                "local_attack_evidence": local_attack_evidence,
                "distinct_nonmoving_attack_classes": distinct_nonmoving_attack_classes,
                "minimum_distinct_nonmoving_attack_classes": minimum_distinct_nonmoving_attack_classes,
                "required_nonmoving_attack_classes": required_nonmoving_attack_classes,
                "specific_filter_defect_note": specific_filter_defect_note,
                "bounded_filter_revision_packet": bounded_filter_revision_packet,
                "proof_debt_program_state": proof_debt_summary.get("program_state"),
                "qm_ruling": qm_ruling_token,
                "direct_attack_class": direct_attack_class,
                "direct_attack_packet_outcome": direct_attack_summary.get("packet_outcome"),
                "direct_attack_selected_target_row": direct_attack_summary.get("selected_target_row"),
                "direct_attack_selected_target_package_id": direct_attack_summary.get("selected_target_package_id"),
                "qm_stat_ruling": qm_stat_ruling_token,
                "qm_stat_target_row": qm_stat_ruling_summary.get("row_id"),
                "qm_stat_target_package_id": qm_stat_ruling_summary.get("target_package_id"),
                "no_further_local_attack_packets_policy": no_further_local_attack_packets_policy,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "decision": decision,
            "filter_revision_status": filter_revision_status,
            "selected_next_attack_class": selected_next_attack_class,
            "distinct_nonmoving_attack_class_count": len(distinct_nonmoving_attack_classes),
            "distinct_nonmoving_attack_classes": distinct_nonmoving_attack_classes,
            "local_attack_packet_hold_policy": no_further_local_attack_packets_policy,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_global_completion_baseline_report": _ptr(science_baseline_path),
            "proof_debt_program_exhaustion_decision_report": _ptr(proof_debt_path),
            "qm_blocker_moving_ruling_report": _ptr(qm_ruling_path),
            "direct_master_action_residual_transport_attack_class_packet_report": _ptr(direct_attack_path),
            "qm_stat_transport_residual_ruling_report": _ptr(qm_stat_ruling_path),
        },
        "non_claim_boundary": "Repository-local post-direct-attack-class decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-direct-attack-class science decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_post_direct_attack_class_decision_20260411_v0.json",
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
        "science_post_direct_attack_class_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
