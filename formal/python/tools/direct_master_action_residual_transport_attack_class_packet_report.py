from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET_20260411_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _extract_registry_value(text: str, token: str) -> str | None:
    pattern = re.compile(rf"{re.escape(token)}:\s*([A-Z0-9_\-]+)")
    match = pattern.search(text)
    if not match:
        return None
    return match.group(1)


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    failure_synthesis_scope = dict(declaration.get("failure_synthesis_scope", {}))
    target = dict(declaration.get("single_bounded_target", {}))
    measurement = dict(declaration.get("success_failure_measurement", {}))
    hypothesis = dict(declaration.get("new_attack_hypothesis", {}))

    science_selection_path = REPO_ROOT / str(required_inputs.get("science_next_attack_class_selection_report", ""))
    proof_debt_decision_path = REPO_ROOT / str(required_inputs.get("proof_debt_program_exhaustion_decision_report", ""))
    qm_ruling_path = REPO_ROOT / str(required_inputs.get("qm_blocker_moving_ruling_report", ""))
    seam_redesign_path = REPO_ROOT / str(required_inputs.get("broader_seam_package_redesign_decision_report", ""))
    seam_registry_path = REPO_ROOT / str(required_inputs.get("seam_registry_surface", ""))
    closure_map_path = REPO_ROOT / str(required_inputs.get("closure_map_report", ""))
    target_artifact_path = REPO_ROOT / str(required_inputs.get("current_target_artifact", ""))

    science_selection = _read_json(science_selection_path)
    proof_debt_decision = _read_json(proof_debt_decision_path)
    qm_ruling = _read_json(qm_ruling_path)
    seam_redesign = _read_json(seam_redesign_path)
    seam_registry_text = _read_text(seam_registry_path)
    closure_map = _read_json(closure_map_path)
    target_artifact = _read_json(target_artifact_path)

    target_row_id = str(target.get("row_id", "")).strip()
    closure_mapping = next(
        (row for row in closure_map.get("mappings", []) if str(row.get("row_id", "")).strip() == target_row_id),
        None,
    )
    target_mapping_present = closure_mapping is not None

    seam_status = _extract_registry_value(seam_registry_text, "SEAM_QM_STAT_STATUS_READ_v0")
    seam_physics_blocker = _extract_registry_value(seam_registry_text, "SEAM_QM_STAT_PHYSICS_BLOCKER_v0")
    seam_governance_complete = _extract_registry_value(seam_registry_text, "SEAM_QM_STAT_GOVERNANCE_COMPLETE_v0")
    seam_physics_complete = _extract_registry_value(seam_registry_text, "SEAM_QM_STAT_PHYSICS_COMPLETE_v0")

    science_selection_summary = dict(science_selection.get("summary", {}))
    proof_debt_summary = dict(proof_debt_decision.get("summary", {}))
    qm_ruling_summary = dict(qm_ruling.get("summary", {}))
    seam_redesign_summary = dict(seam_redesign.get("summary", {}))

    target_artifact_status = str(target_artifact.get("status", "")).strip()
    target_artifact_adjudication = str(target_artifact.get("adjudication", {}).get("value", "")).strip()

    prior_failure_synthesis = [
        {
            "attack_class": "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
            "decision": proof_debt_summary.get("decision"),
            "program_state": proof_debt_summary.get("program_state"),
            "movement_observed": False,
            "implication": "Local proof-debt surfaces were executable and valid but did not move blocker-facing state.",
        },
        {
            "attack_class": "QM_BLOCKER_MOVING_TRANCHE",
            "decision": qm_ruling_summary.get("qm_ruling"),
            "program_state": qm_ruling_summary.get("tranche_classification"),
            "movement_observed": False,
            "implication": "The bounded QM blocker-moving slice was evaluated directly and still failed to move theorem-gap, row-success, or blocker-token state.",
        },
        {
            "attack_class": "BROADER_SEAM_PACKAGE_REDESIGN",
            "decision": seam_redesign_summary.get("decision"),
            "program_state": seam_redesign_summary.get("packet_outcome"),
            "movement_observed": bool(seam_redesign_summary.get("blocker_facing_movement_observed", False)),
            "implication": "Broad seam redesign produced no blocker movement, so the next seam attempt must be narrower and transport/residual-directed.",
        },
    ]

    selected_attack_class = str(science_selection_summary.get("selected_next_attack_class", "")).strip()
    selected_attack_class_matches = (
        selected_attack_class == str(declaration.get("attack_class", "")).strip()
    )
    proof_debt_exhausted = (
        str(proof_debt_summary.get("program_state", "")).strip()
        == "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
    )
    qm_exhausted = str(qm_ruling_summary.get("qm_ruling", "")).strip() == "EXHAUSTED_UNDER_CURRENT_FILTER"
    seam_redesign_nonproductive = (
        str(seam_redesign_summary.get("decision", "")).strip()
        == "BROADER_SEAM_REDESIGN_NONPRODUCTIVE_IN_BOUNDED_TRANCHE"
    )

    blocker_alignment = (
        seam_physics_blocker == "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"
        and str(target.get("target_kind", "")).strip() == "UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"
    )

    if (
        selected_attack_class_matches
        and proof_debt_exhausted
        and qm_exhausted
        and seam_redesign_nonproductive
        and target_mapping_present
        and blocker_alignment
    ):
        packet_outcome = "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED"
        next_action = "EXECUTE_DIRECT_MASTER_ACTION_QM_STAT_TRANSPORT_RESIDUAL_PACKET_ONCE"
    else:
        packet_outcome = "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_INCOMPLETE"
        next_action = "REVIEW_SELECTION_OR_TARGET_ALIGNMENT_ONCE"

    shared_failure_implication = (
        "The repo's recent failures point to a leverage mismatch: local validity and broad redesign work are not moving state because the missing blocker-facing unit is a direct transport/residual package."
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "science_selector_requests_packet_materialization": (
                science_selection_summary.get("decision") == "ESCALATE_TO_DECLARED_NEXT_ATTACK_CLASS"
                and science_selection_summary.get("next_action")
                == "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET"
            ),
            "selected_attack_class_matches_packet": selected_attack_class_matches,
            "proof_debt_exhausted": proof_debt_exhausted,
            "qm_route_exhausted": qm_exhausted,
            "broader_seam_redesign_nonproductive": seam_redesign_nonproductive,
            "target_row_present_in_closure_map": target_mapping_present,
            "qm_stat_blocker_matches_transport_residual_gap": blocker_alignment,
            "prior_failure_synthesis_materialized": len(prior_failure_synthesis) == 3,
        },
        "objective_quality": {
            "criteria": {
                "single_bounded_target_selected": target_row_id != "",
                "broad_reunification_narrative_avoided": target_mapping_present,
                "proof_debt_not_reopened_in_parallel": (
                    science_selection_summary.get("proof_debt_parallel_reopen_allowed") is False
                ),
                "measurement_contract_fail_closed": (
                    str(measurement.get("failure_rule", "")).strip() == "ALL_MOVEMENT_SIGNALS_FALSE"
                    and str(measurement.get("no_loop_rule", "")).strip() == "ONE_BOUNDED_PACKET_ONLY"
                ),
            },
            "inputs": {
                "failure_synthesis_scope": failure_synthesis_scope,
                "prior_failure_synthesis": prior_failure_synthesis,
                "shared_failure_implication": shared_failure_implication,
                "new_attack_hypothesis": hypothesis,
                "single_bounded_target": {
                    "row_id": target_row_id,
                    "blocker_class": target.get("blocker_class"),
                    "owning_lane": target.get("owning_lane"),
                    "target_kind": target.get("target_kind"),
                    "target_package_id": target.get("target_package_id"),
                    "selection_reason": target.get("selection_reason"),
                    "closure_map_entry": closure_mapping,
                    "seam_status": seam_status,
                    "seam_governance_complete": seam_governance_complete,
                    "seam_physics_complete": seam_physics_complete,
                    "seam_physics_blocker": seam_physics_blocker,
                    "current_target_artifact_status": target_artifact_status,
                    "current_target_artifact_adjudication": target_artifact_adjudication,
                },
                "success_failure_measurement": measurement,
            },
            "summary": {
                "all_criteria_satisfied": packet_outcome == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED",
                "phase_status": (
                    "COMPLETE"
                    if packet_outcome == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED"
                    else "INCOMPLETE"
                ),
                "next_action": next_action,
            },
        },
        "failure_synthesis": {
            "prior_classes": prior_failure_synthesis,
            "shared_implication": shared_failure_implication,
        },
        "new_attack_hypothesis": hypothesis,
        "single_bounded_target": {
            "row_id": target_row_id,
            "blocker_class": target.get("blocker_class"),
            "owning_lane": target.get("owning_lane"),
            "target_kind": target.get("target_kind"),
            "target_package_id": target.get("target_package_id"),
            "required_closure_artifact": target.get("required_closure_artifact"),
            "required_evidence_surface": target.get("required_evidence_surface"),
            "selection_reason": target.get("selection_reason"),
            "seam_status": seam_status,
            "seam_physics_blocker": seam_physics_blocker,
            "current_target_artifact_status": target_artifact_status,
            "current_target_artifact_adjudication": target_artifact_adjudication,
        },
        "success_failure_measurement": {
            "success_rule": measurement.get("success_rule"),
            "failure_rule": measurement.get("failure_rule"),
            "no_loop_rule": measurement.get("no_loop_rule"),
            "movement_signals": measurement.get("movement_signals", []),
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "selected_target_row": target_row_id,
            "selected_target_package_id": target.get("target_package_id"),
            "selected_attack_class": selected_attack_class,
            "shared_failure_implication": shared_failure_implication,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_next_attack_class_selection_report": _ptr(science_selection_path),
            "proof_debt_program_exhaustion_decision_report": _ptr(proof_debt_decision_path),
            "qm_blocker_moving_ruling_report": _ptr(qm_ruling_path),
            "broader_seam_package_redesign_decision_report": _ptr(seam_redesign_path),
            "seam_registry_surface": _ptr(seam_registry_path),
            "closure_map_report": _ptr(closure_map_path),
            "current_target_artifact": _ptr(target_artifact_path),
        },
        "non_claim_boundary": "Repository-local direct master-action residual/transport attack-class packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate direct master-action residual/transport attack-class packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
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
        "direct_master_action_residual_transport_attack_class_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
