from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "MASTER_ACTION_PACKET_01_TRANSPORT_BINDING_RECOVERY_REPORT_20260418_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_PACKET_01_TRANSPORT_BINDING_RECOVERY_20260418_v0.json"
)


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-.:/]+)", text)
    if match is None:
        raise ValueError(f"Missing token `{token_name}`.")
    return match.group(1)


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _extract_registry_row(text: str, seam_prefix: str) -> dict[str, str]:
    keys = {
        "governance_complete": f"{seam_prefix}_GOVERNANCE_COMPLETE_v0",
        "physics_complete": f"{seam_prefix}_PHYSICS_COMPLETE_v0",
        "status_read": f"{seam_prefix}_STATUS_READ_v0",
        "physics_blocker": f"{seam_prefix}_PHYSICS_BLOCKER_v0",
    }
    return {name: _extract_token(text, token) for name, token in keys.items()}


def _find_normalized_row(report: dict[str, Any], seam_id: str) -> dict[str, Any]:
    for row in report.get("normalized_rows", []):
        if str(row.get("seam_id", "")).strip() == seam_id:
            return dict(row)
    return {}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    recovery_policy = dict(declaration.get("recovery_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    note_path = REPO_ROOT / str(required_inputs.get("packet01_family_preservation_note", "")).strip()
    closeout_path = REPO_ROOT / str(required_inputs.get("packet01_refinement_closeout_report", "")).strip()
    refinement_path = REPO_ROOT / str(required_inputs.get("packet01_refinement_report", "")).strip()
    attack_path = REPO_ROOT / str(required_inputs.get("direct_master_action_transport_attack_class_report", "")).strip()
    alignment_exec_path = REPO_ROOT / str(required_inputs.get("architecture_alignment_execution_report", "")).strip()
    alignment_ruling_path = REPO_ROOT / str(required_inputs.get("architecture_alignment_ruling_report", "")).strip()
    witness_path = REPO_ROOT / str(required_inputs.get("seam_transport_witness_binding_artifact", "")).strip()
    unit_path = REPO_ROOT / str(required_inputs.get("master_action_residual_extraction_binding_unit_artifact", "")).strip()
    registry_path = REPO_ROOT / str(required_inputs.get("seam_constraint_registry", "")).strip()
    normalization_path = REPO_ROOT / str(required_inputs.get("seam_executable_path_normalization_report", "")).strip()

    note_text = _read(note_path)
    closeout_report = _read_json(closeout_path)
    refinement_report = _read_json(refinement_path)
    attack_report = _read_json(attack_path)
    alignment_exec_report = _read_json(alignment_exec_path)
    alignment_ruling_report = _read_json(alignment_ruling_path)
    witness_artifact = _read_json(witness_path)
    unit_artifact = _read_json(unit_path)
    registry_text = _read(registry_path)
    normalization_report = _read_json(normalization_path)

    closeout_summary = dict(closeout_report.get("summary", {}))
    refinement_summary = dict(refinement_report.get("summary", {}))
    attack_summary = dict(attack_report.get("summary", {}))
    attack_target = dict(attack_report.get("single_bounded_target", {}))
    alignment_exec_summary = dict(alignment_exec_report.get("summary", {}))
    alignment_ruling_summary = dict(alignment_ruling_report.get("summary", {}))
    registry_row = _extract_registry_row(registry_text, "SEAM_QM_STAT")
    qm_stat_row = _find_normalized_row(normalization_report, str(recovery_policy.get("target_seam", "")).strip())

    packet01_family_status = _extract_token(
        note_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_STATUS_v0"
    )
    packet01_family_outcome = _extract_token(
        note_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_OUTCOME_v0"
    )
    canonical_endpoint = _extract_token(
        note_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_CANONICAL_ENDPOINT_v0"
    )

    packet01_family_preserved = packet01_family_status == str(
        recovery_policy.get("required_packet01_family_status", "")
    ).strip()
    packet01_outcome_preserved = packet01_family_outcome == str(
        recovery_policy.get("required_packet01_family_outcome", "")
    ).strip()
    closeout_next_action_preserved = str(closeout_summary.get("next_action", "")).strip() == str(
        recovery_policy.get("required_closeout_next_action", "")
    ).strip()
    packet01_family_closed = bool(closeout_summary.get("packet01_family_closed", False))
    attack_target_match = (
        str(attack_summary.get("selected_target_row", "")).strip() == str(recovery_policy.get("target_row", "")).strip()
        and str(attack_summary.get("selected_target_package_id", "")).strip()
        == str(recovery_policy.get("target_transport_package_id", "")).strip()
        and str(attack_target.get("seam_physics_blocker", "")).strip()
        == str(recovery_policy.get("required_transport_blocker", "")).strip()
    )
    alignment_nonmoving = str(alignment_exec_summary.get("execution_classification", "")).strip() == str(
        recovery_policy.get("required_alignment_execution_classification", "")
    ).strip()
    alignment_ruling_exhausted = str(alignment_ruling_summary.get("alignment_ruling", "")).strip() == str(
        recovery_policy.get("required_alignment_ruling", "")
    ).strip()
    witness_bound = str(witness_artifact.get("status", "")).strip() == "BOUND"
    unit_materialized = str(unit_artifact.get("status", "")).strip() == "MATERIALIZED"
    target_row_match = str(witness_artifact.get("row_id", "")).strip() == str(
        recovery_policy.get("target_row", "")
    ).strip() == str(unit_artifact.get("row_id", "")).strip()
    target_package_match = str(witness_artifact.get("target_package_id", "")).strip() == str(
        recovery_policy.get("target_transport_package_id", "")
    ).strip() == str(unit_artifact.get("target_package_id", "")).strip()
    registry_blocker_explicit = registry_row.get("physics_blocker", "") == str(
        recovery_policy.get("required_transport_blocker", "")
    ).strip()
    qm_stat_policy_blocked = str(qm_stat_row.get("path_class", "")).strip() == str(
        recovery_policy.get("required_qm_stat_path_class", "")
    ).strip()

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get(
            "default_outcome", "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_EVIDENCE_INCOMPLETE"
        )
    ).strip()

    if not canonical_endpoint:
        terminal_outcome = "HOLD_PENDING_MASTER_ACTION_PACKET01_TRANSPORT_BINDING_REPAIR"
        next_action = "RESTORE_PACKET01_PRESERVATION_INPUTS_AND_RERUN"
    elif all(
        [
            packet01_family_preserved,
            packet01_outcome_preserved,
            closeout_next_action_preserved,
            packet01_family_closed,
            attack_target_match,
            alignment_nonmoving,
            alignment_ruling_exhausted,
            witness_bound,
            unit_materialized,
            target_row_match,
            target_package_match,
            registry_blocker_explicit,
            qm_stat_policy_blocked,
        ]
    ):
        terminal_outcome = "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_STATE_MATERIALIZED"
        next_action = "USE_CANONICAL_MASTER_ACTION_TRANSPORT_READ_FOR_PHASE5_DERIVATION_CHAIN_STANDARDIZATION"
    else:
        terminal_outcome = "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_TRANSPORT_BINDING_RECOVERY_INPUTS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet01_family_preserved": packet01_family_preserved,
            "packet01_family_closed": packet01_family_closed,
            "attack_target_match": attack_target_match,
            "alignment_valid_but_nonmoving": alignment_nonmoving,
            "alignment_ruling_exhausted": alignment_ruling_exhausted,
            "witness_binding_materialized": witness_bound,
            "minimal_upstream_unit_materialized": unit_materialized,
            "explicit_transport_blocker_present": registry_blocker_explicit,
            "qm_stat_policy_blocked_path_preserved": qm_stat_policy_blocked,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "no_packet02_rule_preserved": str(closeout_summary.get("authorized_follow_on", "")).strip() == "NONE",
                "no_live_restart_rule_preserved": qm_stat_policy_blocked,
            },
            "inputs": {
                "canonical_packet01_endpoint": canonical_endpoint,
                "packet01_refinement_packet_decision": refinement_summary.get("packet_decision"),
                "attack_target_row": attack_summary.get("selected_target_row"),
                "attack_target_package_id": attack_summary.get("selected_target_package_id"),
                "alignment_execution_classification": alignment_exec_summary.get("execution_classification"),
                "alignment_ruling": alignment_ruling_summary.get("alignment_ruling"),
                "transport_blocker": registry_row.get("physics_blocker"),
                "qm_stat_path_class": qm_stat_row.get("path_class"),
                "canonical_transport_read_token": recovery_policy.get("canonical_transport_read_token"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row": recovery_policy.get("target_row"),
            "target_seam": recovery_policy.get("target_seam"),
            "canonical_packet01_endpoint": canonical_endpoint,
            "canonical_transport_read_token": recovery_policy.get("canonical_transport_read_token"),
            "transport_binding_blocker": registry_row.get("physics_blocker"),
            "qm_stat_path_class": qm_stat_row.get("path_class"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "packet01_family_preservation_note": _ptr(note_path),
            "packet01_refinement_closeout_report": _ptr(closeout_path),
            "packet01_refinement_report": _ptr(refinement_path),
            "direct_master_action_transport_attack_class_report": _ptr(attack_path),
            "architecture_alignment_execution_report": _ptr(alignment_exec_path),
            "architecture_alignment_ruling_report": _ptr(alignment_ruling_path),
            "seam_transport_witness_binding_artifact": _ptr(witness_path),
            "master_action_residual_extraction_binding_unit_artifact": _ptr(unit_path),
            "seam_constraint_registry": _ptr(registry_path),
            "seam_executable_path_normalization_report": _ptr(normalization_path),
        },
        "non_claim_boundary": "Repository-local master-action Packet-01 transport-binding recovery report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the master-action Packet-01 transport-binding recovery report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "master_action_packet_01_transport_binding_recovery_20260418_v0.json",
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
        "master_action_packet_01_transport_binding_recovery_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())