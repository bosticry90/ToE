from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_RESTART_TRIGGER_CONTRACT_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json"
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


def _maybe_text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("restart_trigger_contract", {}))
    outcome_contract = dict(declaration.get("restart_trigger_outcome_contract", {}))

    post_z_path = REPO_ROOT / str(
        required_inputs.get("science_post_phase_z_frontier_decision_report", "")
    ).strip()
    phase_z_path = REPO_ROOT / str(
        required_inputs.get("science_phase_z_stronger_candidate_class_discovery_report", "")
    ).strip()
    summary_doc_path = REPO_ROOT / str(
        required_inputs.get("science_frontier_stop_state_summary_doc", "")
    ).strip()
    policy_trigger_path = REPO_ROOT / str(
        required_inputs.get("science_restart_higher_level_policy_trigger_report", "")
    ).strip()
    anti_alias_report_relpath = str(
        required_inputs.get("science_restart_anti_alias_proof_declaration_report", "")
    ).strip()

    post_z = _read_json(post_z_path)
    phase_z = _read_json(phase_z_path)
    summary_doc = _read_text(summary_doc_path)
    policy_trigger = _read_json(policy_trigger_path)
    anti_alias_report = None
    anti_alias_report_path = None
    if anti_alias_report_relpath:
        candidate_anti_alias_report_path = REPO_ROOT / anti_alias_report_relpath
        if candidate_anti_alias_report_path.exists():
            anti_alias_report_path = candidate_anti_alias_report_path
            anti_alias_report = _read_json(candidate_anti_alias_report_path)

    post_z_summary = dict(post_z.get("summary", {}))
    phase_z_summary = dict(phase_z.get("summary", {}))
    policy_trigger_summary = dict(policy_trigger.get("summary", {}))
    anti_alias_report_summary = dict(anti_alias_report.get("summary", {})) if anti_alias_report else {}

    post_z_outcome = str(post_z_summary.get("terminal_outcome", "")).strip()
    phase_z_outcome = str(phase_z_summary.get("terminal_outcome", "")).strip()
    higher_level_policy_trigger_outcome = str(
        policy_trigger_summary.get("terminal_outcome", "")
    ).strip()

    lane_reopen_authorized = bool(post_z_summary.get("lane_specific_reopen_authorized", True))
    new_lane_or_packet_authorized_now = bool(post_z_summary.get("new_lane_or_packet_authorized_now", True))
    thermal_lane_status = str(post_z_summary.get("thermal_boundary_lane_status", "")).strip()

    required_post_phase_z_outcome = str(contract.get("required_post_phase_z_outcome", "")).strip()
    required_phase_z_outcome = str(contract.get("required_phase_z_outcome", "")).strip()
    required_lane_reopen_authorized = bool(contract.get("required_lane_reopen_authorized", False))
    required_new_lane_or_packet_authorized_now = bool(
        contract.get("required_new_lane_or_packet_authorized_now", False)
    )
    required_thermal_lane_status = str(contract.get("required_thermal_lane_status", "")).strip()
    required_higher_level_policy_trigger_outcome = str(
        contract.get("required_higher_level_policy_trigger_outcome", "")
    ).strip()
    required_higher_level_policy_revision_authorized = bool(
        contract.get("required_higher_level_policy_revision_authorized", False)
    )
    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    restart_trigger_families = dict(contract.get("restart_trigger_families", {}))
    stronger_candidate_class_identified = bool(
        restart_trigger_families.get("stronger_candidate_class_identified", False)
    )
    higher_level_policy_revision_authorized = bool(
        policy_trigger_summary.get(
            "higher_level_policy_revision_authorized",
            restart_trigger_families.get("higher_level_policy_revision_authorized", False),
        )
    )
    material_new_external_evidence_class = bool(
        restart_trigger_families.get("material_new_external_evidence_class", False)
    )
    anti_alias_report_outcome = _maybe_text(anti_alias_report_summary.get("terminal_outcome"))
    if anti_alias_report is not None:
        anti_alias_proof_for_new_candidate_declared = bool(
            anti_alias_report_summary.get("anti_alias_proof_for_new_candidate_declared", False)
        )
    else:
        anti_alias_proof_for_new_candidate_declared = bool(
            restart_trigger_families.get("anti_alias_proof_for_new_candidate_declared", False)
        )
    force_policy_escalation_now = bool(restart_trigger_families.get("force_policy_escalation_now", False))

    signals_shape_ok = all(
        key in restart_trigger_families
        for key in [
            "stronger_candidate_class_identified",
            "higher_level_policy_revision_authorized",
            "material_new_external_evidence_class",
            "anti_alias_proof_for_new_candidate_declared",
            "force_policy_escalation_now",
        ]
    )

    anti_alias_report_usable = anti_alias_report is None or anti_alias_report_outcome in {
        "SCIENCE_RESTART_ANTI_ALIAS_PROOF_READY_BUT_UNDECLARED",
        "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARED",
        "",
    }

    trigger_selected = any(
        [
            stronger_candidate_class_identified,
            higher_level_policy_revision_authorized,
            material_new_external_evidence_class,
            force_policy_escalation_now,
        ]
    )

    summary_doc_semantics_ok = (
        "No currently governed lane is authorized to reopen." in summary_doc
        and "No currently screened future candidate is authorized for active execution." in summary_doc
    )

    preconditions_ok = (
        post_z_outcome == required_post_phase_z_outcome
        and phase_z_outcome == required_phase_z_outcome
        and lane_reopen_authorized == required_lane_reopen_authorized
        and new_lane_or_packet_authorized_now == required_new_lane_or_packet_authorized_now
        and thermal_lane_status == required_thermal_lane_status
        and higher_level_policy_trigger_outcome == required_higher_level_policy_trigger_outcome
        and higher_level_policy_revision_authorized == required_higher_level_policy_revision_authorized
        and forbid_reopen
        and anti_alias_report_usable
        and signals_shape_ok
        and summary_doc_semantics_ok
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "RESTART_TRIGGER_CONTRACT_EVIDENCE_INCOMPLETE")
    ).strip()

    if not signals_shape_ok:
        terminal_outcome = "HOLD_PENDING_RESTART_TRIGGER_CONTRACT_REPAIR"
        next_action = "REPAIR_RESTART_TRIGGER_FAMILY_SIGNAL_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "RESTART_TRIGGER_CONTRACT_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_RESTART_TRIGGER_PRECONDITIONS_AND_RERUN"
    elif trigger_selected and anti_alias_proof_for_new_candidate_declared:
        terminal_outcome = "OPEN_ONE_BOUNDED_PRE_SCREENING_RESTART_GATE"
        next_action = "OPEN_ONE_BOUNDED_PRE_SCREENING_GATE_WITH_NO_DIRECT_EXECUTION_AUTHORIZATION"
    elif trigger_selected and not anti_alias_proof_for_new_candidate_declared:
        terminal_outcome = "RESTART_TRIGGER_CONTRACT_EVIDENCE_INCOMPLETE"
        next_action = "DECLARE_ANTI_ALIAS_PROOF_BEFORE_OPENING_PRE_SCREENING_GATE"
    else:
        terminal_outcome = "REMAIN_IN_GOVERNED_STOP_STATE"
        next_action = "PRESERVE_GOVERNED_STOP_STATE_UNTIL_VALID_RESTART_TRIGGER_FAMILY_IS_PROVEN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "post_phase_z_outcome_match": post_z_outcome == required_post_phase_z_outcome,
            "phase_z_outcome_match": phase_z_outcome == required_phase_z_outcome,
            "lane_reopen_authorized_match": lane_reopen_authorized == required_lane_reopen_authorized,
            "new_lane_or_packet_authorized_now_match": new_lane_or_packet_authorized_now
            == required_new_lane_or_packet_authorized_now,
            "thermal_lane_status_match": thermal_lane_status == required_thermal_lane_status,
            "higher_level_policy_trigger_outcome_match": higher_level_policy_trigger_outcome
            == required_higher_level_policy_trigger_outcome,
            "higher_level_policy_revision_authorized_match": higher_level_policy_revision_authorized
            == required_higher_level_policy_revision_authorized,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "restart_trigger_family_signal_shape_ok": signals_shape_ok,
            "summary_doc_semantics_ok": summary_doc_semantics_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_RESTART_TRIGGER_CONTRACT_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_RESTART_TRIGGER_CONTRACT_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "restart_trigger_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "post_phase_z_outcome": post_z_outcome,
                "required_post_phase_z_outcome": required_post_phase_z_outcome,
                "phase_z_outcome": phase_z_outcome,
                "required_phase_z_outcome": required_phase_z_outcome,
                "lane_reopen_authorized": lane_reopen_authorized,
                "required_lane_reopen_authorized": required_lane_reopen_authorized,
                "new_lane_or_packet_authorized_now": new_lane_or_packet_authorized_now,
                "required_new_lane_or_packet_authorized_now": required_new_lane_or_packet_authorized_now,
                "thermal_lane_status": thermal_lane_status,
                "required_thermal_lane_status": required_thermal_lane_status,
                "higher_level_policy_trigger_outcome": higher_level_policy_trigger_outcome,
                "required_higher_level_policy_trigger_outcome": required_higher_level_policy_trigger_outcome,
                "higher_level_policy_revision_authorized": higher_level_policy_revision_authorized,
                "required_higher_level_policy_revision_authorized": required_higher_level_policy_revision_authorized,
                "anti_alias_proof_declaration_outcome": anti_alias_report_outcome or None,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "restart_trigger_families": restart_trigger_families,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "lane_specific_reopen_authorized": False,
            "new_lane_or_packet_authorized_now": False,
            "direct_execution_authorized_now": False,
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_post_phase_z_frontier_decision_report": _ptr(post_z_path),
            "science_phase_z_stronger_candidate_class_discovery_report": _ptr(phase_z_path),
            "science_restart_higher_level_policy_trigger_report": _ptr(policy_trigger_path),
            "science_restart_anti_alias_proof_declaration_report": (
                _ptr(anti_alias_report_path) if anti_alias_report_path is not None else None
            ),
            "science_frontier_stop_state_summary_doc": _ptr(summary_doc_path),
        },
        "non_claim_boundary": "Repository-local restart trigger contract report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate restart trigger contract report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_restart_trigger_contract_20260412_v0.json",
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
        "science_restart_trigger_contract_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
