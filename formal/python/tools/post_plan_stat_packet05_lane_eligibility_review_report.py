from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_REPORT_20260420_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_20260420_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_stat_packet05_lane_eligibility_review_20260420_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("eligibility_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    evidence_path = REPO_ROOT / _text(required_inputs.get("stat_fresh_movement_evidence_surface_report"))
    matrix_path = REPO_ROOT / _text(required_inputs.get("completion_matrix"))
    protocol_path = REPO_ROOT / _text(required_inputs.get("foundational_empirical_protocol"))
    packet04_matrix_path = REPO_ROOT / _text(required_inputs.get("foundational_empirical_packet04_matrix"))
    packet05_progression_path = REPO_ROOT / _text(required_inputs.get("foundational_empirical_packet05_progression_policy"))
    packet05_matrix_path = REPO_ROOT / _text(required_inputs.get("foundational_empirical_packet05_matrix"))
    packet05_ledger_path = REPO_ROOT / _text(required_inputs.get("empirical_packet05_decision_ledger"))
    doc_path = REPO_ROOT / _text(required_inputs.get("stat_target_doc"))
    artifact_path = REPO_ROOT / _text(required_inputs.get("stat_artifact"))
    gate_path = REPO_ROOT / _text(required_inputs.get("stat_gate"))

    evidence_report = _read_json(evidence_path)
    packet04_matrix = _read_json(packet04_matrix_path)
    packet05_matrix = _read_json(packet05_matrix_path)
    packet05_ledger = _read_json(packet05_ledger_path)
    artifact = _read_json(artifact_path)
    matrix_rows = _parse_markdown_table(
        _read_text(matrix_path),
        [
            "row_id",
            "domain",
            "lane",
            "current_status",
            "blocker_class",
            "primary_target",
            "primary_artifact",
            "primary_gate",
            "governance_checkpoint_status",
            "physics_checkpoint_status",
            "gate_runtime_status",
        ],
    )
    protocol_text = _read_text(protocol_path)
    packet05_progression_text = _read_text(packet05_progression_path)
    doc_text = _read_text(doc_path)
    _read_text(gate_path)

    evidence_summary = evidence_report.get("summary", {})
    target_row_id = _text(policy.get("required_target_row"))
    lane_key = _text(policy.get("required_lane_key"))
    matrix_row = next((row for row in matrix_rows if row.get("row_id") == target_row_id), {})
    packet04_row = dict(packet04_matrix.get("rows", {}).get(lane_key, {}))
    packet05_enabled_lanes = [str(v).strip() for v in packet05_matrix.get("enabled_lanes", [])]
    packet05_rows = dict(packet05_matrix.get("rows", {}))
    packet05_ledger_rows = dict(packet05_ledger.get("rows", {}))
    artifact_payload = dict(artifact.get("payload", {}))

    evidence_pending = evidence_summary.get("terminal_outcome") == _text(policy.get("required_evidence_outcome"))
    evidence_target_ok = all(
        [
            evidence_summary.get("target_row_id") == target_row_id,
            evidence_summary.get("selected_evidence_target_doc") == _ptr(doc_path),
            evidence_summary.get("selected_evidence_artifact") == _ptr(artifact_path),
            evidence_summary.get("selected_evidence_gate") == _ptr(gate_path),
        ]
    )
    matrix_row_ok = all(
        [
            bool(matrix_row),
            matrix_row.get("blocker_class") == _text(policy.get("required_blocker_class")),
            matrix_row.get("physics_checkpoint_status") == _text(policy.get("required_physics_checkpoint_status")),
            matrix_row.get("primary_target") == _ptr(doc_path),
            matrix_row.get("primary_artifact") == _ptr(artifact_path),
            matrix_row.get("primary_gate") == _ptr(gate_path),
        ]
    )
    packet04_matrix_ok = all(
        [
            packet04_row.get("doc_path") == _ptr(doc_path),
            packet04_row.get("artifact_path") == _ptr(artifact_path),
            packet04_row.get("gate_path") == _ptr(gate_path),
        ]
    )
    protocol_packet05_enablement_ok = _text(policy.get("required_protocol_packet05_enablement_token")) in protocol_text
    protocol_packet05_ledger_ok = _text(policy.get("required_protocol_packet05_ledger_token")) in protocol_text
    progression_bootstrap_ok = _text(policy.get("required_progression_bootstrap_token")) in packet05_progression_text
    progression_non_enabled_clause_ok = _text(policy.get("required_progression_non_enabled_clause")) in packet05_progression_text
    required_packet05_bootstrap_lanes = [str(v).strip() for v in policy.get("required_packet05_bootstrap_lanes", [])]
    packet05_bootstrap_lanes_ok = all(lane in packet05_enabled_lanes for lane in required_packet05_bootstrap_lanes)
    doc_and_gate_ok = all(token in doc_text for token in [_ptr(artifact_path), _ptr(gate_path)])
    artifact_ok = all(
        [
            artifact.get("artifact_id") == _text(policy.get("required_artifact_id")),
            artifact_payload.get("status") == _text(policy.get("required_artifact_status")),
            artifact_payload.get("decision") == _text(policy.get("required_artifact_decision")),
            artifact_payload.get("evidence_tier") == _text(policy.get("required_artifact_evidence_tier")),
        ]
    )

    stat_packet05_lane_enabled = lane_key in packet05_enabled_lanes
    stat_packet05_row_declared = lane_key in packet05_rows
    stat_packet05_ledger_visible = lane_key in packet05_ledger_rows
    eligible_for_packet05_bootstrap = all(
        [
            stat_packet05_lane_enabled,
            stat_packet05_row_declared,
            stat_packet05_ledger_visible,
        ]
    )
    common_ready = all(
        [
            evidence_pending,
            evidence_target_ok,
            matrix_row_ok,
            packet04_matrix_ok,
            protocol_packet05_enablement_ok,
            protocol_packet05_ledger_ok,
            progression_bootstrap_ok,
            progression_non_enabled_clause_ok,
            packet05_bootstrap_lanes_ok,
            doc_and_gate_ok,
            artifact_ok,
        ]
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if common_ready and eligible_for_packet05_bootstrap:
        terminal_outcome = "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_ELIGIBLE_FOR_PACKET05_BOOTSTRAP"
        next_action = "RERUN_STAT_DELTA_SOURCE_REVIEW_AND_PROMOTE_ONE_BOUNDED_PACKET05_PATH_ONLY"
    elif common_ready and not any([stat_packet05_lane_enabled, stat_packet05_row_declared, stat_packet05_ledger_visible]):
        terminal_outcome = "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_NOT_ELIGIBLE_UNDER_CURRENT_BOOTSTRAP"
        next_action = "RERUN_STAT_DELTA_SOURCE_REVIEW_DOSSIER_QUALIFICATION_AND_RETAIN_FAIL_CLOSED_POSTURE"
    else:
        terminal_outcome = "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_INPUTS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(contract.get("default_outcome"))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "stat_evidence_surface_pending_delta": evidence_pending,
            "stat_evidence_target_alignment_ok": evidence_target_ok,
            "live_completion_matrix_row_alignment_ok": matrix_row_ok,
            "packet04_matrix_alignment_ok": packet04_matrix_ok,
            "protocol_packet05_enablement_declared": protocol_packet05_enablement_ok,
            "protocol_packet05_ledger_declared": protocol_packet05_ledger_ok,
            "packet05_progression_bootstrap_declared": progression_bootstrap_ok,
            "packet05_non_enabled_lane_clause_declared": progression_non_enabled_clause_ok,
            "packet05_bootstrap_lanes_match_live_matrix": packet05_bootstrap_lanes_ok,
            "stat_packet04_artifact_alignment_ok": artifact_ok,
            "stat_packet04_doc_and_gate_pointers_ok": doc_and_gate_ok,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "bootstrap_eligibility_requires_live_lane_bindings": (
                    terminal_outcome != "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_ELIGIBLE_FOR_PACKET05_BOOTSTRAP"
                )
                or eligible_for_packet05_bootstrap,
                "ineligibility_requires_no_live_lane_bindings": (
                    terminal_outcome != "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_NOT_ELIGIBLE_UNDER_CURRENT_BOOTSTRAP"
                )
                or not any([stat_packet05_lane_enabled, stat_packet05_row_declared, stat_packet05_ledger_visible]),
            },
            "inputs": {
                "target_row_id": target_row_id,
                "lane_key": lane_key,
                "evidence_surface_outcome": evidence_summary.get("terminal_outcome"),
                "artifact_decision": artifact_payload.get("decision"),
                "artifact_evidence_tier": artifact_payload.get("evidence_tier"),
                "packet05_enabled_lanes": packet05_enabled_lanes,
                "stat_packet05_row_declared": stat_packet05_row_declared,
                "stat_packet05_ledger_visible": stat_packet05_ledger_visible,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "lane_key": lane_key,
            "evidence_surface_outcome": evidence_summary.get("terminal_outcome"),
            "eligible_for_packet05_bootstrap": eligible_for_packet05_bootstrap,
            "packet05_enabled_lanes": packet05_enabled_lanes,
            "stat_packet05_lane_enabled": stat_packet05_lane_enabled,
            "stat_packet05_row_declared": stat_packet05_row_declared,
            "stat_packet05_ledger_visible": stat_packet05_ledger_visible,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "stat_fresh_movement_evidence_surface_report": _ptr(evidence_path),
            "completion_matrix": _ptr(matrix_path),
            "foundational_empirical_protocol": _ptr(protocol_path),
            "foundational_empirical_packet04_matrix": _ptr(packet04_matrix_path),
            "foundational_empirical_packet05_progression_policy": _ptr(packet05_progression_path),
            "foundational_empirical_packet05_matrix": _ptr(packet05_matrix_path),
            "empirical_packet05_decision_ledger": _ptr(packet05_ledger_path),
            "stat_target_doc": _ptr(doc_path),
            "stat_artifact": _ptr(artifact_path),
            "stat_gate": _ptr(gate_path),
        },
        "non_claim_boundary": "Repository-local STAT packet-05 lane eligibility review only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan STAT packet-05 lane eligibility review report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
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
        "post_plan_stat_packet05_lane_eligibility_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())