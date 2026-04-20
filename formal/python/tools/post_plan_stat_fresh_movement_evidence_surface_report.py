from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
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
    policy = dict(declaration.get("evidence_policy", {}))
    contract = dict(declaration.get("evidence_contract", {}))

    dossier_path = REPO_ROOT / _text(required_inputs.get("stat_dossier_declaration"))
    qualification_path = REPO_ROOT / _text(required_inputs.get("fresh_movement_qualification_report"))
    reactivation_path = REPO_ROOT / _text(required_inputs.get("stat_reactivation_tranche_report"))
    prior_path = REPO_ROOT / _text(required_inputs.get("prior_stat_completion_tranche_report"))
    dashboard_path = REPO_ROOT / _text(required_inputs.get("blocker_burn_dashboard_report"))
    trend_path = REPO_ROOT / _text(required_inputs.get("theorem_gap_row_outcome_trend_report"))
    target_map_path = REPO_ROOT / _text(required_inputs.get("post_plan_target_map_report"))
    doc_path = REPO_ROOT / _text(required_inputs.get("stat_target_doc"))
    artifact_path = REPO_ROOT / _text(required_inputs.get("stat_artifact"))
    gate_path = REPO_ROOT / _text(required_inputs.get("stat_gate"))
    candidate_doc_path = REPO_ROOT / _text(required_inputs.get("historical_stat_candidate_decision_doc"))
    checkpoint_doc_path = REPO_ROOT / _text(required_inputs.get("historical_stat_checkpoint_doc"))

    dossier_declaration = _read_json(dossier_path)
    qualification_report = _read_json(qualification_path)
    reactivation_report = _read_json(reactivation_path)
    prior_report = _read_json(prior_path)
    dashboard_report = _read_json(dashboard_path)
    trend_report = _read_json(trend_path)
    target_map_report = _read_json(target_map_path)
    doc_text = _read_text(doc_path)
    artifact = _read_json(artifact_path)
    _read_text(gate_path)
    candidate_doc_text = _read_text(candidate_doc_path)
    checkpoint_doc_text = _read_text(checkpoint_doc_path)

    dossier_policy = dict(dossier_declaration.get("row_policy", {}))
    qualification_summary = dict(qualification_report.get("summary", {}))
    reactivation_summary = dict(reactivation_report.get("summary", {}))
    target_row_id = _text(policy.get("required_target_row"))
    target_row = next(
        (row for row in target_map_report.get("routed_rows", []) if row.get("row_id") == target_row_id),
        {},
    )
    row_outcome_counts = (
        trend_report.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {}).get(target_row_id, {})
    )
    artifact_payload = dict(artifact.get("payload", {}))
    theorem_gap_delta = int(
        dashboard_report.get("blocker_scoreboard", {}).get("delta_by_class", {}).get("THEOREM_GAP", 0) or 0
    )

    dossier_ok = all(
        [
            dossier_declaration.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
            _text(dossier_policy.get("row_id")) == target_row_id,
            _text(dossier_policy.get("required_route_class")) == _text(policy.get("required_target_route_class")),
            _text(dossier_policy.get("measurable_blocker_delta_criterion"))
            == _text(policy.get("required_measurable_blocker_delta_criterion")),
        ]
    )
    qualification_visible = qualification_summary.get("default_selected_row") == _text(
        policy.get("required_default_selected_row")
    )
    qualification_selects_stat = qualification_summary.get("selected_row") == target_row_id
    reactivation_ok = reactivation_summary.get("terminal_outcome") == _text(policy.get("required_reactivation_outcome"))
    prior_ok = prior_report.get("summary", {}).get("terminal_outcome") == _text(
        policy.get("required_prior_completion_outcome")
    )
    target_map_ok = all(
        [
            target_row.get("row_id") == target_row_id,
            target_row.get("route_class") == _text(policy.get("required_target_route_class")),
            target_row.get("authoritative_next_action") == _text(policy.get("required_target_next_action")),
        ]
    )
    packet_tuple_matches_dossier = all(
        [
            _text(dossier_policy.get("bounded_execution_surface_declaration"))
            == "formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_20260419_v0.json",
            _ptr(doc_path) == _text(required_inputs.get("stat_target_doc")),
            _ptr(artifact_path) == _text(required_inputs.get("stat_artifact")),
            _ptr(gate_path) == _text(required_inputs.get("stat_gate")),
        ]
    )
    doc_ok = all(token in doc_text for token in [_ptr(artifact_path), _ptr(gate_path)])
    artifact_ok = all(
        [
            artifact.get("artifact_id") == _text(policy.get("required_artifact_id")),
            artifact_payload.get("status") == _text(policy.get("required_artifact_status")),
            artifact_payload.get("decision") == _text(policy.get("required_artifact_decision")),
            artifact_payload.get("evidence_tier") == _text(policy.get("required_artifact_evidence_tier")),
        ]
    )
    candidate_ok = _text(policy.get("required_candidate_state_token")) in candidate_doc_text
    checkpoint_ok = _text(policy.get("required_checkpoint_state_token")) in checkpoint_doc_text

    current_packet_tuple_pinned = all([packet_tuple_matches_dossier, doc_ok, artifact_ok, gate_path.exists()])
    packet04_chain_ready = all(
        [
            dossier_ok,
            qualification_visible,
            reactivation_ok,
            prior_ok,
            target_map_ok,
            current_packet_tuple_pinned,
            candidate_ok,
            checkpoint_ok,
        ]
    )
    fresh_movement_machine_pinned = packet04_chain_ready and theorem_gap_delta < 0 and qualification_selects_stat
    contract_violation = qualification_selects_stat and not all([packet04_chain_ready, theorem_gap_delta < 0])

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _text(contract.get("default_outcome"))

    if not all([dossier_declaration, qualification_report, reactivation_report, prior_report, target_map_report]):
        terminal_outcome = "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_INPUTS_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_CONTRACT_VIOLATION"
        next_action = "REPAIR_STAT_EVIDENCE_SURFACE_BEFORE_ANY_REOPEN_AUTHORIZATION"
    elif fresh_movement_machine_pinned:
        terminal_outcome = "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_FRESH_MOVEMENT_MACHINE_PINNED"
        next_action = "RERUN_STAT_DOSSIER_AND_SUCCESSOR_AUTHORIZATION_REVIEW_ONCE"
    elif packet04_chain_ready:
        terminal_outcome = "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING"
        next_action = "PIN_ONE_FRESH_STAT_ATTRIBUTABLE_THEOREM_GAP_DELTA_BEFORE_AUTHORIZATION"
    else:
        terminal_outcome = "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_INPUTS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "stat_dossier_declared": dossier_ok,
            "qualification_surface_visible": qualification_visible,
            "reactivation_tranche_fail_closed": reactivation_ok,
            "prior_nonpromoted_outcome_recorded": prior_ok,
            "target_map_alignment_ok": target_map_ok,
            "current_packet04_tuple_pinned": current_packet_tuple_pinned,
            "historical_candidate_state_visible": candidate_ok,
            "historical_checkpoint_state_visible": checkpoint_ok,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "fresh_movement_requires_negative_theorem_gap_delta": (
                    terminal_outcome
                    != "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_FRESH_MOVEMENT_MACHINE_PINNED"
                )
                or theorem_gap_delta < 0,
                "ready_state_requires_visible_packet04_chain": (
                    terminal_outcome
                    != "POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_PACKET04_CHAIN_READY_DELTA_PENDING"
                )
                or packet04_chain_ready,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "qualification_selected_row": qualification_summary.get("selected_row"),
                "theorem_gap_delta": theorem_gap_delta,
                "row_outcome_total": row_outcome_counts.get("total", 0),
                "row_outcome_success": row_outcome_counts.get("success", 0),
                "row_outcome_no_change": row_outcome_counts.get("no_change", 0),
                "current_target_doc": _ptr(doc_path),
                "current_target_artifact": _ptr(artifact_path),
                "current_target_gate": _ptr(gate_path),
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
            "selected_evidence_target_doc": _ptr(doc_path),
            "selected_evidence_artifact": _ptr(artifact_path),
            "selected_evidence_gate": _ptr(gate_path),
            "selected_evidence_tuple_pinned": current_packet_tuple_pinned,
            "historical_candidate_state_visible": candidate_ok,
            "historical_checkpoint_state_visible": checkpoint_ok,
            "qualification_selected_row": qualification_summary.get("selected_row"),
            "theorem_gap_delta": theorem_gap_delta,
            "fresh_movement_machine_pinned": fresh_movement_machine_pinned,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "stat_dossier_declaration": _ptr(dossier_path),
            "fresh_movement_qualification_report": _ptr(qualification_path),
            "stat_reactivation_tranche_report": _ptr(reactivation_path),
            "prior_stat_completion_tranche_report": _ptr(prior_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "theorem_gap_row_outcome_trend_report": _ptr(trend_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "stat_target_doc": _ptr(doc_path),
            "stat_artifact": _ptr(artifact_path),
            "stat_gate": _ptr(gate_path),
            "historical_stat_candidate_decision_doc": _ptr(candidate_doc_path),
            "historical_stat_checkpoint_doc": _ptr(checkpoint_doc_path),
        },
        "non_claim_boundary": "Repository-local STAT fresh-movement evidence surface only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan STAT fresh-movement evidence surface report.")
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
        "post_plan_stat_fresh_movement_evidence_surface_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
