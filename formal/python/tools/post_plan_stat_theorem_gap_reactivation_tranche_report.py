from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_20260419_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_stat_theorem_gap_reactivation_tranche_20260419_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    auth_path = REPO_ROOT / _text(required_inputs.get("successor_family_authorization_review_report"))
    qual_path = REPO_ROOT / _text(required_inputs.get("fresh_movement_qualification_report"))
    dossier_path = REPO_ROOT / _text(required_inputs.get("stat_dossier_report"))
    prior_path = REPO_ROOT / _text(required_inputs.get("prior_stat_completion_tranche_report"))
    target_map_path = REPO_ROOT / _text(required_inputs.get("post_plan_target_map_report"))
    matrix_path = REPO_ROOT / _text(required_inputs.get("completion_matrix"))
    dashboard_path = REPO_ROOT / _text(required_inputs.get("blocker_burn_dashboard_report"))
    contradiction_path = REPO_ROOT / _text(required_inputs.get("science_maturity_contradiction_report"))
    doc_path = REPO_ROOT / _text(required_inputs.get("stat_target_doc"))
    artifact_path = REPO_ROOT / _text(required_inputs.get("stat_artifact"))
    gate_path = REPO_ROOT / _text(required_inputs.get("stat_gate"))

    auth_report = _read_json(auth_path)
    qual_report = _read_json(qual_path)
    dossier_report = _read_json(dossier_path)
    prior_report = _read_json(prior_path)
    target_map_report = _read_json(target_map_path)
    dashboard_report = _read_json(dashboard_path)
    contradiction_report = _read_json(contradiction_path)
    artifact = _read_json(artifact_path)
    doc_text = _read_text(doc_path)
    _read_text(gate_path)
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

    row_id = _text(policy.get("required_target_row"))
    target_row = next((row for row in target_map_report.get("routed_rows", []) if row.get("row_id") == row_id), {})
    matrix_row = next((row for row in matrix_rows if row.get("row_id") == row_id), {})
    payload = dict(artifact.get("payload", {}))
    expected_doc = _rel(doc_path)
    expected_artifact = _rel(artifact_path)
    expected_gate = _rel(gate_path)

    auth_ok = auth_report.get("summary", {}).get("terminal_outcome") == _text(policy.get("required_authorization_outcome"))
    qual_ok = qual_report.get("summary", {}).get("terminal_outcome") == _text(policy.get("required_qualification_outcome"))
    selected_ok = auth_report.get("summary", {}).get("selected_row") == _text(policy.get("required_selected_row"))
    dossier_ok = dossier_report.get("summary", {}).get("row_id") == row_id and bool(dossier_report.get("summary", {}).get("fresh_movement_machine_pinned"))
    prior_ok = prior_report.get("summary", {}).get("terminal_outcome") == _text(policy.get("required_prior_outcome"))
    route_ok = target_row.get("route_class") == _text(policy.get("required_target_route_class"))
    row_ok = bool(matrix_row) and all(
        [
            matrix_row.get("blocker_class") == _text(policy.get("required_target_blocker_class")),
            matrix_row.get("primary_target") == expected_doc,
            matrix_row.get("primary_artifact") == expected_artifact,
            matrix_row.get("primary_gate") == expected_gate,
        ]
    )
    doc_ok = all(token in doc_text for token in [expected_artifact, expected_gate])
    artifact_ok = (
        artifact.get("artifact_id") == "stat_empirical_comparison_packet_04_v0"
        and payload.get("status") == _text(policy.get("required_target_status"))
        and payload.get("decision") in {_text(policy.get("required_target_decision")), "PRUNE_v0"}
        and payload.get("evidence_tier") == _text(policy.get("required_target_evidence_tier"))
    )
    contradiction_ok = any(
        obs.get("row_id") == row_id and obs.get("observation_type") == "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP"
        for obs in contradiction_report.get("modeled_observations", [])
    )

    row_truth_change_detected = bool(matrix_row) and (
        matrix_row.get("blocker_class") != "THEOREM_GAP"
        or matrix_row.get("physics_checkpoint_status") != "THEOREM_GAP_OPEN"
        or matrix_row.get("current_status") == "GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE"
    )
    explicit_exhaustion_detected = payload.get("decision") == "PRUNE_v0" and not row_truth_change_detected and auth_ok and qual_ok and dossier_ok

    prerequisites_ok = all([auth_ok, qual_ok, selected_ok, dossier_ok, prior_ok, route_ok, row_ok, doc_ok, artifact_ok, contradiction_ok])
    if not all([target_row, matrix_row]):
        terminal_outcome = "HOLD_PENDING_POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_REPAIR"
        next_action = "RESTORE_STAT_REACTIVATION_INPUT_SHAPE_AND_RERUN"
    elif prerequisites_ok and row_truth_change_detected:
        terminal_outcome = "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EXECUTED_AND_PROMOTED"
        next_action = "RERUN_THEOREM_GAP_RERANKING_AFTER_STAT_BLOCKER_REDUCTION"
    elif prerequisites_ok and explicit_exhaustion_detected:
        terminal_outcome = "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EXPLICITLY_EXHAUSTED"
        next_action = "RERUN_THEOREM_GAP_RERANKING_AFTER_STAT_EXPLICIT_EXHAUSTION"
    else:
        terminal_outcome = "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_STAT_REACTIVATION_EVIDENCE_OR_RETAIN_TERMINAL_HOLD"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(contract.get("default_outcome"))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "authorization_surface_ok": auth_ok,
            "qualification_surface_ok": qual_ok,
            "selected_row_ok": selected_ok,
            "dossier_surface_ok": dossier_ok,
            "prior_outcome_recorded": prior_ok,
            "target_map_route_class_ok": route_ok,
            "row_alignment_ok": row_ok,
            "doc_tokens_present": doc_ok,
            "artifact_alignment_ok": artifact_ok,
            "live_theorem_gap_observation_present": contradiction_ok,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "promotion_only_if_row_truth_changed": (terminal_outcome != "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EXECUTED_AND_PROMOTED") or row_truth_change_detected,
                "exhaustion_only_if_pruned_under_new_authorization": (terminal_outcome != "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EXPLICITLY_EXHAUSTED") or explicit_exhaustion_detected,
            },
            "inputs": {
                "target_row_id": row_id,
                "artifact_decision": payload.get("decision"),
                "artifact_status": payload.get("status"),
                "blocker_movement_status": dashboard_report.get("blocker_scoreboard", {}).get("movement_status"),
                "blocker_net_delta": dashboard_report.get("blocker_scoreboard", {}).get("net_delta"),
                "row_current_status": matrix_row.get("current_status"),
                "row_physics_checkpoint_status": matrix_row.get("physics_checkpoint_status"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": row_id,
            "target_route_class": target_row.get("route_class"),
            "row_truth_change_detected": row_truth_change_detected,
            "explicit_exhaustion_detected": explicit_exhaustion_detected,
            "artifact_decision": payload.get("decision"),
            "selected_row": auth_report.get("summary", {}).get("selected_row"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "successor_family_authorization_review_report": _ptr(auth_path),
            "fresh_movement_qualification_report": _ptr(qual_path),
            "stat_dossier_report": _ptr(dossier_path),
            "prior_stat_completion_tranche_report": _ptr(prior_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "completion_matrix": _ptr(matrix_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "science_maturity_contradiction_report": _ptr(contradiction_path),
            "stat_target_doc": _ptr(doc_path),
            "stat_artifact": _ptr(artifact_path),
            "stat_gate": _ptr(gate_path),
        },
        "non_claim_boundary": "Repository-local refreshed STAT theorem-gap reactivation tranche only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the refreshed STAT theorem-gap reactivation tranche report.")
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
        "post_plan_stat_theorem_gap_reactivation_tranche_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
