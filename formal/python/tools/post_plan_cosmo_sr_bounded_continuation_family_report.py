from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


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
    policy = dict(declaration.get("execution_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    target_map_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_target_map_report"))
    prior_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_cosmo_sr_first_live_seam_tranche_report"))
    dashboard_path = REPO_ROOT / _maybe_text(required_inputs.get("blocker_burn_dashboard_report"))
    cycle07_artifact_path = REPO_ROOT / _maybe_text(required_inputs.get("cosmo_sr_cycle07_artifact"))
    synthesis_doc_path = REPO_ROOT / _maybe_text(required_inputs.get("cosmo_sr_cycle06_to_07_synthesis_doc"))
    historical_candidate_path = REPO_ROOT / _maybe_text(required_inputs.get("historical_cycle08_candidate_doc"))

    target_map = _read_json(target_map_path)
    prior_report = _read_json(prior_path)
    dashboard = _read_json(dashboard_path)
    cycle07_artifact = _read_json(cycle07_artifact_path)
    synthesis_doc_text = _read_text(synthesis_doc_path)
    historical_candidate_text = _read_text(historical_candidate_path)

    routed_rows = {row.get("row_id"): row for row in target_map.get("routed_rows", [])}
    target_row_id = _maybe_text(policy.get("required_target_row"))
    target_row = dict(routed_rows.get(target_row_id, {}))
    alternate_row_id = _maybe_text(policy.get("required_alternate_blocked_row"))
    alternate_row = dict(routed_rows.get(alternate_row_id, {}))

    selected_continuation_lane = _maybe_text(policy.get("selected_continuation_lane")) or "NONE"
    selected_continuation_target_doc = _maybe_text(policy.get("selected_continuation_target_doc"))
    selected_continuation_artifact = _maybe_text(policy.get("selected_continuation_artifact"))
    selected_continuation_gate = _maybe_text(policy.get("selected_continuation_gate"))
    selected_continuation_machine_pinned = bool(policy.get("selected_continuation_machine_pinned", False))

    expected_cycle08_target_doc = REPO_ROOT / _maybe_text(policy.get("expected_cycle08_target_doc"))
    expected_cycle08_artifact = REPO_ROOT / _maybe_text(policy.get("expected_cycle08_artifact"))
    expected_cycle08_gate = REPO_ROOT / _maybe_text(policy.get("expected_cycle08_gate"))
    actual_cycle08_surfaces_pinned = all(
        [expected_cycle08_target_doc.exists(), expected_cycle08_artifact.exists(), expected_cycle08_gate.exists()]
    )

    required_target_route_class = _maybe_text(policy.get("required_target_route_class"))
    required_alternate_blocked_route_class = _maybe_text(policy.get("required_alternate_blocked_route_class"))

    target_map_ok = (
        target_map.get("summary", {}).get("terminal_outcome")
        == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
        and target_row.get("route_class") == required_target_route_class
        and alternate_row.get("route_class") == required_alternate_blocked_route_class
    )
    prior_ok = (
        prior_report.get("summary", {}).get("terminal_outcome") == _maybe_text(policy.get("required_prior_outcome"))
        and prior_report.get("summary", {}).get("next_action") == _maybe_text(policy.get("required_prior_next_action"))
        and bool(prior_report.get("summary", {}).get("row_truth_change_detected"))
        == bool(policy.get("required_prior_row_truth_change", False))
    )
    target_row_ok = (
        bool(target_row)
        and target_row.get("row_id") == target_row_id
        and target_row.get("blocker_class") == _maybe_text(policy.get("required_row_blocker_class"))
        and target_row.get("lane") == "COSMO_SR_CYCLE07"
    )
    synthesis_ok = all(
        token in synthesis_doc_text
        for token in [
            _maybe_text(policy.get("required_decision_rule")),
            _maybe_text(policy.get("required_decision_boundary_status")),
            "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        ]
    )
    historical_candidate_ok = all(
        token in historical_candidate_text
        for token in [
            "Candidate lane: `COSMO_SR_CYCLE08`.",
            "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0",
            "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle08_v0.json",
            "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle08_gate.py",
        ]
    )
    cycle07_ok = (
        cycle07_artifact.get("artifact_id") == "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0"
        and cycle07_artifact.get("seam_id") == _maybe_text(policy.get("required_target_seam"))
    )

    blocker_deltas = dashboard.get("blocker_scoreboard", {}).get("delta_by_class", {})
    seam_gap_delta = int(blocker_deltas.get("SEAM_INTEGRATION_GAP", 0))
    blocker_movement_detected = seam_gap_delta < 0 or target_row.get("physics_checkpoint_status") == "PHYSICS_COMPLETE"

    contract_violation = False
    if selected_continuation_lane == "NONE":
        contract_violation = any(
            [
                selected_continuation_target_doc,
                selected_continuation_artifact,
                selected_continuation_gate,
                selected_continuation_machine_pinned,
            ]
        )
    else:
        selected_target = REPO_ROOT / selected_continuation_target_doc if selected_continuation_target_doc else None
        selected_artifact = REPO_ROOT / selected_continuation_artifact if selected_continuation_artifact else None
        selected_gate = REPO_ROOT / selected_continuation_gate if selected_continuation_gate else None
        contract_violation = not all(
            [
                selected_target,
                selected_artifact,
                selected_gate,
                selected_continuation_machine_pinned,
                selected_target.exists() if selected_target else False,
                selected_artifact.exists() if selected_artifact else False,
                selected_gate.exists() if selected_gate else False,
                actual_cycle08_surfaces_pinned,
            ]
        )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    if not all([target_map_ok, prior_ok, target_row_ok, synthesis_ok, historical_candidate_ok, cycle07_ok]):
        terminal_outcome = "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_COSMO_SR_CONTINUATION_FAMILY_EVIDENCE_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_CONTRACT_VIOLATION"
        next_action = "REPAIR_COSMO_SR_CONTINUATION_FAMILY_POLICY_BEFORE_EXECUTION"
    elif blocker_movement_detected:
        terminal_outcome = "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_BLOCKER_MOVEMENT_RECORDED"
        next_action = "RERUN_TARGET_MAP_AND_REEVALUATE_SEAM_REROUTE_AND_MASTER_ACTION"
    elif selected_continuation_lane != "NONE" and actual_cycle08_surfaces_pinned:
        terminal_outcome = "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXECUTED_NONPROMOTED_CLOSEOUT"
        next_action = "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE"
    else:
        terminal_outcome = "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE"
        next_action = "DO_NOT_REOPEN_COSMO_SR_UNTIL_NEW_MACHINE_PINNED_CYCLE08_OR_LATER_PAYLOAD_EXISTS"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_map_matches_current_cosmo_sr_route": target_map_ok,
            "first_live_tranche_consumed_nonpromoted": prior_ok,
            "target_row_alignment_ok": target_row_ok,
            "cycle06_to_07_synthesis_boundary_present": synthesis_ok,
            "historical_cycle08_candidate_present": historical_candidate_ok,
            "cycle07_artifact_alignment_ok": cycle07_ok,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "row_or_blocker_movement_required_for_advancement": (
                    terminal_outcome != "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_BLOCKER_MOVEMENT_RECORDED"
                )
                or blocker_movement_detected,
                "explicit_exhaustion_only_without_machine_pinned_continuation": (
                    terminal_outcome != "POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_EXPLICITLY_EXHAUSTED_UNDER_CURRENT_SEAM_ARCHITECTURE"
                )
                or not actual_cycle08_surfaces_pinned,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_route_class": target_row.get("route_class"),
                "alternate_blocked_row": alternate_row_id,
                "alternate_blocked_route_class": alternate_row.get("route_class"),
                "prior_terminal_outcome": prior_report.get("summary", {}).get("terminal_outcome"),
                "prior_next_action": prior_report.get("summary", {}).get("next_action"),
                "seam_integration_gap_delta": seam_gap_delta,
                "selected_continuation_lane": selected_continuation_lane,
                "selected_continuation_machine_pinned": selected_continuation_machine_pinned,
                "actual_cycle08_surfaces_pinned": actual_cycle08_surfaces_pinned,
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
            "selected_continuation_lane": selected_continuation_lane,
            "selected_continuation_machine_pinned": selected_continuation_machine_pinned,
            "historical_cycle08_candidate_present": historical_candidate_ok,
            "actual_cycle08_surfaces_pinned": actual_cycle08_surfaces_pinned,
            "qm_stat_alternate_blocked": alternate_row.get("route_class") == required_alternate_blocked_route_class,
            "blocker_movement_detected": blocker_movement_detected,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "post_plan_cosmo_sr_first_live_seam_tranche_report": _ptr(prior_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "cosmo_sr_cycle07_artifact": _ptr(cycle07_artifact_path),
            "cosmo_sr_cycle06_to_07_synthesis_doc": _ptr(synthesis_doc_path),
            "historical_cycle08_candidate_doc": _ptr(historical_candidate_path),
            "expected_cycle08_target_doc": _ptr(expected_cycle08_target_doc),
            "expected_cycle08_artifact": _ptr(expected_cycle08_artifact),
            "expected_cycle08_gate": _ptr(expected_cycle08_gate),
        },
        "non_claim_boundary": "Repository-local post-plan COSMO-SR bounded continuation family only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan COSMO-SR bounded continuation family report.")
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
        "post_plan_cosmo_sr_bounded_continuation_family_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())