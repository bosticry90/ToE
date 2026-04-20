from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json"
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


def _cycle_index(value: str) -> int | None:
    match = re.search(r"CYCLE(\d+)", value.upper())
    if not match:
        return None
    return int(match.group(1))


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("unlock_policy", {}))
    contract = dict(declaration.get("unlock_contract", {}))

    continuation_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_cosmo_sr_bounded_continuation_family_report"))
    target_map_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_target_map_report"))
    synthesis_doc_path = REPO_ROOT / _maybe_text(required_inputs.get("cosmo_sr_cycle06_to_07_synthesis_doc"))
    candidate_doc_path = REPO_ROOT / _maybe_text(required_inputs.get("historical_cycle08_candidate_doc"))

    continuation_report = _read_json(continuation_path)
    target_map = _read_json(target_map_path)
    synthesis_doc_text = _read_text(synthesis_doc_path)
    candidate_doc_text = _read_text(candidate_doc_path)

    routed_rows = {row.get("row_id"): row for row in target_map.get("routed_rows", [])}
    target_row_id = _maybe_text(policy.get("required_target_row"))
    target_row = dict(routed_rows.get(target_row_id, {}))

    continuation_ok = (
        continuation_report.get("summary", {}).get("terminal_outcome")
        == _maybe_text(policy.get("required_continuation_outcome"))
        and continuation_report.get("summary", {}).get("next_action")
        == _maybe_text(policy.get("required_continuation_next_action"))
    )
    target_map_ok = (
        target_map.get("summary", {}).get("terminal_outcome")
        == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
        and target_row.get("row_id") == target_row_id
        and target_row.get("route_class") == _maybe_text(policy.get("required_target_route_class"))
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
        token in candidate_doc_text
        for token in [
            _maybe_text(policy.get("required_candidate_status")),
            _maybe_text(policy.get("required_candidate_payload_type")),
            "Candidate lane: `COSMO_SR_CYCLE08`.",
        ]
    )

    selected_unlock_payload_lane = _maybe_text(policy.get("selected_unlock_payload_lane")) or "NONE"
    selected_unlock_payload_target_doc = _maybe_text(policy.get("selected_unlock_payload_target_doc"))
    selected_unlock_payload_artifact = _maybe_text(policy.get("selected_unlock_payload_artifact"))
    selected_unlock_payload_gate = _maybe_text(policy.get("selected_unlock_payload_gate"))
    selected_unlock_payload_machine_pinned = bool(policy.get("selected_unlock_payload_machine_pinned", False))
    selected_unlock_payload_declared_nonredundant = bool(
        policy.get("selected_unlock_payload_declared_nonredundant", False)
    )
    minimum_allowed_cycle_index = int(policy.get("minimum_allowed_cycle_index", 8))

    selected_target_path = REPO_ROOT / selected_unlock_payload_target_doc if selected_unlock_payload_target_doc else None
    selected_artifact_path = REPO_ROOT / selected_unlock_payload_artifact if selected_unlock_payload_artifact else None
    selected_gate_path = REPO_ROOT / selected_unlock_payload_gate if selected_unlock_payload_gate else None
    selected_payload_paths_exist = all(
        [
            selected_target_path.exists() if selected_target_path else False,
            selected_artifact_path.exists() if selected_artifact_path else False,
            selected_gate_path.exists() if selected_gate_path else False,
        ]
    )
    selected_cycle_index = _cycle_index(selected_unlock_payload_lane)
    selected_cycle_allowed = selected_cycle_index is not None and selected_cycle_index >= minimum_allowed_cycle_index

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    contract_violation = False
    if selected_unlock_payload_lane == "NONE":
        contract_violation = any(
            [
                selected_unlock_payload_target_doc,
                selected_unlock_payload_artifact,
                selected_unlock_payload_gate,
                selected_unlock_payload_machine_pinned,
                selected_unlock_payload_declared_nonredundant,
            ]
        )
    else:
        contract_violation = not all(
            [
                selected_cycle_allowed,
                selected_unlock_payload_target_doc,
                selected_unlock_payload_artifact,
                selected_unlock_payload_gate,
                selected_unlock_payload_machine_pinned,
                selected_unlock_payload_declared_nonredundant,
                selected_payload_paths_exist,
            ]
        )

    if not all([continuation_ok, target_map_ok, synthesis_ok, historical_candidate_ok]):
        terminal_outcome = "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_COSMO_SR_UNLOCK_SURFACE_EVIDENCE_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_CONTRACT_VIOLATION"
        next_action = "REPAIR_COSMO_SR_UNLOCK_SURFACE_POLICY_BEFORE_REOPEN_AUTHORIZATION"
    elif selected_unlock_payload_lane != "NONE":
        terminal_outcome = "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED"
        next_action = "AUTHOR_NEW_COSMO_SR_CONTINUATION_FAMILY_AGAINST_SELECTED_MACHINE_PINNED_PAYLOAD"
    else:
        terminal_outcome = "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_LOCKED_PENDING_MACHINE_PINNED_PAYLOAD"
        next_action = "WAIT_FOR_NEW_MACHINE_PINNED_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_BEFORE_REOPEN_AUTHORIZATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "bounded_continuation_exhaustion_recorded": continuation_ok,
            "target_map_alignment_ok": target_map_ok,
            "cycle06_to_07_decision_boundary_present": synthesis_ok,
            "historical_cycle08_candidate_declared": historical_candidate_ok,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "unlock_requires_machine_pinned_payload": (
                    terminal_outcome != "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED"
                )
                or all(
                    [
                        selected_payload_paths_exist,
                        selected_unlock_payload_machine_pinned,
                        selected_unlock_payload_declared_nonredundant,
                        selected_cycle_allowed,
                    ]
                ),
                "locked_state_preserved_without_selected_payload": (
                    terminal_outcome
                    != "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_LOCKED_PENDING_MACHINE_PINNED_PAYLOAD"
                )
                or selected_unlock_payload_lane == "NONE",
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_route_class": target_row.get("route_class"),
                "minimum_allowed_cycle_index": minimum_allowed_cycle_index,
                "selected_unlock_payload_lane": selected_unlock_payload_lane,
                "selected_unlock_payload_machine_pinned": selected_unlock_payload_machine_pinned,
                "selected_unlock_payload_declared_nonredundant": selected_unlock_payload_declared_nonredundant,
                "selected_payload_paths_exist": selected_payload_paths_exist,
                "selected_cycle_index": selected_cycle_index,
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
            "minimum_allowed_cycle_index": minimum_allowed_cycle_index,
            "selected_unlock_payload_lane": selected_unlock_payload_lane,
            "selected_unlock_payload_machine_pinned": selected_unlock_payload_machine_pinned,
            "selected_unlock_payload_declared_nonredundant": selected_unlock_payload_declared_nonredundant,
            "selected_payload_paths_exist": selected_payload_paths_exist,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_cosmo_sr_bounded_continuation_family_report": _ptr(continuation_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "cosmo_sr_cycle06_to_07_synthesis_doc": _ptr(synthesis_doc_path),
            "historical_cycle08_candidate_doc": _ptr(candidate_doc_path),
            "selected_unlock_payload_target_doc": _maybe_text(policy.get("selected_unlock_payload_target_doc")) or None,
            "selected_unlock_payload_artifact": _maybe_text(policy.get("selected_unlock_payload_artifact")) or None,
            "selected_unlock_payload_gate": _maybe_text(policy.get("selected_unlock_payload_gate")) or None,
        },
        "non_claim_boundary": "Repository-local post-plan COSMO-SR Cycle08-or-later payload unlock surface only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-plan COSMO-SR Cycle08-or-later payload unlock surface report."
    )
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
        "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())