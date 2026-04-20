from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json"
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

    prior_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_cosmo_sr_bounded_continuation_family_report"))
    unlock_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report"))
    target_map_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_target_map_report"))
    selected_target_doc_path = REPO_ROOT / _maybe_text(required_inputs.get("selected_continuation_target_doc"))
    selected_artifact_path = REPO_ROOT / _maybe_text(required_inputs.get("selected_continuation_artifact"))
    selected_gate_path = REPO_ROOT / _maybe_text(required_inputs.get("selected_continuation_gate"))

    prior_report = _read_json(prior_path)
    unlock_report = _read_json(unlock_path)
    target_map = _read_json(target_map_path)
    selected_target_doc_text = _read_text(selected_target_doc_path)
    selected_artifact = _read_json(selected_artifact_path)
    selected_gate_text = _read_text(selected_gate_path)

    prior_summary = dict(prior_report.get("summary", {}))
    unlock_summary = dict(unlock_report.get("summary", {}))
    routed_rows = {row.get("row_id"): row for row in target_map.get("routed_rows", [])}
    target_row_id = _maybe_text(policy.get("required_target_row"))
    target_row = dict(routed_rows.get(target_row_id, {}))

    prior_ok = prior_summary.get("terminal_outcome") == _maybe_text(policy.get("required_prior_continuation_outcome"))
    unlock_ok = all(
        [
            unlock_summary.get("terminal_outcome") == _maybe_text(policy.get("required_unlock_outcome")),
            unlock_summary.get("next_action") == _maybe_text(policy.get("required_unlock_next_action")),
            unlock_summary.get("selected_unlock_payload_lane") == _maybe_text(policy.get("required_selected_lane")),
            bool(unlock_summary.get("selected_unlock_payload_machine_pinned")) == bool(policy.get("required_selected_machine_pinned")),
            bool(unlock_summary.get("selected_unlock_payload_declared_nonredundant")) == bool(policy.get("required_selected_declared_nonredundant")),
            unlock_summary.get("target_row_id") == target_row_id,
        ]
    )
    target_map_ok = (
        target_map.get("summary", {}).get("terminal_outcome") == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
        and target_row.get("route_class") == _maybe_text(policy.get("required_target_route_class"))
    )
    selected_payload_ok = all(
        [
            selected_target_doc_path.exists(),
            selected_artifact_path.exists(),
            selected_gate_path.exists(),
            "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0" in selected_target_doc_text,
            selected_artifact.get("artifact_id") == "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0",
            "def test_cosmo_sr_cycle08_artifacts_exist()" in selected_gate_text,
        ]
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    contract_violation = _maybe_text(policy.get("single_use_execution_mode")) != "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE"

    if not all([prior_ok, unlock_ok, target_map_ok, selected_payload_ok]):
        terminal_outcome = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_COSMO_SR_SELECTED_CONTINUATION_FAMILY_INPUTS_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_CONTRACT_VIOLATION"
        next_action = "REPAIR_COSMO_SR_SELECTED_CONTINUATION_FAMILY_POLICY_BEFORE_EXECUTION"
    else:
        terminal_outcome = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION"
        next_action = _maybe_text(policy.get("single_use_execution_mode"))

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "prior_continuation_exhaustion_recorded": prior_ok,
            "unlock_surface_ready": unlock_ok,
            "target_map_alignment_ok": target_map_ok,
            "selected_payload_tuple_exists": selected_payload_ok,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "selected_payload_is_machine_pinned": unlock_ok,
                "selected_family_is_execution_ready": terminal_outcome
                == "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION",
            },
            "inputs": {
                "target_row_id": target_row_id,
                "selected_lane": unlock_summary.get("selected_unlock_payload_lane"),
                "selected_payload_machine_pinned": unlock_summary.get("selected_unlock_payload_machine_pinned"),
                "selected_payload_declared_nonredundant": unlock_summary.get("selected_unlock_payload_declared_nonredundant"),
                "target_route_class": target_row.get("route_class"),
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
            "selected_continuation_lane": unlock_summary.get("selected_unlock_payload_lane"),
            "selected_continuation_machine_pinned": unlock_summary.get("selected_unlock_payload_machine_pinned"),
            "selected_continuation_target_doc": _ptr(selected_target_doc_path),
            "selected_continuation_artifact": _ptr(selected_artifact_path),
            "selected_continuation_gate": _ptr(selected_gate_path),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_cosmo_sr_bounded_continuation_family_report": _ptr(prior_path),
            "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report": _ptr(unlock_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "selected_continuation_target_doc": _ptr(selected_target_doc_path),
            "selected_continuation_artifact": _ptr(selected_artifact_path),
            "selected_continuation_gate": _ptr(selected_gate_path),
        },
        "non_claim_boundary": "Repository-local post-plan COSMO-SR selected continuation family only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan COSMO-SR selected continuation family report.")
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
        "post_plan_cosmo_sr_selected_continuation_family_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())