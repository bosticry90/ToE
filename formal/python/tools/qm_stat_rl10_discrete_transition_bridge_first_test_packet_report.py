from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_PACKET_20260412_v0.json"
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


def _single_terminal_outcome(
    *,
    out_of_scope: bool,
    requires_undeclared_structure: bool,
    incoherent: bool,
) -> str:
    if out_of_scope:
        return "BRIDGE_SEAM_FIRST_TEST_OUT_OF_SCOPE"
    if requires_undeclared_structure:
        return "BRIDGE_SEAM_FIRST_TEST_REQUIRES_UNDECLARED_STRUCTURE"
    if incoherent:
        return "BRIDGE_SEAM_FIRST_TEST_INCOHERENT"
    return "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE"


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    test_scope = dict(declaration.get("test_scope", {}))
    structure = dict(declaration.get("declared_transition_structure", {}))
    undeclared_structure_policy = dict(declaration.get("undeclared_structure_policy", {}))
    terminal_contract = dict(declaration.get("terminal_contract", {}))

    proposal_decl_path = REPO_ROOT / str(
        required_inputs.get("new_external_path_seam_model_proposal_declaration", "")
    ).strip()
    proposal_report_path = REPO_ROOT / str(
        required_inputs.get("new_external_path_seam_model_proposal_report", "")
    ).strip()
    feasibility_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_transition_dynamics_feasibility_review_report", "")
    ).strip()
    sigma_db_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_rl10_sigma_db_transformation_report", "")
    ).strip()
    comparator_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_single_baseline_comparator_report", "")
    ).strip()

    proposal_decl = _read_json(proposal_decl_path)
    proposal_report = _read_json(proposal_report_path)
    feasibility_report = _read_json(feasibility_path)
    sigma_db_report = _read_json(sigma_db_path)
    comparator_report = _read_json(comparator_path)

    proposal_scope = dict(proposal_decl.get("proposal_scope", {}))
    proposal_summary = dict(proposal_report.get("summary", {}))
    feasibility_summary = dict(feasibility_report.get("summary", {}))
    sigma_db_summary = dict(sigma_db_report.get("summary", {}))
    comparator_summary = dict(comparator_report.get("summary", {}))

    proposed_seam_model_class_id = str(test_scope.get("proposed_seam_model_class_id", "")).strip()
    bounded_first_test_id = str(test_scope.get("bounded_first_test_id", "")).strip()
    target_baseline_id = str(test_scope.get("single_baseline_id", "")).strip()

    proposal_outcome = str(proposal_summary.get("proposal_outcome", "")).strip()
    proposal_class = str(proposal_summary.get("proposed_seam_model_class_id", "")).strip()
    proposal_first_test = str(proposal_summary.get("bounded_first_test_id", "")).strip()
    no_lane_reopen_rule = str(proposal_decl.get("proposal_contract", {}).get("no_existing_lane_reopen_rule", "")).strip()

    feasibility_outcome = str(feasibility_summary.get("review_outcome", "")).strip()
    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()
    comparator_baseline_id = str(comparator_summary.get("baseline_id", "")).strip()

    sigma_proxy_missing = not bool(sigma_db_summary.get("sigma_proxy_definable_from_current_qm_stat_surfaces", False))
    db_residual_missing = not bool(sigma_db_summary.get("db_residual_definable_from_current_qm_stat_surfaces", False))

    kernel = dict(structure.get("discrete_transition_kernel", {}))
    rates = dict(structure.get("bidirectional_transition_rate_matrix", {}))
    bridge_interface = dict(structure.get("stationary_flow_sigma_db_interface", {}))

    state_space = list(kernel.get("state_space", []))
    shape = list(rates.get("shape", []))
    row_stochastic = bool(kernel.get("row_stochastic", False))
    bidirectional = bool(rates.get("bidirectional", False))
    nonnegative_off_diag = bool(rates.get("nonnegative_off_diagonal", False))
    sigma_mapping_declared = bool(bridge_interface.get("sigma_proxy_mapping_declared", False))
    db_mapping_declared = bool(bridge_interface.get("db_residual_mapping_declared", False))
    interface_baseline = str(bridge_interface.get("baseline_id", "")).strip()

    allowed_new_assumptions = set(undeclared_structure_policy.get("allowed_new_assumptions", []))
    forbidden_extra_assumptions = list(undeclared_structure_policy.get("forbidden_extra_assumptions", []))

    proposal_justified = proposal_outcome == "NEW_SEAM_MODEL_PROPOSAL_JUSTIFIED"
    seam_match = proposal_class == proposed_seam_model_class_id == proposal_scope.get("proposed_seam_model_class_id")
    first_test_match = proposal_first_test == bounded_first_test_id == proposal_scope.get("bounded_first_test_id")
    governance_boundary_preserved = (
        no_lane_reopen_rule == "DO_NOT_REOPEN_EXISTING_QM_STAT_OR_OTHER_CYCLE11_LANES_FROM_THIS_PROPOSAL"
        and str(test_scope.get("governance_boundary", "")).strip()
        == "DO_NOT_REOPEN_EXISTING_QM_STAT_OR_OTHER_CYCLE11_LANES"
    )
    discrete_support_only = bool(test_scope.get("discrete_support_only", False))

    transition_structure_coherent = (
        len(state_space) >= 2
        and len(shape) == 2
        and shape[0] == shape[1] == len(state_space)
        and row_stochastic
        and bidirectional
        and nonnegative_off_diag
    )
    bridge_observable_ready = (
        sigma_mapping_declared
        and db_mapping_declared
        and interface_baseline == target_baseline_id
        and comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        and comparator_baseline_id == target_baseline_id
        and sigma_proxy_missing
        and db_residual_missing
    )

    required_assumptions = {
        "DECLARE_DISCRETE_TRANSITION_DYNAMICS_OPERATOR_OR_MARKOV_KERNEL",
        "DECLARE_BIDIRECTIONAL_TRANSITION_RATES_OR_EQUIVALENT_TRANSITION_MATRIX",
        "DECLARE_STATIONARY_FLOW_TO_SIGMA_DB_OBSERVABLE_INTERFACE",
    }
    requires_undeclared_structure = (
        not required_assumptions.issubset(allowed_new_assumptions)
        or len(forbidden_extra_assumptions) > 0
    )

    out_of_scope = (
        not proposal_justified
        or not seam_match
        or not first_test_match
        or not governance_boundary_preserved
        or feasibility_outcome != "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE"
        or not discrete_support_only
    )
    incoherent = not (transition_structure_coherent and bridge_observable_ready)

    terminal_outcome = _single_terminal_outcome(
        out_of_scope=out_of_scope,
        requires_undeclared_structure=requires_undeclared_structure,
        incoherent=incoherent,
    )
    allowed_outcomes = set(terminal_contract.get("allowed_outcomes", []))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "proposal_justified": proposal_justified,
            "governance_boundary_preserved": governance_boundary_preserved,
            "transition_structure_coherent": transition_structure_coherent,
            "bridge_observable_ready": bridge_observable_ready,
            "single_terminal_outcome_rule_declared": str(terminal_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_TERMINAL_OUTCOME",
            "no_loop_rule_declared": str(terminal_contract.get("no_loop_rule", "")).strip()
            == "ONE_BOUNDED_FIRST_TEST_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_terminal_outcome_materialized": True,
                "single_baseline_only_enforced": comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "current_lane_reopen_block_preserved": governance_boundary_preserved,
            },
            "inputs": {
                "proposal_outcome": proposal_outcome,
                "proposed_seam_model_class_id": proposed_seam_model_class_id,
                "bounded_first_test_id": bounded_first_test_id,
                "feasibility_outcome": feasibility_outcome,
                "comparator_status": comparator_status,
                "comparator_baseline_id": comparator_baseline_id,
                "sigma_proxy_missing_in_qm_stat": sigma_proxy_missing,
                "db_residual_missing_in_qm_stat": db_residual_missing,
                "transition_state_space_size": len(state_space),
                "transition_rate_matrix_shape": shape,
                "required_assumptions": sorted(required_assumptions),
                "declared_allowed_new_assumptions": sorted(allowed_new_assumptions),
                "forbidden_extra_assumptions": forbidden_extra_assumptions,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome == "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE",
                "phase_status": "COMPLETE",
                "next_action": "TERMINAL_OUTCOME_RECORDED",
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "proposed_seam_model_class_id": proposed_seam_model_class_id,
            "bounded_first_test_id": bounded_first_test_id,
            "governance_boundary_pass": governance_boundary_preserved,
            "transition_structure_coherent": transition_structure_coherent,
            "bridge_observable_ready": bridge_observable_ready,
            "requires_undeclared_structure": requires_undeclared_structure,
            "next_action": "TERMINAL_OUTCOME_RECORDED",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "new_external_path_seam_model_proposal_declaration": _ptr(proposal_decl_path),
            "new_external_path_seam_model_proposal_report": _ptr(proposal_report_path),
            "qm_stat_transition_dynamics_feasibility_review_report": _ptr(feasibility_path),
            "qm_stat_rl10_sigma_db_transformation_report": _ptr(sigma_db_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
        },
        "non_claim_boundary": "Repository-local bounded first-test packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 discrete-transition bridge first-test packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_first_test_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())