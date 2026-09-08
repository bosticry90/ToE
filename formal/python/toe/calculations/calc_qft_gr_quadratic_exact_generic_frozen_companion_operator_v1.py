from __future__ import annotations

import re

from formal.python.toe.calculations.calc_qft_gr_quadratic_exact_generic_frozen_companion_operator import (
    minkowski_control_companion,
    sparse_entry_ledger,
)
from formal.python.tools.bounded_program_governance import QUADRATIC_PROGRAM_ID
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    canonical_json_bytes,
    read_json,
    sha256_bytes,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
EXECUTION_TARGET = (
    "derive_qft_gr_quadratic_exact_generic_frozen_companion_operator_v1"
)
SEMANTIC_STAGE_ID = "EXACT_FROZEN_COMPANION_OPERATOR"
OPEN_EVENT_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_events/"
    "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0_ATTEMPT_03_OPEN_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
STAGE_1_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-GENERIC-BACKGROUND-"
    "LINEARIZATION-GAUGE-AND-JET-CONTRACT-v0.json"
)
STAGE_2_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-"
    "GENERIC-BACKGROUND-LINEARIZATION-v1.json"
)
MINKOWSKI_CONTROL_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-"
    "COMPANION-OPERATOR-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-"
    "COMPANION-OPERATOR-v1.json"
)

REFERENCE_PATTERN = re.compile(r"@([A-Za-z0-9_]+)")
LEAF_PATTERN = re.compile(r"\$([A-Za-z0-9_]+)")


def _verify_open_authority() -> dict:
    event = read_json(OPEN_EVENT_PATH)
    registry = read_json(REGISTRY_PATH)
    program = registry["bounded_programs_v1"][QUADRATIC_PROGRAM_ID]
    if (
        event["event_type"] != "ATTEMPT_OPEN"
        or event["attempt_sequence_number"] != 3
        or event["semantic_stage_id"] != SEMANTIC_STAGE_ID
        or event["target"] != EXECUTION_TARGET
    ):
        raise QuadraticHyperbolicityError("Stage 3 OPEN event mismatch")
    open_is_live = (
        program["state"] == "OPEN"
        and program["open_attempt_number"] == 3
        and program["event_chain_tip_hash"] == event["event_hash"]
    )
    open_is_immutably_closed = (
        program["last_closed_attempt_number"] >= 3
        and any(
            row["event_type"] == "ATTEMPT_OPEN"
            and row["attempt_sequence_number"] == 3
            and row["event_hash"] == event["event_hash"]
            for row in program["events"]
        )
        and any(
            row["event_type"] == "ATTEMPT_CLOSE"
            and row["attempt_sequence_number"] == 3
            for row in program["events"]
        )
    )
    if not (open_is_live or open_is_immutably_closed):
        raise QuadraticHyperbolicityError("Stage 3 OPEN event is not live")
    return event


def _reachable_perturbation_leaves(
    expression: str, nodes_by_id: dict[str, dict]
) -> set[str]:
    leaves: set[str] = set()
    visited: set[str] = set()
    stack = list(REFERENCE_PATTERN.findall(expression))
    leaves.update(LEAF_PATTERN.findall(expression))
    while stack:
        identifier = stack.pop()
        if identifier in visited:
            continue
        visited.add(identifier)
        node = nodes_by_id.get(identifier)
        if node is None:
            raise QuadraticHyperbolicityError(
                f"unresolved component DAG reference: {identifier}"
            )
        node_expression = node["expression"]
        leaves.update(LEAF_PATTERN.findall(node_expression))
        stack.extend(REFERENCE_PATTERN.findall(node_expression))
    return {
        leaf
        for leaf in leaves
        if leaf == "q"
        or leaf.startswith(
            ("h_", "k_", "dk_", "d2k_", "u_", "du_", "d2u_", "s_", "ds_", "d2s_")
        )
    }


def _minkowski_regression() -> dict:
    accepted = read_json(MINKOWSKI_CONTROL_PATH)["exact_minkowski_control"]
    entries = sparse_entry_ledger(minkowski_control_companion())
    digest = sha256_bytes(canonical_json_bytes(entries))
    if (
        accepted["matrix_shape"] != [128, 128]
        or accepted["nonzero_entry_count"] != 224
        or accepted["sparse_entries"] != entries
        or accepted["sparse_entry_sha256"] != digest
    ):
        raise QuadraticHyperbolicityError("Minkowski companion regression changed")
    return {
        "classification": "MINKOWSKI_CONTROL_REPRODUCED",
        "matrix_shape": [128, 128],
        "nonzero_entry_count": 224,
        "sparse_entry_sha256": digest,
        "does_not_supply_generic_off_constraint_closure": True,
    }


def _closure_audit(stage_1: dict, stage_2: dict) -> dict:
    nodes_by_id = {
        node["id"]: node for node in stage_2["component_dag"]["nodes"]
    }
    common = stage_2["component_equations"]["common_equations"]
    metric_rows = [
        row for row in common if row["classification"] == "TEN_METRIC_COMPONENT_EQUATIONS"
    ]
    scalar_rows = [row for row in common if row["id"] == "delta_ER"]
    if len(metric_rows) != 10 or len(scalar_rows) != 1:
        raise QuadraticHyperbolicityError("accepted metric/scalar row inventory changed")

    metric_leaves = set().union(
        *(
            _reachable_perturbation_leaves(
                row["linearized_component_expression"], nodes_by_id
            )
            for row in metric_rows
        )
    )
    scalar_leaves = _reachable_perturbation_leaves(
        scalar_rows[0]["linearized_component_expression"], nodes_by_id
    )
    metric_has_derivative_proxy = any(leaf.startswith("dk_") for leaf in metric_leaves)
    metric_has_independent_second_jet = any(
        leaf.startswith(("dh_", "d2h_")) for leaf in metric_leaves
    )
    scalar_has_derivative_proxy = any(leaf.startswith("du_") for leaf in scalar_leaves)
    scalar_has_independent_second_jet = any(
        leaf.startswith(("dq_", "d2q_")) for leaf in scalar_leaves
    )

    leaf_contract = stage_2["leaf_symbol_contract"]["perturbation_leaf_families"]
    contracted_metric_second_jet = any(
        family.startswith(("dh_", "d2h_")) for family in leaf_contract
    )
    contracted_scalar_second_jet = any(
        family.startswith(("dq_", "d2q_")) for family in leaf_contract
    )

    charts: list[dict] = []
    for chart in stage_2["component_equations"]["tracefree_atlas_equations"]:
        pivot = chart["chart_id"].removeprefix("TRACEFREE_CHART_PIVOT_")
        reachable = set().union(
            *(
                _reachable_perturbation_leaves(
                    row["linearized_component_expression"], nodes_by_id
                )
                for row in chart["component_expressions"]
            )
        )
        retained = sorted(
            leaf
            for leaf in reachable
            if leaf == f"s_{pivot}" or leaf.startswith(f"ds_{pivot}_")
        )
        charts.append(
            {
                "chart_id": chart["chart_id"],
                "dependent_component": pivot,
                "dependent_tangent_leaves_retained": retained,
                "closed_in_its_nine_independent_spin_variables": not retained,
            }
        )

    missing_differentiated_reconstruction = all(
        not row["closed_in_its_nine_independent_spin_variables"] for row in charts
    )
    exact_128_state_closure = not (
        (metric_has_derivative_proxy and not metric_has_independent_second_jet)
        or (scalar_has_derivative_proxy and not scalar_has_independent_second_jet)
        or missing_differentiated_reconstruction
        or not contracted_metric_second_jet
        or not contracted_scalar_second_jet
    )
    if exact_128_state_closure:
        raise QuadraticHyperbolicityError(
            "closure audit unexpectedly found a unique generic 128-state map"
        )

    return {
        "question": (
            "Does the accepted component expansion determine one exact generic "
            "off-constraint 128-state companion operator without importing the "
            "later constraint-tangent construction?"
        ),
        "answer": False,
        "terminal_outcome": "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED",
        "state_dimension_requested": 128,
        "accepted_reduced_unknown_count": 64,
        "metric_wave_slot_audit": {
            "metric_rows": 10,
            "uses_dk_as_second_derivative_proxy": metric_has_derivative_proxy,
            "contains_independent_dh_or_d2h_slots": metric_has_independent_second_jet,
            "leaf_contract_contains_independent_dh_or_d2h_family": (
                contracted_metric_second_jet
            ),
            "status": "BLOCKED_OFF_CONSTRAINT_SLOT_AMBIGUITY",
        },
        "scalar_wave_slot_audit": {
            "scalar_rows": 1,
            "uses_du_as_second_derivative_proxy": scalar_has_derivative_proxy,
            "contains_independent_dq_or_d2q_slots": scalar_has_independent_second_jet,
            "leaf_contract_contains_independent_dq_or_d2q_family": (
                contracted_scalar_second_jet
            ),
            "status": "BLOCKED_OFF_CONSTRAINT_SLOT_AMBIGUITY",
        },
        "tracefree_chart_closure": {
            "chart_count": len(charts),
            "charts": charts,
            "differentiated_dependent_component_substitution_present": False,
            "status": "BLOCKED_DEPENDENT_TRACE_JETS_RETAINED",
        },
        "nonunique_mappings": [
            {
                "id": "METRIC_EQUIVALENCE_MAPPING",
                "description": (
                    "Interpret dk and du in the metric and scalar rows through "
                    "c=partial g and r=partial R. This imposes definition "
                    "constraints before the Stage 4 tangent-space construction."
                ),
                "not_authorized_here": True,
            },
            {
                "id": "INDEPENDENT_EQUAL_ORDER_WAVE_MAPPING",
                "description": (
                    "Introduce independent dh,d2h,dq,d2q wave jets and retain "
                    "c,r as separate equal-order variables. Those jet families "
                    "are absent from the accepted Stage 2 contract."
                ),
                "not_available_from_inputs": True,
            },
        ],
        "why_the_block_is_decisive": (
            "The two mappings agree only on the definition-constraint surface "
            "but define different off-constraint companion systems. Stage 4, "
            "not Stage 3, is authorized to construct that tangent surface. "
            "Choosing either map here would import a later-stage conclusion or "
            "add unapproved state variables."
        ),
        "stage_1_atlas_formula_is_not_enough": (
            "Stage 1 freezes an algebraic tangent trace reconstruction. The "
            "accepted Stage 2 chart equations still retain the dependent "
            "component and its differentiated leaves, and do not provide the "
            "differentiated substitution ledger needed for an exact chartwise "
            "companion matrix."
        ),
        "required_but_prohibited_repair": [
            "a new off-constraint wave-slot contract",
            "independent metric/scalar wave-jet families or an early constraint projection",
            "differentiated trace-chart reconstruction through required jet order",
        ],
        "bounded_program_consequence": (
            "Stage 3 is BLOCKED. The zero-repair bounded program must close "
            "this attempt and advance directly to its mandatory role gate."
        ),
        "regular_stratum_contract_preserved": stage_1["regular_background_domain"],
    }


def build_calculation() -> dict:
    event = _verify_open_authority()
    stage_1 = read_json(STAGE_1_PATH)
    stage_2 = read_json(STAGE_2_PATH)
    if stage_2["terminal_outcome"] != (
        "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE"
    ):
        raise QuadraticHyperbolicityError("accepted Stage 2 result changed")
    audit = _closure_audit(stage_1, stage_2)
    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_"
            "COMPANION_OPERATOR_v1"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-"
            "COMPANION-OPERATOR-v1"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "bounded_authority": {
            "program_id": QUADRATIC_PROGRAM_ID,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "attempt_sequence_number": 3,
            "open_event_path": OPEN_EVENT_PATH.relative_to(REPO_ROOT).as_posix(),
            "open_event_hash": event["event_hash"],
            "opened_from_commit": event["opened_from_commit"],
            "scope_hash": event["scope_hash"],
        },
        "consumed_stage_1_contract": {
            "path": STAGE_1_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(STAGE_1_PATH),
        },
        "consumed_stage_2_component_expansion": {
            "path": STAGE_2_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(STAGE_2_PATH),
        },
        "generic_companion_closure_audit": audit,
        "Minkowski_regression": _minkowski_regression(),
        "claim_boundary": {
            "exact_generic_frozen_companion_operator_derived": False,
            "Minkowski_control_remains_exact": True,
            "constraint_tangent_projector_constructed": False,
            "subprincipal_propagator_growth_computed": False,
            "generic_finite_loss_established": False,
            "local_well_posedness_established": False,
            "quadratic_gravity_native_toe_status_claimed": False,
        },
        "prohibitions_respected": {
            "subsidiary_scientific_target_created": False,
            "repair_target_created": False,
            "constraint_surface_imposed_early": False,
            "new_state_variables_invented": False,
            "placeholder_matrix_called_exact": False,
            "spectral_result_claimed": False,
        },
        "terminal_result": "BLOCKED",
        "terminal_outcome": "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED",
        "mandatory_exit_target": (
            "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"
        ),
        "verdict": (
            "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED_BECAUSE_THE_ACCEPTED_"
            "COMPONENT_EXPANSION_DOES_NOT_FIX_A_UNIQUE_OFF_CONSTRAINT_128_"
            "STATE_WAVE_SLOT_MAP_OR_CLOSE_THE_NINE_COMPONENT_TRACE_CHARTS_"
            "NO_REPAIR_TARGET_MANDATORY_ROLE_GATE"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity exact generic frozen companion operator v1"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
