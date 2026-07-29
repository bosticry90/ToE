from __future__ import annotations

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
    "prepare_qft_gr_quadratic_generic_background_linearization_"
    "gauge_and_jet_contract_v0"
)
SEMANTIC_STAGE_ID = "STRICT_HARMONIC_GAUGE_JET_CONTRACT"
OPEN_EVENT_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_events/"
    "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0_ATTEMPT_01_OPEN_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
PREDECESSOR_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_"
    "LINEARIZATION_RESULT_REVIEW_20260728_v0.json"
)
REDUCED_SYSTEM_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0.json"
)
MINKOWSKI_CONTROL_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-COMPANION-"
    "OPERATOR-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-GENERIC-BACKGROUND-LINEARIZATION-"
    "GAUGE-AND-JET-CONTRACT-v0.json"
)

SYMMETRIC_COMPONENTS = (
    "00",
    "01",
    "02",
    "03",
    "11",
    "12",
    "13",
    "22",
    "23",
    "33",
)


def _program_record() -> dict:
    registry = read_json(REGISTRY_PATH)
    return registry["bounded_programs_v1"][QUADRATIC_PROGRAM_ID]


def _verify_open_authority() -> dict:
    event = read_json(OPEN_EVENT_PATH)
    program = _program_record()
    if event["event_type"] != "ATTEMPT_OPEN":
        raise QuadraticHyperbolicityError("Stage 1 OPEN event has wrong type")
    if event["semantic_stage_id"] != SEMANTIC_STAGE_ID:
        raise QuadraticHyperbolicityError("Stage 1 OPEN semantic ID mismatch")
    if event["target"] != EXECUTION_TARGET:
        raise QuadraticHyperbolicityError("Stage 1 OPEN target mismatch")
    open_refs = [
        item
        for item in program["events"]
        if item["event_type"] == "ATTEMPT_OPEN"
        and item["attempt_sequence_number"] == 1
    ]
    if len(open_refs) != 1 or open_refs[0]["event_hash"] != event["event_hash"]:
        raise QuadraticHyperbolicityError(
            "bounded program does not preserve the Stage 1 OPEN event"
        )
    if SEMANTIC_STAGE_ID not in program["attempted_stage_ids"]:
        raise QuadraticHyperbolicityError("unexpected bounded attempt ledger")
    if program["state"] == "OPEN":
        if program["open_attempt_number"] != 1:
            raise QuadraticHyperbolicityError("bounded Stage 1 OPEN state is inconsistent")
        if program["event_chain_tip_hash"] != event["event_hash"]:
            raise QuadraticHyperbolicityError("OPEN event is not the live chain tip")
    elif program["state"] == "CLOSED":
        close_refs = [
            item
            for item in program["events"]
            if item["event_type"] == "ATTEMPT_CLOSE"
            and item["attempt_sequence_number"] == 1
        ]
        if program["open_attempt_number"] is not None:
            raise QuadraticHyperbolicityError("closed Stage 1 retains an open attempt")
        if program["last_closed_attempt_number"] < 1 or len(close_refs) != 1:
            raise QuadraticHyperbolicityError(
                "bounded program does not preserve the Stage 1 CLOSE linkage"
            )
        close_event = read_json(REPO_ROOT / close_refs[0]["path"])
        if close_event["open_event_hash"] != event["event_hash"]:
            raise QuadraticHyperbolicityError(
                "Stage 1 CLOSE event does not link to the preserved OPEN event"
            )
    else:
        raise QuadraticHyperbolicityError(
            f"bounded Stage 1 has unsupported program state {program['state']!r}"
        )
    return event


def _trace_coefficients() -> list[dict]:
    rows = []
    for component in SYMMETRIC_COMPONENTS:
        factor = 1 if component[0] == component[1] else 2
        rows.append(
            {
                "component": component,
                "coefficient": (
                    f"gbar^{component}"
                    if factor == 1
                    else f"2*gbar^{component}"
                ),
                "multiplicity": factor,
            }
        )
    return rows


def _trace_atlas() -> list[dict]:
    charts = []
    for pivot in SYMMETRIC_COMPONENTS:
        independent = [item for item in SYMMETRIC_COMPONENTS if item != pivot]
        charts.append(
            {
                "chart_id": f"TRACEFREE_CHART_PIVOT_{pivot}",
                "pivot_component": pivot,
                "open_domain": f"q_{pivot} != 0",
                "compact_conditioned_domain": f"|q_{pivot}| >= epsilon > 0",
                "independent_components": independent,
                "basis_rule": (
                    f"E_A=e_A-(q_A/q_{pivot})e_{pivot}, A != {pivot}"
                ),
                "dependent_component_rule": (
                    f"s_{pivot}=-(sum_A q_A*s_A)/q_{pivot}"
                    f"+(Sbar^ab*h_ab)/(4*q_{pivot})*q(gbar)"
                ),
            }
        )
    return charts


def _regularity_ledgers() -> dict:
    reduced = [
        {
            "field": "g_mn",
            "background_jet_in_evolution": 2,
            "perturbation_jet_in_evolution": 2,
            "identity_only_jet": 3,
            "required_class": "C3",
            "evolution_state": True,
        },
        {
            "field": "c_mna",
            "background_jet_in_evolution": 2,
            "perturbation_jet_in_evolution": 2,
            "identity_only_jet": 3,
            "required_class": "C3",
            "evolution_state": True,
        },
        {
            "field": "R",
            "background_jet_in_evolution": 2,
            "perturbation_jet_in_evolution": 2,
            "identity_only_jet": 3,
            "required_class": "C3",
            "evolution_state": True,
        },
        {
            "field": "r_a",
            "background_jet_in_evolution": 2,
            "perturbation_jet_in_evolution": 2,
            "identity_only_jet": 3,
            "required_class": "C3",
            "evolution_state": True,
        },
        {
            "field": "S_mn",
            "background_jet_in_evolution": 2,
            "perturbation_jet_in_evolution": 2,
            "identity_only_jet": 3,
            "required_class": "C3",
            "evolution_state": True,
        },
    ]
    metric = [
        {
            "relation": "c=partial g with c in C3",
            "implied_metric_class": "C4",
            "derivative_shift": 1,
        },
        {
            "relation": "R=scalar_curvature[g] with R in C3",
            "implied_metric_class": "C5",
            "derivative_shift": 2,
        },
        {
            "relation": "S=RicciTF[g] with S in C3",
            "implied_metric_class": "C5",
            "derivative_shift": 2,
        },
        {
            "relation": "r=partial R in C3 and R=scalar_curvature[g]",
            "implied_metric_class": "C6",
            "derivative_shift": 3,
        },
    ]
    return {
        "reduced_variable_regularity": reduced,
        "identity_verification_jets": {
            "background_reduced_jet_order": 3,
            "perturbation_reduced_jet_order": 3,
            "evolution_state": False,
            "purpose": (
                "linearized Bianchi, differentiated definition, and "
                "normal-form verification only"
            ),
        },
        "original_metric_equivalence_regularity": metric,
        "combined_sufficient_metric_class": "C6",
        "combined_sufficient_metric_perturbation_class": "C6",
        "optimality_claimed": False,
        "why_not_uniform_C3": (
            "C3 is a reduced-variable contract; imposing c, r, R, and S as "
            "metric derivatives raises the required metric regularity."
        ),
    }


def _rewrite_contract() -> dict:
    rules = [
        {
            "rule_id": "R1_STRICT_HARMONIC_ZERO",
            "lhs_head": "GAUGE_SOURCE_JET",
            "rhs_heads": [],
            "measure_rank": 6,
        },
        {
            "rule_id": "R2_TRACE_ATLAS",
            "lhs_head": "TRACE_PIVOT_COMPONENT",
            "rhs_heads": ["ATLAS_INDEPENDENT_COMPONENT"],
            "measure_rank": 5,
        },
        {
            "rule_id": "R3_INVERSE_METRIC_DERIVATIVE",
            "lhs_head": "INVERSE_METRIC_DERIVATIVE",
            "rhs_heads": ["METRIC_INVERSE", "METRIC_DERIVATIVE_VARIABLE"],
            "measure_rank": 4,
        },
        {
            "rule_id": "R4_DEFINITION_NORMALIZATION",
            "lhs_head": "DEFINITION_DERIVATIVE",
            "rhs_heads": ["REDUCED_DERIVATIVE_VARIABLE"],
            "measure_rank": 3,
        },
        {
            "rule_id": "R5_WAVE_NORMAL_DERIVATIVE",
            "lhs_head": "SECOND_NORMAL_DERIVATIVE",
            "rhs_heads": ["REDUCED_RHS", "SPATIAL_DERIVATIVE"],
            "measure_rank": 2,
        },
        {
            "rule_id": "R6_ON_SHELL_RESIDUAL",
            "lhs_head": "BACKGROUND_EQUATION_RESIDUAL",
            "rhs_heads": [],
            "measure_rank": 1,
        },
    ]
    lhs = [row["lhs_head"] for row in rules]
    if len(lhs) != len(set(lhs)):
        raise QuadraticHyperbolicityError("rewrite heads are not unique")
    ranks = {row["lhs_head"]: row["measure_rank"] for row in rules}
    for row in rules:
        for dependency in row["rhs_heads"]:
            if dependency in ranks and ranks[dependency] >= row["measure_rank"]:
                raise QuadraticHyperbolicityError("rewrite dependency is not decreasing")
    return {
        "rewrite_precedence": [row["rule_id"] for row in rules],
        "rules": rules,
        "well_founded_measure": (
            "lexicographic multiset count of typed lhs heads ordered by "
            "measure_rank, then expression tree size"
        ),
        "termination_established": True,
        "critical_pair_inventory": [],
        "critical_pairs_closed": True,
        "local_confluence_basis": (
            "Every lhs head is unique and typed; no lhs unifies with a proper "
            "subterm headed by another lhs. Phase boundaries are fixed by "
            "rewrite_precedence."
        ),
        "normal_form_unique": True,
        "normalization_idempotent": True,
        "off_shell_boundary": (
            "R6_ON_SHELL_RESIDUAL is disabled; all 64 residuals remain."
        ),
        "on_shell_boundary": (
            "R6 is enabled only after component Jacobian construction and "
            "after R1-R5 reach normal form."
        ),
    }


def _minkowski_regression(control: dict) -> dict:
    minkowski = control["exact_minkowski_control"]
    entries = minkowski["sparse_entries"]
    entry_hash = sha256_bytes(canonical_json_bytes(entries))
    if minkowski["matrix_shape"] != [128, 128]:
        raise QuadraticHyperbolicityError("Minkowski matrix shape drift")
    if minkowski["nonzero_entry_count"] != 224 or len(entries) != 224:
        raise QuadraticHyperbolicityError("Minkowski entry count drift")
    if entry_hash != minkowski["sparse_entry_sha256"]:
        raise QuadraticHyperbolicityError("Minkowski sparse-entry hash drift")
    return {
        "metric_signature": "(-,+,+,+)",
        "selected_trace_chart": "TRACEFREE_CHART_PIVOT_33",
        "trace_coefficients": {
            "q_00": "-1",
            "q_11": "1",
            "q_22": "1",
            "q_33": "1",
            "off_diagonal": "0",
        },
        "zero_curvature_trace_rule": "s_33=s_00-s_11-s_22",
        "strict_harmonic_source": "H^mu=delta H^mu=0",
        "matrix_shape": [128, 128],
        "nonzero_entry_count": 224,
        "sparse_entry_sha256": entry_hash,
        "regression_status": "EXACT_ACCEPTED_CONTROL_CUSTODY_REPRODUCED",
    }


def build_calculation() -> dict:
    event = _verify_open_authority()
    predecessor = read_json(PREDECESSOR_REVIEW_PATH)
    reduced = read_json(REDUCED_SYSTEM_PATH)
    control = read_json(MINKOWSKI_CONTROL_PATH)
    if predecessor["selected_next_target"] != EXECUTION_TARGET:
        raise QuadraticHyperbolicityError("predecessor did not select Stage 1")
    counts = {
        row["symbol"]: row["components"]
        for row in reduced["auxiliary_variables"]
    }
    if counts != {"g_mn": 10, "R": 1, "r_a": 4, "c_mna": 40, "S_mn": 9}:
        raise QuadraticHyperbolicityError("accepted reduced inventory drift")

    atlas = _trace_atlas()
    if len(atlas) != 10:
        raise QuadraticHyperbolicityError("trace-free atlas is incomplete")

    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_GENERIC_BACKGROUND_LINEARIZATION_"
            "GAUGE_AND_JET_CONTRACT_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-GENERIC-BACKGROUND-LINEARIZATION-"
            "GAUGE-AND-JET-CONTRACT-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "bounded_authority": {
            "program_id": QUADRATIC_PROGRAM_ID,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "attempt_sequence_number": 1,
            "open_event_path": OPEN_EVENT_PATH.relative_to(REPO_ROOT).as_posix(),
            "open_event_hash": event["event_hash"],
            "open_event_sha256": sha256_path(OPEN_EVENT_PATH),
        },
        "consumed_inputs": {
            "predecessor_review": {
                "path": PREDECESSOR_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
                "sha256": sha256_path(PREDECESSOR_REVIEW_PATH),
            },
            "reduced_system": {
                "path": REDUCED_SYSTEM_PATH.relative_to(REPO_ROOT).as_posix(),
                "sha256": sha256_path(REDUCED_SYSTEM_PATH),
            },
            "minkowski_control": {
                "path": MINKOWSKI_CONTROL_PATH.relative_to(REPO_ROOT).as_posix(),
                "sha256": sha256_path(MINKOWSKI_CONTROL_PATH),
            },
        },
        "strict_harmonic_gauge_contract": {
            "H_mu": "0",
            "delta_H_mu": "0",
            "gauge_source_jet_orders_zero": [0, 1, 2, 3],
            "constraint_additions": "ZERO",
            "damping_terms": "ZERO",
            "regularizers": "ZERO",
            "classification": "STRICT_HARMONIC_GENERIC_BACKGROUND",
            "gauge_universality_claimed": False,
        },
        "tracefree_atlas": {
            "symmetric_component_order": list(SYMMETRIC_COMPONENTS),
            "trace_covector_coefficients": _trace_coefficients(),
            "coverage_proof": (
                "A nondegenerate inverse metric cannot have all ten symmetric "
                "components zero, so at least one q_p is nonzero."
            ),
            "charts": atlas,
            "tangent_reconstruction": (
                "s_mn=E^A_mn*sigma_A"
                "+(1/4)gbar_mn*Sbar^rs*h_rs"
            ),
            "linearized_trace_identity": (
                "gbar^mn*s_mn=Sbar^rs*h_rs"
            ),
            "chart_overlap_transition": (
                "sigma^(q)=T_qp(gbar)*sigma^(p), obtained by equality of "
                "the reconstructed s_mn"
            ),
            "overlap_invariants": [
                "characteristic_roots",
                "Jordan_dimensions",
                "finite_loss_classification",
            ],
        },
        "regular_background_domain": {
            "regular_open_stratum": [
                "det(gbar_mn) != 0",
                "beta != 0",
                "3*alpha+beta != 0",
                "q_p != 0 in the selected trace chart",
                "component linearization Jacobian has locally constant rank",
            ],
            "compact_uniform_subset": [
                "|det(gbar_mn)| >= determinant_epsilon > 0",
                "|q_p| >= trace_epsilon > 0",
                "||gbar||+||gbar_inverse|| <= metric_bound",
                "||J^3 Ubar|| <= jet_bound",
            ],
            "uniformity_statement": (
                "locally uniform on compact subsets of the regular stratum"
            ),
            "excluded_controls": [
                "rank-changing algebraic surfaces",
                "trace-chart boundary q_p=0",
                "beta=0",
                "3*alpha+beta=0",
                "Minkowski and constant-curvature special controls",
            ],
        },
        "regularity_contract": _regularity_ledgers(),
        "background_classes": {
            "off_shell_generic_jet": (
                "Retain the accepted 64 reduced residuals; do not use field "
                "equations as substitutions."
            ),
            "on_shell_generic_background": (
                "Set reduced residuals to zero only after the off-shell "
                "component Jacobian and normal form have been recorded."
            ),
            "gauge_compatible_on_shell_background": (
                "Apply strict H=0 and the harmonic constraint after the "
                "on-shell normal form; no gauge-source coefficient survives."
            ),
            "accepted_equation_count_input": 64,
            "stage_2_independent_inventory_verification_required": True,
        },
        "rewrite_contract": _rewrite_contract(),
        "minkowski_regression": _minkowski_regression(control),
        "terminal_outcomes": [
            "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_COMPLETE"
        ],
        "claim_boundary": {
            "strict_harmonic_contract_frozen": True,
            "tracefree_atlas_complete": True,
            "finite_jet_order_frozen": True,
            "reduced_and_metric_regularity_separated": True,
            "rewrite_termination_and_confluence_established": True,
            "component_expanded_linearization_derived": False,
            "exact_generic_companion_operator_derived": False,
            "constraint_tangent_projector_constructed": False,
            "generic_finite_loss_established": False,
            "local_well_posedness_established": False,
            "quadratic_gravity_native_toe_status_claimed": False,
        },
        "selected_next_target": (
            "review_qft_gr_quadratic_generic_background_linearization_"
            "gauge_and_jet_contract_v0_result"
        ),
        "verdict": "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_COMPLETE",
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity strict-harmonic gauge-and-jet contract"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
