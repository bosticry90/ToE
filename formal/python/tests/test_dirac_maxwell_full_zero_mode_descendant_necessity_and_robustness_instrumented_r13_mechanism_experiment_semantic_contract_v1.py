from __future__ import annotations

import numpy as np

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1
    as contract,
)


def test_support_constant_and_provenance_closure_is_exact() -> None:
    leaves = {
        (hypothesis, constant_id)
        for hypothesis, constants in contract.SUPPORT_CONSTANTS_V1.items()
        for constant_id in constants
    }
    provenance = {
        (record["hypothesis"], record["constant_id"])
        for record in contract.SUPPORT_CONSTANT_PROVENANCE
    }
    assert len(leaves) == 23
    assert len(contract.SUPPORT_CONSTANT_PROVENANCE) == 23
    assert provenance == leaves
    assert all(
        record["source_artifact"]
        and record["source_record_ids"]
        and record["derivation_formula"]
        and record["rounding_rule"]
        and record["scientific_meaning"]
        and record["source_category"] in contract.SOURCE_CATEGORIES
        and record["source_commit"] == contract.UNCOMMITTED_SOURCE_SENTINEL
        and record["decision_bearing_or_descriptive"] == "DECISION_BEARING"
        and record["nonfuture"] is True
        and record["future_mechanism_outputs_used"] is False
        for record in contract.SUPPORT_CONSTANT_PROVENANCE
    )
    assert contract.validate_semantic_contract() == []


def test_h_c_uses_independent_paths_and_legacy_q_is_gate_only() -> None:
    p0 = np.array([[0.2, -0.1, 0.3], [0.1, 0.0, -0.1]])
    grad = np.array([[0.08, -0.06, 0.02], [0.01, 0.02, -0.03]])
    stored_direct_defect = np.array(
        [[2.0e-5, -1.0e-5, 3.0e-5], [1.0e-5, 2.0e-5, -1.0e-5]]
    )
    dt = 0.01
    a = 0.25
    # The raw state/operator path is exact-Maxwell here.  The independently
    # stored terminal defect is deliberately changed and must remain visible.
    p1 = p0 - dt * grad
    rho0 = np.array([[0.04, -0.02, 0.01], [0.02, -0.01, 0.03]])
    rho1 = np.array([[0.03, -0.015, 0.005], [0.01, -0.02, 0.025]])
    baseline = contract.reconstruct_independent_hc_paths(
        direct_terminal_p_equation_defect=np.zeros_like(stored_direct_defect),
        p_previous=p0,
        p_current=p1,
        rho_previous=rho0,
        rho_current=rho1,
        continuity_current_midpoint_independently_recomputed=grad.copy(),
        maxwell_source_midpoint_registered=grad.copy(),
        a=a,
        dt=dt,
        requested_solver_tolerance=1.0e-8,
    )
    paths = contract.reconstruct_independent_hc_paths(
        direct_terminal_p_equation_defect=stored_direct_defect,
        p_previous=p0,
        p_current=p1,
        rho_previous=rho0,
        rho_current=rho1,
        continuity_current_midpoint_independently_recomputed=grad.copy(),
        maxwell_source_midpoint_registered=grad.copy(),
        a=a,
        dt=dt,
        requested_solver_tolerance=1.0e-8,
    )
    summary = contract.summarize_independent_hc_paths(paths)
    assert summary["max_relative_path_mismatch"] > 0.0
    assert not np.array_equal(
        paths["independent_path_mismatch"],
        baseline["independent_path_mismatch"],
    )
    changed_current = contract.reconstruct_independent_hc_paths(
        direct_terminal_p_equation_defect=np.zeros_like(stored_direct_defect),
        p_previous=p0,
        p_current=p1,
        rho_previous=rho0,
        rho_current=rho1,
        continuity_current_midpoint_independently_recomputed=grad
        + np.array([[0.01, 0.0, -0.01], [0.0, 0.02, -0.02]]),
        maxwell_source_midpoint_registered=grad.copy(),
        a=a,
        dt=dt,
        requested_solver_tolerance=1.0e-8,
    )
    assert not np.array_equal(
        changed_current["independent_path_mismatch"],
        baseline["independent_path_mismatch"],
    )
    assert np.array_equal(
        changed_current["legacy_q_operator_gate_only"],
        baseline["legacy_q_operator_gate_only"],
    )
    assert summary["gamma32_used"] is False
    assert summary["legacy_q_used"] is False
    assert paths["mechanism_path_sources_independent"] is True
    assert paths["continuity_path_uses_registered_maxwell_source"] is False
    assert paths["legacy_q_mechanism_decision_bearing"] is False
    assert contract.LEGACY_Q["may_support_H_C"] is False
    assert all("gamma" not in key.casefold() for key in contract.SUPPORT_CONSTANTS_V1["H_C"])


def test_review_control_and_identity_mutation_contract_is_complete_and_unique() -> None:
    assert len(contract.MISSING_REVIEW_CONTROL_IDS) == 9
    assert len(set(contract.MISSING_REVIEW_CONTROL_IDS)) == 9
    assert len(contract.IDENTITY_MUTATION_FIELDS) == 20
    assert len(set(contract.IDENTITY_MUTATION_FIELDS)) == 20
    assert set(contract.IDENTITY_MUTATION_VALUES) == set(
        contract.IDENTITY_MUTATION_FIELDS
    )
    records = contract.FULL_ADVERSARIAL_REGISTRY_V1
    ids = [record["control_id"] for record in records]
    assert len(records) == 41
    assert len(ids) == len(set(ids))
    assert set(contract.MISSING_REVIEW_CONTROL_IDS) <= set(ids)
    assert {
        f"M_FREEZE_MATRIX_IDENTITY_FIELD_{field.upper()}"
        for field in contract.IDENTITY_MUTATION_FIELDS
    } <= set(ids)


def test_preserved_v0_controls_have_exact_executable_mutations_and_outcomes() -> None:
    expected = {
        "M_FREEZE_CANDIDATE_RUN_OMITTED": {
            "mutation": "remove the final R10 noninstrumented record from the exact matrix",
            "diagnostic": "RUN_MATRIX_COUNT_MISMATCH",
            "evidence": "BLOCKED_RUN_IDENTITY",
            "decision": "EVIDENCE_ADMISSIBILITY_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
        "M_FREEZE_R10_NEIGHBOR_DISPLACED": {
            "mutation": "replace the R10 row payload in MECHv0:R10_LOOSE:INSTRUMENTED with any other row",
            "diagnostic": "RUN_MATRIX_ROW_ID_MISMATCH:MECHv0:R10_LOOSE:INSTRUMENTED",
            "evidence": "BLOCKED_RUN_IDENTITY",
            "decision": "EXACT_NEIGHBOR_FREEZE_TO_BLOCKED",
        },
        "M_FREEZE_MULTIPLE_AGGREGATE_IDS_REMOVED": {
            "mutation": "delete supported_mechanism_ids from a MULTIPLE_SUPPORTED_MECHANISMS result",
            "diagnostic": "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING",
            "evidence": "RESULT_INVALID",
            "decision": "MULTIPLE_SUPPORTED_MECHANISMS_TO_REJECTED_RESULT",
        },
        "M_FREEZE_SUPPORTED_IDENTITY_SET_MISMATCH": {
            "mutation": "replace ordered supported_mechanism_ids with a set inconsistent with individual decisions",
            "diagnostic": "SUPPORTED_MECHANISM_IDENTITY_SET_MISMATCH",
            "evidence": "RESULT_INVALID",
            "decision": "SUPPORTED_RESULT_TO_REJECTED_RESULT",
        },
        "M_FREEZE_H_D_WITHOUT_POSITIVE_EVIDENCE": {
            "mutation": "mark H_D SUPPORTED while one or more H_D necessary criteria are FAILED",
            "diagnostic": "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR_AWARDED_WITHOUT_POSITIVE_EVIDENCE",
            "evidence": "RESULT_INVALID",
            "decision": "H_D_SUPPORTED_TO_REJECTED_RESULT",
        },
        "M_FREEZE_H_E_WITH_MISSING_OBSERVABLE": {
            "mutation": "after required_observables_complete=false blocks evidence, illegally mark H_E SUPPORTED and label the aggregate unresolved",
            "diagnostic": "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED",
            "evidence": "RESULT_INVALID",
            "decision": "ILLEGAL_H_E_UNRESOLVED_TO_REJECTED_RESULT",
        },
        "M_FREEZE_CLASSIFICATION_AFTER_NONPERTURBATION_FAILURE": {
            "mutation": "after instrumentation_nonperturbation_passed=false blocks evidence, illegally mark one physical hypothesis SUPPORTED",
            "diagnostic": "CLASSIFICATION_PERFORMED_AFTER_EVIDENCE_BLOCK",
            "evidence": "RESULT_INVALID",
            "decision": "POST_BLOCK_CLASSIFICATION_TO_REJECTED_RESULT",
        },
        "M_FREEZE_CONTINUUM_OPERATOR_SUBSTITUTED": {
            "mutation": "set discrete_operator_binding_passed false after substituting a continuum operator",
            "diagnostic": "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
            "evidence": "BLOCKED_OPERATOR_BINDING",
            "decision": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
        "M_FREEZE_OUTPUT_ROOT_COLLIDES_CANONICAL": {
            "mutation": "set the future experiment output root equal to or inside the canonical output root",
            "diagnostic": "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL",
            "evidence": "BLOCKED_CUSTODY",
            "decision": "SEPARATE_OUTPUT_CUSTODY_TO_BLOCKED",
        },
        "M_FREEZE_TRAJECTORY_BYTE_MISMATCH": {
            "mutation": "change one packed float64 state byte in one instrumented trajectory only",
            "diagnostic": "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL",
            "evidence": "BLOCKED_INSTRUMENTATION_PERTURBATION",
            "decision": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; no fallback equivalence",
        },
        "M_FREEZE_OBSERVABLE_UNITS_OR_NORMALIZATION_MISSING": {
            "mutation": "remove one required unit, normalization scale, floor, or aggregation binding",
            "diagnostic": "OBSERVABLE_UNIT_OR_NORMALIZATION_INVALID",
            "evidence": "BLOCKED_OBSERVABLE_SEMANTICS",
            "decision": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
        "M_FREEZE_UNKNOWN_OR_DUPLICATE_RUN_ID": {
            "mutation": "replace one expected run ID with an unknown ID or duplicate an earlier expected run ID",
            "diagnostic": {
                "DUPLICATE_RUN_ID": "DUPLICATE_RUN_IDENTITY",
                "UNKNOWN_RUN_ID": "EXPECTED_RUN_ID_CLOSURE_MISMATCH",
            },
            "evidence": "BLOCKED_RUN_IDENTITY",
            "decision": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
    }
    records = {
        record["control_id"]: record
        for record in contract.FULL_ADVERSARIAL_REGISTRY_V1
        if record["category"] == "PRESERVED_V0_REGISTERED_CONTROL"
    }
    assert set(records) == set(expected)
    for control_id, expected_record in expected.items():
        record = records[control_id]
        assert record["mutation"] == expected_record["mutation"]
        assert "preserve the exact v0 registered mutation semantics" not in record[
            "mutation"
        ].casefold()
        diagnostic = record.get(
            "expected_first_diagnostic",
            record.get("expected_first_diagnostic_by_variant"),
        )
        assert diagnostic == expected_record["diagnostic"]
        assert record["expected_evidence_result"] == expected_record["evidence"]
        assert record["expected_decision_change"] == expected_record["decision"]
