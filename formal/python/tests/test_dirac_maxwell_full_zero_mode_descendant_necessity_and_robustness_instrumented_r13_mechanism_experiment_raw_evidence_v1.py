from __future__ import annotations

import inspect
from pathlib import Path

import numpy as np

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v1
    as classifier,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v1
    as assembler,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def _block_summary(block_id: str = "PHI2_KINEMATIC") -> dict:
    shares = {name: 0.1 for name in assembler.BLOCK_IDS}
    shares[block_id] = 0.3
    return {
        "dominant_block_id": block_id,
        "median_dominance_share": shares[block_id],
        "dominant_step_fraction": 1.0,
        "median_share_by_block": shares,
        "sample_count": 16,
    }


def _closure(value: float, consecutive: int) -> dict:
    return {
        "max_relative_path_mismatch": value,
        "maximum_consecutive_mismatch_steps": consecutive,
        "sample_count": 16,
        "legacy_q_used": False,
        "mechanism_path_sources_independent": True,
    }


def _distributed(value: float) -> dict:
    return {
        "distributed_step_fraction": value,
        "linked_series_maxima_at_final_count": 0,
        "minimum_nondecreasing_increment_count": 0,
        "sample_count": 16,
        "linked_series_count": 4,
    }


def _assembled(*, support_a: bool, support_c: bool) -> assembler.AssembledRawEvidence:
    exchange = {
        "R13_LOOSE": {
            "median_kappa": 1.0e7 if support_a else 1.0,
            "severe_step_fraction": 1.0 if support_a else 0.0,
            "sample_count": 16,
        },
        "R13_TIGHT": {"median_kappa": 1.0e5 if support_a else 1.0},
        "R10_LOOSE_NEIGHBOR": {
            "median_kappa": 1.0e5 if support_a else 1.0
        },
    }
    closure = {
        "R13_LOOSE": _closure(0.20 if support_c else 0.0, 2 if support_c else 0),
        "R13_TIGHT": _closure(0.01 if support_c else 0.0, 0),
        "R10_LOOSE_NEIGHBOR": _closure(0.05 if support_c else 0.0, 0),
    }
    return assembler.AssembledRawEvidence(
        assembler_id=assembler.ASSEMBLER_ID,
        run_ids=assembler.EXPECTED_RUN_IDS,
        payload_identity_ids=tuple(f"payload-{index}" for index in range(12)),
        payloads_by_run_id={},
        recomputed_metrics={
            "exchange_conditioning": exchange,
            "block_dominance": {
                role: _block_summary() for role in classifier.ROLE_KEYS
            },
            "independent_discrete_closure": closure,
            "distributed_accumulation": {
                role: _distributed(0.0) for role in classifier.ROLE_KEYS
            },
        },
        nonperturbation_pairs=(),
        canonical_tree_sha256="0" * 64,
        review_anchor_sha256="1" * 64,
        scientific_input_closure_digest="2" * 64,
        raw_evidence_ids=("raw",),
        supplied_summary_disposition="IGNORED",
        semantic_contract_id=classifier.semantic_v1.CONTRACT_ID,
    )


def test_public_classifier_is_path_closed() -> None:
    signature = inspect.signature(classifier.classify_from_raw_payloads)
    assert tuple(signature.parameters) == ("repo_root",)
    assert tuple(inspect.signature(assembler.assemble_raw_evidence).parameters) == (
        "repo_root",
    )
    assert not hasattr(classifier, "classify")


def test_independent_current_disagreement_is_h_c_evidence_not_a_gate() -> None:
    zeros = np.zeros(assembler.LATTICE_SIZE, dtype=np.float64)
    zero_spinor = np.zeros((assembler.LATTICE_SIZE, 4), dtype=np.complex128)
    state = {
        "theta": zeros.copy(),
        "p": zeros.copy(),
        "phi2": zeros.copy(),
        "P2": zeros.copy(),
        "phi3": zeros.copy(),
        "P3": zeros.copy(),
        "psi_plus": zero_spinor.copy(),
        "psi_minus": zero_spinor.copy(),
    }
    registered = np.ones(assembler.LATTICE_SIZE, dtype=np.float64)
    spacing = 1.0 / assembler.LATTICE_SIZE
    forward = assembler._expected_forward_wilson_matrix(spacing)
    outputs = {
        "time_centered_theta": zeros.copy(),
        "backward_shift_p_previous": zeros.copy(),
        "backward_shift_p_current": zeros.copy(),
        "backward_shift_grad_theta_midpoint": registered.copy(),
        "grad_theta_midpoint_registered": registered.copy(),
        "forward_wilson_matrix": forward.copy(),
        "wilson_r": 1.0,
        "periodic_shift_rule": "NUMPY_ROLL_AXIS0",
        "time_centering_rule": "ARITHMETIC_MIDPOINT",
        "grad_theta_midpoint_recomputed": zeros.copy(),
        "grad_theta_recomputation_byte_identical": False,
    }
    for species in ("psi_plus", "psi_minus"):
        outputs[f"{species}_next_periodic"] = zero_spinor.copy()
        outputs[f"{species}_gauge_phase"] = np.ones(
            assembler.LATTICE_SIZE, dtype=np.complex128
        )
        outputs[f"{species}_forward_transport"] = zero_spinor.copy()
        outputs[f"{species}_link_bilinear"] = np.zeros(
            assembler.LATTICE_SIZE, dtype=np.complex128
        )
        outputs[f"{species}_grad_contribution"] = zeros.copy()
    independent = assembler._validate_operator_outputs(
        outputs,
        {
            "p_previous": zeros.copy(),
            "p_current": zeros.copy(),
            "rho_previous": zeros.copy(),
            "rho_current": zeros.copy(),
            "grad_theta_midpoint": registered.copy(),
        },
        state,
        state,
        0.8,
        spacing,
        1,
    )
    assert np.array_equal(independent, zeros)
    assert not np.array_equal(independent, registered)


def test_missing_execution_evidence_blocks_before_every_hypothesis() -> None:
    result = classifier.classify_from_raw_payloads(REPO_ROOT)
    assert result["aggregate_mechanism_result"] == "BLOCKED"
    assert result["supported_mechanism_ids"] == []
    assert all(
        decision["status"] == "NOT_EVALUATED"
        for decision in result["hypothesis_decisions"].values()
    )


def test_multiple_supported_mechanism_identities_are_preserved() -> None:
    result = classifier._classify_assembled(_assembled(support_a=True, support_c=True))
    assert result["evidence_result"] == "EVIDENCE_ADMISSIBLE"
    assert result["supported_mechanism_ids"] == [
        classifier.HYPOTHESES_A_TO_D[0],
        classifier.HYPOTHESES_A_TO_D[2],
    ]
    assert result["aggregate_mechanism_result"] == "MULTIPLE_SUPPORTED_MECHANISMS"
    assert result["hypothesis_decisions"][classifier.H_E]["status"] == "NOT_SUPPORTED"


def test_h_e_requires_complete_assembled_evidence_and_empty_support_set() -> None:
    result = classifier._classify_assembled(_assembled(support_a=False, support_c=False))
    assert result["evidence_result"] == "EVIDENCE_ADMISSIBLE"
    assert result["supported_mechanism_ids"] == []
    assert result["aggregate_mechanism_result"] == "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    assert result["hypothesis_decisions"][classifier.H_E]["status"] == "SUPPORTED"


def test_support_constants_and_provenance_are_one_to_one() -> None:
    leaves = {
        (hypothesis, constant_id)
        for hypothesis, values in classifier.SUPPORT_CONSTANTS.items()
        for constant_id in values
    }
    provenance = {
        (record["hypothesis"], record["constant_id"])
        for record in classifier.SUPPORT_CONSTANT_PROVENANCE
    }
    assert len(leaves) == 23
    assert provenance == leaves


def test_module_self_validation_is_green() -> None:
    assert all(assembler.self_validate().values())
    assert all(classifier.self_validate().values())
