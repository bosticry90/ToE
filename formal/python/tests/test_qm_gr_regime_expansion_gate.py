from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
QM_FULL_DERIVATION_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md"
)
GR_CONTINUUM_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md"
)
GR_STRONG_FIELD_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR_STRONG_FIELD_REGIME_v0.md"
)
QM_GR_CROSS_LANE_BUNDLE_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "QM_GR_CROSS_LANE_COMPATIBILITY_BUNDLE_v0.md"
)
QM_FULL_DERIVATION_LEAN_SCAFFOLD_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "QMFullDerivationScaffold.lean"
)
GR_CONTINUUM_CYCLE1_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_continuum_refinement_trend_cycle1_v0.json"
)
GR_CONTINUUM_CYCLE2_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_continuum_grid_independence_cycle2_v0.json"
)
GR_CONTINUUM_CYCLE3_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_continuum_bridge_theorem_surface_cycle3_v0.json"
)
GR_STRONG_FIELD_CYCLE1_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_strong_field_regime_predicate_cycle1_v0.json"
)
GR_STRONG_FIELD_CYCLE2_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_strong_field_nonlinear_closure_cycle2_v0.json"
)
GR_STRONG_FIELD_CYCLE3_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_strong_field_theorem_surface_cycle3_v0.json"
)
QM_GR_CROSS_LANE_CYCLE1_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_gr_cross_lane_compatibility_cycle1_v0.json"
)
QM_GR_CROSS_LANE_CYCLE2_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_gr_cross_lane_compatibility_cycle2_v0.json"
)
QM_GR_CROSS_LANE_CYCLE3_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_gr_cross_lane_compatibility_cycle3_v0.json"
)
QM_FULL_DERIVATION_CRITERIA_CYCLE10_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_full_derivation_discharge_criteria_cycle10_v0.json"
)
GR_CONTINUUM_CRITERIA_CYCLE10_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_continuum_discharge_criteria_cycle10_v0.json"
)
GR_STRONG_FIELD_CRITERIA_CYCLE10_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr_strong_field_discharge_criteria_cycle10_v0.json"
)
QM_GR_INTEGRATED_CRITERIA_CYCLE10_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_gr_integrated_discharge_criteria_cycle10_v0.json"
)
QM_FULL_DERIVATION_EXIT_COVERAGE_CYCLE14_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_full_derivation_exit_criteria_coverage_cycle14_v0.json"
)
QM_FULL_DERIVATION_PREDISCHARGE_GATE_CYCLE19_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_full_derivation_predischarge_gate_cycle19_v0.json"
)
QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_CYCLE20_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_full_derivation_discharge_transition_bundle_cycle20_v0.json"
)
QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_CYCLE21_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_full_derivation_keyb_policy_signoff_cycle21_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token_value(text: str, token_label: str) -> str:
    m = re.search(rf"{re.escape(token_label)}:\s*([^\n`]+)", text)
    assert m is not None, f"Missing token: {token_label}"
    return m.group(1).strip()


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_qm_full_derivation_target_is_pinned_with_required_boundaries() -> None:
    text = _read(QM_FULL_DERIVATION_TARGET_PATH)
    lean_scaffold_text = _read(QM_FULL_DERIVATION_LEAN_SCAFFOLD_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0",
        "TARGET-QM-FULL-DERIVATION-DISCHARGE-v0",
        "QM_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0_DERIVATION_GRADE",
        "QM_FULL_DERIVATION_PROGRESS_v0: CYCLE1_CONTRACT_BRIDGE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE2_v0: UNITARY_CONSISTENCY_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE3_v0: ANTI_CIRCULARITY_GUARD_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE4_v0: COMPOSITION_BUNDLE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE5_v0: ASSUMPTION_MINIMIZATION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE6_v0: EXIT_CRITERIA_COVERAGE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE7_v0: UNITARY_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE8_v0: DERIVATION_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE9_v0: ANTICIRCULARITY_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE10_v0: ASSUMPTION_MINIMIZATION_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE11_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE12_v0: DISCHARGE_TRANSITION_BUNDLE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE13_v0: KEYB_POLICY_SIGNOFF_SURFACE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE14_v0: TWO_KEY_RELEASE_DISCHARGE_COMPLETED",
        "QM_FULL_DERIVATION_RECLASSIFICATION_v0_MIN1: hStepTotalPolicy_POLICY_TO_MATH_via_qm_step_total_of_definition",
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "QM_FULL_DERIVATION_CRITERIA_ROW_01_v0: EVOLUTION_LAW_DERIVATION_CHAIN_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_01_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_02_v0: UNITARY_CONSISTENCY_CHAIN_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_02_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle6_unitary_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_03_v0: ANTI_CIRCULARITY_GUARD_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_04_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle8_anticircularity_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_04_v0: ASSUMPTION_MINIMIZATION_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_03_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_05_v0: STATE_GATE_SYNC_PINNED",
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_v0: qm_full_derivation_discharge_criteria_cycle10_v0",
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/qm_full_derivation_discharge_criteria_cycle10_v0.json",
        "QM_FULL_DERIVATION_EXIT_CRITERIA_COVERAGE_ARTIFACT_v0: qm_full_derivation_exit_criteria_coverage_cycle14_v0",
        "formal/output/qm_full_derivation_exit_criteria_coverage_cycle14_v0.json",
        "QM_FULL_DERIVATION_PREDISCHARGE_GATE_ARTIFACT_v0: qm_full_derivation_predischarge_gate_cycle19_v0",
        "formal/output/qm_full_derivation_predischarge_gate_cycle19_v0.json",
        "QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0: qm_full_derivation_discharge_transition_bundle_cycle20_v0",
        "formal/output/qm_full_derivation_discharge_transition_bundle_cycle20_v0.json",
        "QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_ARTIFACT_v0: qm_full_derivation_keyb_policy_signoff_cycle21_v0",
        "formal/output/qm_full_derivation_keyb_policy_signoff_cycle21_v0.json",
        "TARGET-QM-FULL-MICRO-01-CONTRACT-BRIDGE-v0",
        "TARGET-QM-FULL-MICRO-02-UNITARY-CONSISTENCY-v0",
        "TARGET-QM-FULL-MICRO-03-ANTI-CIRCULARITY-GUARD-v0",
        "TARGET-QM-FULL-MICRO-04-COMPOSITION-BUNDLE-v0",
        "TARGET-QM-FULL-MICRO-05-ASSUMPTION-MINIMIZATION-v0",
        "qm_full_derivation_cycle1_contract_bridge_token_v0",
        "qm_full_derivation_cycle2_unitary_consistency_token_v0",
        "qm_full_derivation_cycle3_no_direct_schrodinger_insertion_guard_v0",
        "qm_full_derivation_cycle4_composition_bundle_token_v0",
        "qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0",
        "QM_ANTI_CIRCULARITY_GUARD_v0: NO_DIRECT_SCHRODINGER_INSERTION",
        "QM_FORBIDDEN_DIRECT_SCHRODINGER_INSERTION_v0",
        "no claim of completed Schrodinger derivation",
        "no claim of completed unitary recovery",
        "Evolution-law derivation track",
        "Unitary-consistency track",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required QM full-derivation target token(s): " + ", ".join(missing)

    for token in [
        "theorem qm_full_derivation_cycle1_contract_bridge_token_v0",
        "theorem qm_full_derivation_cycle2_unitary_consistency_token_v0",
        "theorem qm_full_derivation_cycle3_no_direct_schrodinger_insertion_guard_v0",
        "theorem qm_full_derivation_cycle4_composition_bundle_token_v0",
        "theorem qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0",
        "theorem qm_full_derivation_cycle6_unitary_exit_row_closure_token_v0",
        "theorem qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0",
        "theorem qm_full_derivation_cycle8_anticircularity_exit_row_closure_token_v0",
        "theorem qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0",
        "QMUnitaryConsistencyWitnessUnderContract",
        "QMAntiCircularityGuardNoDirectSchrodingerInsertion",
        "QMFullDerivationCycle4Bundle",
        "QMEvolutionOperatorStepTotal",
        "qm_step_total_of_definition",
        "QMEvolutionAssumptions_v0_min1",
        "QMStateEvolvesUnderContract",
    ]:
        assert token in lean_scaffold_text, f"Missing QM full-derivation scaffold token: {token}"

    assert "QM_FORBIDDEN_DIRECT_SCHRODINGER_INSERTION_v0" not in lean_scaffold_text, (
        "Forbidden direct Schrodinger insertion token leaked into Lean scaffold."
    )


def test_gr_continuum_target_is_pinned_with_required_boundaries() -> None:
    text = _read(GR_CONTINUUM_TARGET_PATH)
    required_tokens = [
        "DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0",
        "TARGET-GR-CONTINUUM-LIMIT-BRIDGE-v0",
        "GR_CONTINUUM_LIMIT_ADJUDICATION: NOT_YET_DISCHARGED_v0",
        "GR_CONTINUUM_LIMIT_PROGRESS_v0: CYCLE1_REFINEMENT_TREND_TOKEN_PINNED",
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE2_v0: GRID_INDEPENDENCE_SANITY_TOKEN_PINNED",
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE3_v0: BRIDGE_THEOREM_SURFACE_TOKEN_PINNED",
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_01_v0: REFINEMENT_TREND_MONOTONIC_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_02_v0: DISCRETE_TO_CONTINUUM_MAP_SURFACE_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_03_v0: BOUNDARY_ASSUMPTION_TRANSPARENCY_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_04_v0: STATE_GATE_SYNC_PINNED",
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_v0: gr_continuum_discharge_criteria_cycle10_v0",
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/gr_continuum_discharge_criteria_cycle10_v0.json",
        "TARGET-GR-CONTINUUM-MICRO-01-REFINEMENT-TREND-v0",
        "gr_continuum_refinement_trend_cycle1_v0",
        "formal/output/gr_continuum_refinement_trend_cycle1_v0.json",
        "TARGET-GR-CONTINUUM-MICRO-02-GRID-INDEPENDENCE-SANITY-v0",
        "gr_continuum_grid_independence_cycle2_v0",
        "formal/output/gr_continuum_grid_independence_cycle2_v0.json",
        "TARGET-GR-CONTINUUM-MICRO-03-BRIDGE-THEOREM-SURFACE-v0",
        "gr_continuum_bridge_theorem_surface_cycle3_v0",
        "formal/output/gr_continuum_bridge_theorem_surface_cycle3_v0.json",
        "no claim of completed continuum-limit theorem",
        "no infinite-domain uniqueness claim",
        "Refinement consistency track",
        "Grid-independence sanity track",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required GR continuum target token(s): " + ", ".join(missing)


def test_gr_strong_field_target_is_pinned_with_required_boundaries() -> None:
    text = _read(GR_STRONG_FIELD_TARGET_PATH)
    required_tokens = [
        "DERIVATION_TARGET_GR_STRONG_FIELD_REGIME_v0",
        "TARGET-GR-STRONG-FIELD-REGIME-v0",
        "GR_STRONG_FIELD_ADJUDICATION: NOT_YET_DISCHARGED_v0",
        "GR_STRONG_FIELD_PROGRESS_v0: CYCLE1_REGIME_PREDICATE_TOKEN_PINNED",
        "GR_STRONG_FIELD_PROGRESS_CYCLE2_v0: NONLINEAR_CLOSURE_SCAFFOLD_TOKEN_PINNED",
        "GR_STRONG_FIELD_PROGRESS_CYCLE3_v0: STRONG_FIELD_THEOREM_SURFACE_TOKEN_PINNED",
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_01_v0: REGIME_PREDICATE_SURFACE_PINNED",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_02_v0: NONLINEAR_CLOSURE_SURFACE_PINNED",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_03_v0: REGULARITY_DOMAIN_BOUNDARY_PINNED",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_04_v0: STATE_GATE_SYNC_PINNED",
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_v0: gr_strong_field_discharge_criteria_cycle10_v0",
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/gr_strong_field_discharge_criteria_cycle10_v0.json",
        "TARGET-GR-STRONG-FIELD-MICRO-01-REGIME-PREDICATE-v0",
        "gr_strong_field_regime_predicate_cycle1_v0",
        "formal/output/gr_strong_field_regime_predicate_cycle1_v0.json",
        "TARGET-GR-STRONG-FIELD-MICRO-02-NONLINEAR-CLOSURE-SCAFFOLD-v0",
        "gr_strong_field_nonlinear_closure_cycle2_v0",
        "formal/output/gr_strong_field_nonlinear_closure_cycle2_v0.json",
        "TARGET-GR-STRONG-FIELD-MICRO-03-THEOREM-SURFACE-v0",
        "gr_strong_field_theorem_surface_cycle3_v0",
        "formal/output/gr_strong_field_theorem_surface_cycle3_v0.json",
        "no claim of completed full-Einstein strong-field recovery",
        "no black-hole uniqueness theorem claim",
        "Strong-field regime object track",
        "Nonlinear closure track",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required GR strong-field target token(s): " + ", ".join(missing)


def test_expansion_targets_are_synchronized_in_state() -> None:
    state_text = _read(STATE_PATH)
    qm_target_text = _read(QM_FULL_DERIVATION_TARGET_PATH)
    cont_target_text = _read(GR_CONTINUUM_TARGET_PATH)
    strong_target_text = _read(GR_STRONG_FIELD_TARGET_PATH)
    cross_lane_bundle_text = _read(QM_GR_CROSS_LANE_BUNDLE_PATH)

    expected_tokens = [
        "QM_FULL_DERIVATION_ADJUDICATION",
        "QM_FULL_DERIVATION_PROGRESS_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE2_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE3_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE4_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE5_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE6_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE7_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE8_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE9_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE10_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE11_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE12_v0",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE13_v0",
        "QM_FULL_DERIVATION_RECLASSIFICATION_v0_MIN1",
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_01_v0: EVOLUTION_LAW_DERIVATION_CHAIN_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_01_STATUS_v0",
        "qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_02_v0: UNITARY_CONSISTENCY_CHAIN_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_02_STATUS_v0",
        "qm_full_derivation_cycle6_unitary_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_03_v0: ANTI_CIRCULARITY_GUARD_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_04_STATUS_v0",
        "qm_full_derivation_cycle8_anticircularity_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_04_v0: ASSUMPTION_MINIMIZATION_PINNED",
        "QM_FULL_DERIVATION_EXIT_ROW_03_STATUS_v0",
        "qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_05_v0: STATE_GATE_SYNC_PINNED",
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_v0",
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/qm_full_derivation_discharge_criteria_cycle10_v0.json",
        "QM_FULL_DERIVATION_EXIT_CRITERIA_COVERAGE_ARTIFACT_v0",
        "formal/output/qm_full_derivation_exit_criteria_coverage_cycle14_v0.json",
        "QM_FULL_DERIVATION_PREDISCHARGE_GATE_ARTIFACT_v0",
        "formal/output/qm_full_derivation_predischarge_gate_cycle19_v0.json",
        "QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0",
        "formal/output/qm_full_derivation_discharge_transition_bundle_cycle20_v0.json",
        "QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_ARTIFACT_v0",
        "formal/output/qm_full_derivation_keyb_policy_signoff_cycle21_v0.json",
        "QM_ANTI_CIRCULARITY_GUARD_v0",
        "GR_CONTINUUM_LIMIT_ADJUDICATION",
        "GR_CONTINUUM_LIMIT_PROGRESS_v0",
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE2_v0",
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE3_v0",
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_v0",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_01_v0: REFINEMENT_TREND_MONOTONIC_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_02_v0: DISCRETE_TO_CONTINUUM_MAP_SURFACE_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_03_v0: BOUNDARY_ASSUMPTION_TRANSPARENCY_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_04_v0: STATE_GATE_SYNC_PINNED",
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_v0",
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/gr_continuum_discharge_criteria_cycle10_v0.json",
        "GR_STRONG_FIELD_ADJUDICATION",
        "GR_STRONG_FIELD_PROGRESS_v0",
        "GR_STRONG_FIELD_PROGRESS_CYCLE2_v0",
        "GR_STRONG_FIELD_PROGRESS_CYCLE3_v0",
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_v0",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_01_v0: REGIME_PREDICATE_SURFACE_PINNED",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_02_v0: NONLINEAR_CLOSURE_SURFACE_PINNED",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_03_v0: REGULARITY_DOMAIN_BOUNDARY_PINNED",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_04_v0: STATE_GATE_SYNC_PINNED",
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_v0",
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/gr_strong_field_discharge_criteria_cycle10_v0.json",
        "QM_GR_CROSS_LANE_PROGRESS_v0",
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE2_v0",
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE3_v0",
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_v0",
        "QM_GR_INTEGRATED_CRITERIA_ROW_01_v0: LANE_CHECKPOINT_COMPATIBILITY_PINNED",
        "QM_GR_INTEGRATED_CRITERIA_ROW_02_v0: EXPLICIT_NON_CLAIM_POSTURE_PINNED",
        "QM_GR_INTEGRATED_CRITERIA_ROW_03_v0: STATE_GATE_SYNC_PINNED",
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_v0",
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/qm_gr_integrated_discharge_criteria_cycle10_v0.json",
    ]
    for token in expected_tokens:
        assert token in state_text, f"Missing expansion token in state: {token}"

    state_qm = _extract_token_value(state_text, "QM_FULL_DERIVATION_ADJUDICATION")
    state_qm_progress = _extract_token_value(state_text, "QM_FULL_DERIVATION_PROGRESS_v0")
    state_qm_progress_cycle2 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE2_v0",
    )
    state_qm_progress_cycle3 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE3_v0",
    )
    state_qm_progress_cycle4 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE4_v0",
    )
    state_qm_progress_cycle5 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE5_v0",
    )
    state_qm_progress_cycle6 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE6_v0",
    )
    state_qm_progress_cycle7 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE7_v0",
    )
    state_qm_progress_cycle8 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE8_v0",
    )
    state_qm_progress_cycle9 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE9_v0",
    )
    state_qm_progress_cycle10 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE10_v0",
    )
    state_qm_progress_cycle11 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE11_v0",
    )
    state_qm_progress_cycle12 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE12_v0",
    )
    state_qm_progress_cycle13 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE13_v0",
    )
    state_qm_progress_cycle14 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE14_v0",
    )
    state_qm_reclass = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_RECLASSIFICATION_v0_MIN1",
    )
    state_qm_discharge_criteria = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_v0",
    )
    state_qm_criteria_artifact = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    state_qm_exit_coverage_artifact = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_EXIT_CRITERIA_COVERAGE_ARTIFACT_v0",
    )
    state_qm_predischarge_gate_artifact = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_PREDISCHARGE_GATE_ARTIFACT_v0",
    )
    state_qm_discharge_transition_bundle_artifact = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0",
    )
    state_qm_keyb_policy_signoff_artifact = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_ARTIFACT_v0",
    )
    state_qm_exit_row02_status = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_EXIT_ROW_02_STATUS_v0",
    )
    state_qm_exit_row01_status = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_EXIT_ROW_01_STATUS_v0",
    )
    state_qm_exit_row04_status = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_EXIT_ROW_04_STATUS_v0",
    )
    state_qm_exit_row03_status = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_EXIT_ROW_03_STATUS_v0",
    )
    state_qm_criteria_artifact_sha256 = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    state_qm_guard = _extract_token_value(
        state_text,
        "QM_ANTI_CIRCULARITY_GUARD_v0",
    )
    state_cont = _extract_token_value(state_text, "GR_CONTINUUM_LIMIT_ADJUDICATION")
    state_cont_progress = _extract_token_value(state_text, "GR_CONTINUUM_LIMIT_PROGRESS_v0")
    state_cont_progress_cycle2 = _extract_token_value(
        state_text,
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE2_v0",
    )
    state_cont_progress_cycle3 = _extract_token_value(
        state_text,
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE3_v0",
    )
    state_cont_discharge_criteria = _extract_token_value(
        state_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_v0",
    )
    state_cont_criteria_artifact = _extract_token_value(
        state_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    state_cont_criteria_artifact_sha256 = _extract_token_value(
        state_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    state_strong = _extract_token_value(state_text, "GR_STRONG_FIELD_ADJUDICATION")
    state_strong_progress = _extract_token_value(state_text, "GR_STRONG_FIELD_PROGRESS_v0")
    state_strong_progress_cycle2 = _extract_token_value(
        state_text,
        "GR_STRONG_FIELD_PROGRESS_CYCLE2_v0",
    )
    state_strong_progress_cycle3 = _extract_token_value(
        state_text,
        "GR_STRONG_FIELD_PROGRESS_CYCLE3_v0",
    )
    state_strong_discharge_criteria = _extract_token_value(
        state_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_v0",
    )
    state_strong_criteria_artifact = _extract_token_value(
        state_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    state_strong_criteria_artifact_sha256 = _extract_token_value(
        state_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    state_cross_lane_progress = _extract_token_value(
        state_text,
        "QM_GR_CROSS_LANE_PROGRESS_v0",
    )
    state_cross_lane_progress_cycle2 = _extract_token_value(
        state_text,
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE2_v0",
    )
    state_cross_lane_progress_cycle3 = _extract_token_value(
        state_text,
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE3_v0",
    )
    state_cross_lane_discharge_criteria = _extract_token_value(
        state_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_v0",
    )
    state_cross_lane_criteria_artifact = _extract_token_value(
        state_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    state_cross_lane_criteria_artifact_sha256 = _extract_token_value(
        state_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )

    target_qm = _extract_token_value(qm_target_text, "QM_FULL_DERIVATION_ADJUDICATION")
    target_qm_progress = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_v0",
    )
    target_qm_progress_cycle2 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE2_v0",
    )
    target_qm_progress_cycle3 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE3_v0",
    )
    target_qm_progress_cycle4 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE4_v0",
    )
    target_qm_progress_cycle5 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE5_v0",
    )
    target_qm_progress_cycle6 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE6_v0",
    )
    target_qm_progress_cycle7 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE7_v0",
    )
    target_qm_progress_cycle8 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE8_v0",
    )
    target_qm_progress_cycle9 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE9_v0",
    )
    target_qm_progress_cycle10 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE10_v0",
    )
    target_qm_progress_cycle11 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE11_v0",
    )
    target_qm_progress_cycle12 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE12_v0",
    )
    target_qm_progress_cycle13 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE13_v0",
    )
    target_qm_progress_cycle14 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PROGRESS_CYCLE14_v0",
    )
    target_qm_reclass = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_RECLASSIFICATION_v0_MIN1",
    )
    target_qm_discharge_criteria = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_v0",
    )
    target_qm_criteria_artifact = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    target_qm_exit_coverage_artifact = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_EXIT_CRITERIA_COVERAGE_ARTIFACT_v0",
    )
    target_qm_predischarge_gate_artifact = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_PREDISCHARGE_GATE_ARTIFACT_v0",
    )
    target_qm_discharge_transition_bundle_artifact = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0",
    )
    target_qm_keyb_policy_signoff_artifact = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_ARTIFACT_v0",
    )
    target_qm_exit_row02_status = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_EXIT_ROW_02_STATUS_v0",
    )
    target_qm_exit_row01_status = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_EXIT_ROW_01_STATUS_v0",
    )
    target_qm_exit_row04_status = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_EXIT_ROW_04_STATUS_v0",
    )
    target_qm_exit_row03_status = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_EXIT_ROW_03_STATUS_v0",
    )
    target_qm_criteria_artifact_sha256 = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    target_qm_guard = _extract_token_value(
        qm_target_text,
        "QM_ANTI_CIRCULARITY_GUARD_v0",
    )
    target_cont = _extract_token_value(cont_target_text, "GR_CONTINUUM_LIMIT_ADJUDICATION")
    target_cont_progress = _extract_token_value(
        cont_target_text,
        "GR_CONTINUUM_LIMIT_PROGRESS_v0",
    )
    target_cont_progress_cycle2 = _extract_token_value(
        cont_target_text,
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE2_v0",
    )
    target_cont_progress_cycle3 = _extract_token_value(
        cont_target_text,
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE3_v0",
    )
    target_cont_discharge_criteria = _extract_token_value(
        cont_target_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_v0",
    )
    target_cont_criteria_artifact = _extract_token_value(
        cont_target_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    target_cont_criteria_artifact_sha256 = _extract_token_value(
        cont_target_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    target_strong = _extract_token_value(strong_target_text, "GR_STRONG_FIELD_ADJUDICATION")
    target_strong_progress = _extract_token_value(
        strong_target_text,
        "GR_STRONG_FIELD_PROGRESS_v0",
    )
    target_strong_progress_cycle2 = _extract_token_value(
        strong_target_text,
        "GR_STRONG_FIELD_PROGRESS_CYCLE2_v0",
    )
    target_strong_progress_cycle3 = _extract_token_value(
        strong_target_text,
        "GR_STRONG_FIELD_PROGRESS_CYCLE3_v0",
    )
    target_strong_discharge_criteria = _extract_token_value(
        strong_target_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_v0",
    )
    target_strong_criteria_artifact = _extract_token_value(
        strong_target_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    target_strong_criteria_artifact_sha256 = _extract_token_value(
        strong_target_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    target_cross_lane_progress = _extract_token_value(
        cross_lane_bundle_text,
        "QM_GR_CROSS_LANE_PROGRESS_v0",
    )
    target_cross_lane_progress_cycle2 = _extract_token_value(
        cross_lane_bundle_text,
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE2_v0",
    )
    target_cross_lane_progress_cycle3 = _extract_token_value(
        cross_lane_bundle_text,
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE3_v0",
    )
    target_cross_lane_discharge_criteria = _extract_token_value(
        cross_lane_bundle_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_v0",
    )
    target_cross_lane_criteria_artifact = _extract_token_value(
        cross_lane_bundle_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_v0",
    )
    target_cross_lane_criteria_artifact_sha256 = _extract_token_value(
        cross_lane_bundle_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )

    assert state_qm == target_qm, f"QM token drift: state={state_qm}, target={target_qm}"
    assert state_qm_progress == target_qm_progress, (
        f"QM progress token drift: state={state_qm_progress}, target={target_qm_progress}"
    )
    assert state_qm_progress_cycle2 == target_qm_progress_cycle2, (
        "QM cycle2 progress token drift: "
        f"state={state_qm_progress_cycle2}, target={target_qm_progress_cycle2}"
    )
    assert state_qm_progress_cycle3 == target_qm_progress_cycle3, (
        "QM cycle3 progress token drift: "
        f"state={state_qm_progress_cycle3}, target={target_qm_progress_cycle3}"
    )
    assert state_qm_progress_cycle4 == target_qm_progress_cycle4, (
        "QM cycle4 progress token drift: "
        f"state={state_qm_progress_cycle4}, target={target_qm_progress_cycle4}"
    )
    assert state_qm_progress_cycle5 == target_qm_progress_cycle5, (
        "QM cycle5 progress token drift: "
        f"state={state_qm_progress_cycle5}, target={target_qm_progress_cycle5}"
    )
    assert state_qm_progress_cycle6 == target_qm_progress_cycle6, (
        "QM cycle6 progress token drift: "
        f"state={state_qm_progress_cycle6}, target={target_qm_progress_cycle6}"
    )
    assert state_qm_progress_cycle7 == target_qm_progress_cycle7, (
        "QM cycle7 progress token drift: "
        f"state={state_qm_progress_cycle7}, target={target_qm_progress_cycle7}"
    )
    assert state_qm_progress_cycle8 == target_qm_progress_cycle8, (
        "QM cycle8 progress token drift: "
        f"state={state_qm_progress_cycle8}, target={target_qm_progress_cycle8}"
    )
    assert state_qm_progress_cycle9 == target_qm_progress_cycle9, (
        "QM cycle9 progress token drift: "
        f"state={state_qm_progress_cycle9}, target={target_qm_progress_cycle9}"
    )
    assert state_qm_progress_cycle10 == target_qm_progress_cycle10, (
        "QM cycle10 progress token drift: "
        f"state={state_qm_progress_cycle10}, target={target_qm_progress_cycle10}"
    )
    assert state_qm_progress_cycle11 == target_qm_progress_cycle11, (
        "QM cycle11 progress token drift: "
        f"state={state_qm_progress_cycle11}, target={target_qm_progress_cycle11}"
    )
    assert state_qm_progress_cycle12 == target_qm_progress_cycle12, (
        "QM cycle12 progress token drift: "
        f"state={state_qm_progress_cycle12}, target={target_qm_progress_cycle12}"
    )
    assert state_qm_progress_cycle13 == target_qm_progress_cycle13, (
        "QM cycle13 progress token drift: "
        f"state={state_qm_progress_cycle13}, target={target_qm_progress_cycle13}"
    )
    assert state_qm_progress_cycle14 == target_qm_progress_cycle14, (
        "QM cycle14 progress token drift: "
        f"state={state_qm_progress_cycle14}, target={target_qm_progress_cycle14}"
    )
    assert state_qm_reclass == target_qm_reclass, (
        f"QM reclassification token drift: state={state_qm_reclass}, target={target_qm_reclass}"
    )
    assert state_qm_discharge_criteria == target_qm_discharge_criteria, (
        "QM discharge-criteria token drift: "
        f"state={state_qm_discharge_criteria}, target={target_qm_discharge_criteria}"
    )
    assert state_qm_criteria_artifact == target_qm_criteria_artifact, (
        "QM criteria artifact token drift: "
        f"state={state_qm_criteria_artifact}, target={target_qm_criteria_artifact}"
    )
    assert state_qm_exit_coverage_artifact == target_qm_exit_coverage_artifact, (
        "QM exit-coverage artifact token drift: "
        f"state={state_qm_exit_coverage_artifact}, target={target_qm_exit_coverage_artifact}"
    )
    assert state_qm_predischarge_gate_artifact == target_qm_predischarge_gate_artifact, (
        "QM pre-discharge gate artifact token drift: "
        f"state={state_qm_predischarge_gate_artifact}, target={target_qm_predischarge_gate_artifact}"
    )
    assert (
        state_qm_discharge_transition_bundle_artifact
        == target_qm_discharge_transition_bundle_artifact
    ), (
        "QM discharge-transition bundle artifact token drift: "
        "state="
        f"{state_qm_discharge_transition_bundle_artifact}, "
        f"target={target_qm_discharge_transition_bundle_artifact}"
    )
    assert state_qm_keyb_policy_signoff_artifact == target_qm_keyb_policy_signoff_artifact, (
        "QM key-B policy-signoff artifact token drift: "
        f"state={state_qm_keyb_policy_signoff_artifact}, "
        f"target={target_qm_keyb_policy_signoff_artifact}"
    )
    assert state_qm_exit_row02_status == target_qm_exit_row02_status, (
        "QM exit-row02 status token drift: "
        f"state={state_qm_exit_row02_status}, target={target_qm_exit_row02_status}"
    )
    assert state_qm_exit_row01_status == target_qm_exit_row01_status, (
        "QM exit-row01 status token drift: "
        f"state={state_qm_exit_row01_status}, target={target_qm_exit_row01_status}"
    )
    assert state_qm_exit_row04_status == target_qm_exit_row04_status, (
        "QM exit-row04 status token drift: "
        f"state={state_qm_exit_row04_status}, target={target_qm_exit_row04_status}"
    )
    assert state_qm_exit_row03_status == target_qm_exit_row03_status, (
        "QM exit-row03 status token drift: "
        f"state={state_qm_exit_row03_status}, target={target_qm_exit_row03_status}"
    )
    assert state_qm_criteria_artifact_sha256 == target_qm_criteria_artifact_sha256, (
        "QM criteria artifact sha256 drift: "
        f"state={state_qm_criteria_artifact_sha256}, target={target_qm_criteria_artifact_sha256}"
    )
    assert state_qm_guard == target_qm_guard, (
        f"QM anti-circularity guard token drift: state={state_qm_guard}, target={target_qm_guard}"
    )
    assert state_cont == target_cont, f"Continuum token drift: state={state_cont}, target={target_cont}"
    assert state_cont_progress == target_cont_progress, (
        "Continuum progress token drift: "
        f"state={state_cont_progress}, target={target_cont_progress}"
    )
    assert state_cont_progress_cycle2 == target_cont_progress_cycle2, (
        "Continuum cycle2 progress token drift: "
        f"state={state_cont_progress_cycle2}, target={target_cont_progress_cycle2}"
    )
    assert state_cont_progress_cycle3 == target_cont_progress_cycle3, (
        "Continuum cycle3 progress token drift: "
        f"state={state_cont_progress_cycle3}, target={target_cont_progress_cycle3}"
    )
    assert state_cont_discharge_criteria == target_cont_discharge_criteria, (
        "Continuum discharge-criteria token drift: "
        f"state={state_cont_discharge_criteria}, target={target_cont_discharge_criteria}"
    )
    assert state_cont_criteria_artifact == target_cont_criteria_artifact, (
        "Continuum criteria artifact token drift: "
        f"state={state_cont_criteria_artifact}, target={target_cont_criteria_artifact}"
    )
    assert state_cont_criteria_artifact_sha256 == target_cont_criteria_artifact_sha256, (
        "Continuum criteria artifact sha256 drift: "
        f"state={state_cont_criteria_artifact_sha256}, target={target_cont_criteria_artifact_sha256}"
    )
    assert state_strong == target_strong, (
        f"Strong-field token drift: state={state_strong}, target={target_strong}"
    )
    assert state_strong_progress == target_strong_progress, (
        "Strong-field progress token drift: "
        f"state={state_strong_progress}, target={target_strong_progress}"
    )
    assert state_strong_progress_cycle2 == target_strong_progress_cycle2, (
        "Strong-field cycle2 progress token drift: "
        f"state={state_strong_progress_cycle2}, target={target_strong_progress_cycle2}"
    )
    assert state_strong_progress_cycle3 == target_strong_progress_cycle3, (
        "Strong-field cycle3 progress token drift: "
        f"state={state_strong_progress_cycle3}, target={target_strong_progress_cycle3}"
    )
    assert state_strong_discharge_criteria == target_strong_discharge_criteria, (
        "Strong-field discharge-criteria token drift: "
        f"state={state_strong_discharge_criteria}, target={target_strong_discharge_criteria}"
    )
    assert state_strong_criteria_artifact == target_strong_criteria_artifact, (
        "Strong-field criteria artifact token drift: "
        f"state={state_strong_criteria_artifact}, target={target_strong_criteria_artifact}"
    )
    assert state_strong_criteria_artifact_sha256 == target_strong_criteria_artifact_sha256, (
        "Strong-field criteria artifact sha256 drift: "
        "state="
        f"{state_strong_criteria_artifact_sha256}, target={target_strong_criteria_artifact_sha256}"
    )
    assert state_cross_lane_progress == target_cross_lane_progress, (
        "Cross-lane progress token drift: "
        f"state={state_cross_lane_progress}, target={target_cross_lane_progress}"
    )
    assert state_cross_lane_progress_cycle2 == target_cross_lane_progress_cycle2, (
        "Cross-lane cycle2 progress token drift: "
        f"state={state_cross_lane_progress_cycle2}, target={target_cross_lane_progress_cycle2}"
    )
    assert state_cross_lane_progress_cycle3 == target_cross_lane_progress_cycle3, (
        "Cross-lane cycle3 progress token drift: "
        f"state={state_cross_lane_progress_cycle3}, target={target_cross_lane_progress_cycle3}"
    )
    assert state_cross_lane_discharge_criteria == target_cross_lane_discharge_criteria, (
        "Cross-lane discharge-criteria token drift: "
        f"state={state_cross_lane_discharge_criteria}, target={target_cross_lane_discharge_criteria}"
    )
    assert state_cross_lane_criteria_artifact == target_cross_lane_criteria_artifact, (
        "Cross-lane criteria artifact token drift: "
        f"state={state_cross_lane_criteria_artifact}, target={target_cross_lane_criteria_artifact}"
    )
    assert state_cross_lane_criteria_artifact_sha256 == target_cross_lane_criteria_artifact_sha256, (
        "Cross-lane criteria artifact sha256 drift: "
        "state="
        f"{state_cross_lane_criteria_artifact_sha256}, target={target_cross_lane_criteria_artifact_sha256}"
    )


def test_gr_continuum_cycle1_refinement_artifact_is_pinned_and_monotonic() -> None:
    payload = json.loads(_read(GR_CONTINUUM_CYCLE1_ARTIFACT_PATH))

    assert payload.get("record_id") == "GR_CONTINUUM_LIMIT_BRIDGE_CYCLE1_v0"
    assert payload.get("artifact_id") == "gr_continuum_refinement_trend_cycle1_v0"
    assert payload.get("scope") == "bounded_discrete_to_continuum_bridge_v0"
    assert payload.get("grid_series") == [32, 64, 128]

    residual_series = payload.get("residual_norm_series")
    assert isinstance(residual_series, list) and len(residual_series) == 3
    r32, r64, r128 = (float(residual_series[0]), float(residual_series[1]), float(residual_series[2]))
    assert r64 <= r32, f"Continuum cycle1 trend regression: 64-grid residual {r64} > 32-grid residual {r32}."
    assert r128 <= r64, f"Continuum cycle1 trend regression: 128-grid residual {r128} > 64-grid residual {r64}."

    assert payload.get("trend_label") == "nonincreasing_residual_under_refinement"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_gr_strong_field_cycle1_regime_artifact_is_pinned_and_well_formed() -> None:
    payload = json.loads(_read(GR_STRONG_FIELD_CYCLE1_ARTIFACT_PATH))

    assert payload.get("record_id") == "GR_STRONG_FIELD_REGIME_CYCLE1_v0"
    assert payload.get("artifact_id") == "gr_strong_field_regime_predicate_cycle1_v0"
    assert payload.get("scope") == "bounded_strong_field_program_v0"
    assert payload.get("regime_predicate_id") == "GR_STRONG_FIELD_REGIME_PREDICATE_v0"

    assumptions = payload.get("assumptions")
    assert isinstance(assumptions, dict)
    assert assumptions.get("curvature_intensity") == "high_but_bounded"
    assert assumptions.get("domain_regularization") == "explicit_bounded_domain"
    assert assumptions.get("singularity_posture") == "excluded_in_v0_cycle1"

    assert payload.get("compatibility_posture") == "weak_field_bridge_preserved"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_gr_continuum_cycle2_grid_independence_artifact_is_pinned_and_well_formed() -> None:
    payload = json.loads(_read(GR_CONTINUUM_CYCLE2_ARTIFACT_PATH))

    assert payload.get("record_id") == "GR_CONTINUUM_LIMIT_BRIDGE_CYCLE2_v0"
    assert payload.get("artifact_id") == "gr_continuum_grid_independence_cycle2_v0"
    assert payload.get("scope") == "bounded_discrete_to_continuum_bridge_v0"

    encodings = payload.get("encodings")
    assert isinstance(encodings, list) and len(encodings) >= 3

    residuals = payload.get("residual_norm_by_encoding")
    assert isinstance(residuals, dict) and len(residuals) >= 3
    tolerance = float(payload.get("tolerance"))
    values = [float(v) for v in residuals.values()]
    assert max(values) - min(values) <= tolerance

    assert payload.get("independence_summary") == "within_v0_grid_independence_tolerance"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_gr_strong_field_cycle2_nonlinear_closure_artifact_is_pinned_and_well_formed() -> None:
    payload = json.loads(_read(GR_STRONG_FIELD_CYCLE2_ARTIFACT_PATH))

    assert payload.get("record_id") == "GR_STRONG_FIELD_REGIME_CYCLE2_v0"
    assert payload.get("artifact_id") == "gr_strong_field_nonlinear_closure_cycle2_v0"
    assert payload.get("scope") == "bounded_strong_field_program_v0"
    assert payload.get("closure_surface_id") == "GR_STRONG_FIELD_NONLINEAR_CLOSURE_SURFACE_v0"

    residual_family = payload.get("residual_family")
    assert isinstance(residual_family, list) and len(residual_family) >= 2
    assumptions = payload.get("assumptions")
    assert isinstance(assumptions, dict)
    assert assumptions.get("weak_field_compatibility_hook") == "preserved"

    assert payload.get("closure_posture") == "scaffold_pinned_not_yet_discharged"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_gr_continuum_cycle3_bridge_theorem_surface_artifact_is_pinned_and_well_formed() -> None:
    payload = json.loads(_read(GR_CONTINUUM_CYCLE3_ARTIFACT_PATH))

    assert payload.get("record_id") == "GR_CONTINUUM_LIMIT_BRIDGE_CYCLE3_v0"
    assert payload.get("artifact_id") == "gr_continuum_bridge_theorem_surface_cycle3_v0"
    assert payload.get("scope") == "bounded_discrete_to_continuum_bridge_v0"

    theorem_tokens = payload.get("theorem_surface_tokens")
    assert isinstance(theorem_tokens, list) and len(theorem_tokens) >= 3
    assert "TARGET-GR-CONTINUUM-MICRO-03-BRIDGE-THEOREM-SURFACE-v0" in theorem_tokens

    mapping_hypotheses = payload.get("mapping_hypotheses")
    assert isinstance(mapping_hypotheses, dict)
    assert mapping_hypotheses.get("discrete_to_continuum_map_explicit") is True
    assert mapping_hypotheses.get("bounded_domain_assumptions_explicit") is True
    assert mapping_hypotheses.get("infinite_domain_uniqueness_claim") is False

    assert payload.get("closure_posture") == "theorem_surface_pinned_not_yet_discharged"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_gr_strong_field_cycle3_theorem_surface_artifact_is_pinned_and_well_formed() -> None:
    payload = json.loads(_read(GR_STRONG_FIELD_CYCLE3_ARTIFACT_PATH))

    assert payload.get("record_id") == "GR_STRONG_FIELD_REGIME_CYCLE3_v0"
    assert payload.get("artifact_id") == "gr_strong_field_theorem_surface_cycle3_v0"
    assert payload.get("scope") == "bounded_strong_field_program_v0"

    theorem_tokens = payload.get("theorem_surface_tokens")
    assert isinstance(theorem_tokens, list) and len(theorem_tokens) >= 3
    assert "TARGET-GR-STRONG-FIELD-MICRO-03-THEOREM-SURFACE-v0" in theorem_tokens

    assumption_posture = payload.get("assumption_posture")
    assert isinstance(assumption_posture, dict)
    assert assumption_posture.get("nonlinear_closure_assumptions_registry_linked") is True
    assert assumption_posture.get("domain_regularity_controls_explicit") is True
    assert assumption_posture.get("black_hole_uniqueness_claim") is False

    assert payload.get("closure_posture") == "theorem_surface_pinned_not_yet_discharged"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_qm_gr_cross_lane_cycle1_bundle_artifact_is_pinned_and_well_formed() -> None:
    bundle_text = _read(QM_GR_CROSS_LANE_BUNDLE_PATH)
    payload = json.loads(_read(QM_GR_CROSS_LANE_CYCLE1_ARTIFACT_PATH))

    for token in [
        "QM_GR_CROSS_LANE_COMPATIBILITY_BUNDLE_v0",
        "QM_GR_CROSS_LANE_PROGRESS_v0: CYCLE1_COMPATIBILITY_BUNDLE_PINNED",
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE2_v0: CYCLE2_COMPATIBILITY_BUNDLE_PINNED",
        "QM_GR_CROSS_LANE_PROGRESS_CYCLE3_v0: CYCLE3_COMPATIBILITY_BUNDLE_PINNED",
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "QM_GR_INTEGRATED_CRITERIA_ROW_01_v0: LANE_CHECKPOINT_COMPATIBILITY_PINNED",
        "QM_GR_INTEGRATED_CRITERIA_ROW_02_v0: EXPLICIT_NON_CLAIM_POSTURE_PINNED",
        "QM_GR_INTEGRATED_CRITERIA_ROW_03_v0: STATE_GATE_SYNC_PINNED",
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_v0: qm_gr_integrated_discharge_criteria_cycle10_v0",
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        "formal/output/qm_gr_integrated_discharge_criteria_cycle10_v0.json",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE5_v0: ASSUMPTION_MINIMIZATION_TOKEN_PINNED",
        "GR_CONTINUUM_LIMIT_PROGRESS_v0: CYCLE1_REFINEMENT_TREND_TOKEN_PINNED",
        "GR_STRONG_FIELD_PROGRESS_v0: CYCLE1_REGIME_PREDICATE_TOKEN_PINNED",
        "qm_gr_cross_lane_compatibility_cycle1_v0",
        "qm_gr_cross_lane_compatibility_cycle2_v0",
        "qm_gr_cross_lane_compatibility_cycle3_v0",
    ]:
        assert token in bundle_text, f"Missing cross-lane bundle token: {token}"

    assert payload.get("record_id") == "QM_GR_CROSS_LANE_COMPATIBILITY_CYCLE1_v0"
    assert payload.get("artifact_id") == "qm_gr_cross_lane_compatibility_cycle1_v0"
    assert payload.get("scope") == "cross_lane_checkpoint_sync_v0"

    lane_checkpoints = payload.get("lane_checkpoints")
    assert isinstance(lane_checkpoints, dict)
    assert lane_checkpoints.get("qm_full_derivation") == (
        "QM_FULL_DERIVATION_PROGRESS_CYCLE5_v0: ASSUMPTION_MINIMIZATION_TOKEN_PINNED"
    )
    assert lane_checkpoints.get("gr_continuum") == (
        "GR_CONTINUUM_LIMIT_PROGRESS_v0: CYCLE1_REFINEMENT_TREND_TOKEN_PINNED"
    )
    assert lane_checkpoints.get("gr_strong_field") == (
        "GR_STRONG_FIELD_PROGRESS_v0: CYCLE1_REGIME_PREDICATE_TOKEN_PINNED"
    )

    assert payload.get("compatibility_status") == "synchronized_cycle1"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_qm_gr_cross_lane_cycle2_bundle_artifact_is_pinned_and_well_formed() -> None:
    payload = json.loads(_read(QM_GR_CROSS_LANE_CYCLE2_ARTIFACT_PATH))

    assert payload.get("record_id") == "QM_GR_CROSS_LANE_COMPATIBILITY_CYCLE2_v0"
    assert payload.get("artifact_id") == "qm_gr_cross_lane_compatibility_cycle2_v0"
    assert payload.get("scope") == "cross_lane_checkpoint_sync_v0"

    lane_checkpoints = payload.get("lane_checkpoints")
    assert isinstance(lane_checkpoints, dict)
    assert lane_checkpoints.get("qm_full_derivation") == (
        "QM_FULL_DERIVATION_PROGRESS_CYCLE14_v0: TWO_KEY_RELEASE_DISCHARGE_COMPLETED"
    )
    assert lane_checkpoints.get("gr_continuum") == (
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE2_v0: GRID_INDEPENDENCE_SANITY_TOKEN_PINNED"
    )
    assert lane_checkpoints.get("gr_strong_field") == (
        "GR_STRONG_FIELD_PROGRESS_CYCLE2_v0: NONLINEAR_CLOSURE_SCAFFOLD_TOKEN_PINNED"
    )

    assert payload.get("compatibility_status") == "synchronized_cycle2"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_qm_gr_cross_lane_cycle3_bundle_artifact_is_pinned_and_well_formed() -> None:
    payload = json.loads(_read(QM_GR_CROSS_LANE_CYCLE3_ARTIFACT_PATH))

    assert payload.get("record_id") == "QM_GR_CROSS_LANE_COMPATIBILITY_CYCLE3_v0"
    assert payload.get("artifact_id") == "qm_gr_cross_lane_compatibility_cycle3_v0"
    assert payload.get("scope") == "cross_lane_checkpoint_sync_v0"

    lane_checkpoints = payload.get("lane_checkpoints")
    assert isinstance(lane_checkpoints, dict)
    assert lane_checkpoints.get("gr_continuum") == (
        "GR_CONTINUUM_LIMIT_PROGRESS_CYCLE3_v0: BRIDGE_THEOREM_SURFACE_TOKEN_PINNED"
    )
    assert lane_checkpoints.get("gr_strong_field") == (
        "GR_STRONG_FIELD_PROGRESS_CYCLE3_v0: STRONG_FIELD_THEOREM_SURFACE_TOKEN_PINNED"
    )

    assert payload.get("compatibility_status") == "synchronized_cycle3"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_cycle10_discharge_criteria_artifacts_are_pinned_and_well_formed() -> None:
    qm_payload = json.loads(_read(QM_FULL_DERIVATION_CRITERIA_CYCLE10_ARTIFACT_PATH))
    cont_payload = json.loads(_read(GR_CONTINUUM_CRITERIA_CYCLE10_ARTIFACT_PATH))
    strong_payload = json.loads(_read(GR_STRONG_FIELD_CRITERIA_CYCLE10_ARTIFACT_PATH))
    integrated_payload = json.loads(_read(QM_GR_INTEGRATED_CRITERIA_CYCLE10_ARTIFACT_PATH))
    qm_target_text = _read(QM_FULL_DERIVATION_TARGET_PATH)
    cont_target_text = _read(GR_CONTINUUM_TARGET_PATH)
    strong_target_text = _read(GR_STRONG_FIELD_TARGET_PATH)
    cross_lane_bundle_text = _read(QM_GR_CROSS_LANE_BUNDLE_PATH)
    state_text = _read(STATE_PATH)
    qm_digest = _sha256(QM_FULL_DERIVATION_CRITERIA_CYCLE10_ARTIFACT_PATH)
    cont_digest = _sha256(GR_CONTINUUM_CRITERIA_CYCLE10_ARTIFACT_PATH)
    strong_digest = _sha256(GR_STRONG_FIELD_CRITERIA_CYCLE10_ARTIFACT_PATH)
    integrated_digest = _sha256(QM_GR_INTEGRATED_CRITERIA_CYCLE10_ARTIFACT_PATH)

    target_qm_digest = _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    target_cont_digest = _extract_token_value(
        cont_target_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    target_strong_digest = _extract_token_value(
        strong_target_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    target_integrated_digest = _extract_token_value(
        cross_lane_bundle_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )

    state_qm_digest = _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    state_cont_digest = _extract_token_value(
        state_text,
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    state_strong_digest = _extract_token_value(
        state_text,
        "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )
    state_integrated_digest = _extract_token_value(
        state_text,
        "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
    )

    assert target_qm_digest == state_qm_digest
    assert target_cont_digest == state_cont_digest
    assert target_strong_digest == state_strong_digest
    assert target_integrated_digest == state_integrated_digest

    assert qm_digest == target_qm_digest
    assert cont_digest == target_cont_digest
    assert strong_digest == target_strong_digest
    assert integrated_digest == target_integrated_digest

    assert qm_payload.get("record_id") == "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_CYCLE10_v0"
    assert qm_payload.get("artifact_id") == "qm_full_derivation_discharge_criteria_cycle10_v0"
    qm_rows = qm_payload.get("criteria_rows")
    assert isinstance(qm_rows, list) and len(qm_rows) == 5
    assert [r.get("row_id") for r in qm_rows] == [
        "QM_FULL_DERIVATION_CRITERIA_ROW_01_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_02_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_03_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_04_v0",
        "QM_FULL_DERIVATION_CRITERIA_ROW_05_v0",
    ]

    assert cont_payload.get("record_id") == "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_CYCLE10_v0"
    assert cont_payload.get("artifact_id") == "gr_continuum_discharge_criteria_cycle10_v0"
    cont_rows = cont_payload.get("criteria_rows")
    assert isinstance(cont_rows, list) and len(cont_rows) == 4
    assert [r.get("row_id") for r in cont_rows] == [
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_01_v0",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_02_v0",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_03_v0",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_04_v0",
    ]

    assert strong_payload.get("record_id") == "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_CYCLE10_v0"
    assert strong_payload.get("artifact_id") == "gr_strong_field_discharge_criteria_cycle10_v0"
    strong_rows = strong_payload.get("criteria_rows")
    assert isinstance(strong_rows, list) and len(strong_rows) == 4
    assert [r.get("row_id") for r in strong_rows] == [
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_01_v0",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_02_v0",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_03_v0",
        "GR_STRONG_FIELD_REGIME_CRITERIA_ROW_04_v0",
    ]

    assert integrated_payload.get("record_id") == "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_CYCLE10_v0"
    assert integrated_payload.get("artifact_id") == "qm_gr_integrated_discharge_criteria_cycle10_v0"
    integrated_rows = integrated_payload.get("criteria_rows")
    assert isinstance(integrated_rows, list) and len(integrated_rows) == 3
    assert [r.get("row_id") for r in integrated_rows] == [
        "QM_GR_INTEGRATED_CRITERIA_ROW_01_v0",
        "QM_GR_INTEGRATED_CRITERIA_ROW_02_v0",
        "QM_GR_INTEGRATED_CRITERIA_ROW_03_v0",
    ]

    for payload in [qm_payload, cont_payload, strong_payload, integrated_payload]:
        determinism = payload.get("determinism")
        assert isinstance(determinism, dict)
        assert determinism.get("schema_version") == "v0"
        assert determinism.get("fingerprint_method") == "literal-json-lock"
        assert determinism.get("seed") == "fixed-none"


def test_qm_cycle14_exit_criteria_coverage_artifact_is_pinned_and_well_formed() -> None:
    qm_target_text = _read(QM_FULL_DERIVATION_TARGET_PATH)
    state_text = _read(STATE_PATH)
    payload = json.loads(_read(QM_FULL_DERIVATION_EXIT_COVERAGE_CYCLE14_ARTIFACT_PATH))

    for token in [
        "QM_FULL_DERIVATION_PROGRESS_CYCLE6_v0: EXIT_CRITERIA_COVERAGE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE7_v0: UNITARY_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE8_v0: DERIVATION_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE9_v0: ANTICIRCULARITY_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE10_v0: ASSUMPTION_MINIMIZATION_EXIT_ROW_PROMOTION_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PROGRESS_CYCLE14_v0: TWO_KEY_RELEASE_DISCHARGE_COMPLETED",
        "QM_FULL_DERIVATION_EXIT_ROW_01_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_EXIT_ROW_02_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle6_unitary_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_EXIT_ROW_04_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle8_anticircularity_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_EXIT_ROW_03_STATUS_v0: DISCHARGED_v0_DERIVATION_GRADE",
        "qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0",
        "QM_FULL_DERIVATION_EXIT_CRITERIA_COVERAGE_ARTIFACT_v0: qm_full_derivation_exit_criteria_coverage_cycle14_v0",
        "formal/output/qm_full_derivation_exit_criteria_coverage_cycle14_v0.json",
    ]:
        assert token in qm_target_text, f"Missing QM cycle14 target token: {token}"
        assert token in state_text, f"Missing QM cycle14 state token: {token}"

    assert payload.get("record_id") == "QM_FULL_DERIVATION_EXIT_CRITERIA_COVERAGE_CYCLE14_v0"
    assert payload.get("artifact_id") == "qm_full_derivation_exit_criteria_coverage_cycle14_v0"
    assert payload.get("scope") == "qm_full_derivation_exit_criteria_coverage_v0"
    assert payload.get("adjudication_posture") == "DISCHARGED_v0_DERIVATION_GRADE"

    rows = payload.get("coverage_rows")
    assert isinstance(rows, list) and len(rows) == 5
    assert [r.get("row_id") for r in rows] == [
        "QM_FULL_DERIVATION_EXIT_ROW_01_v0",
        "QM_FULL_DERIVATION_EXIT_ROW_02_v0",
        "QM_FULL_DERIVATION_EXIT_ROW_03_v0",
        "QM_FULL_DERIVATION_EXIT_ROW_04_v0",
        "QM_FULL_DERIVATION_EXIT_ROW_05_v0",
    ]

    row2 = next(r for r in rows if r.get("row_id") == "QM_FULL_DERIVATION_EXIT_ROW_02_v0")
    assert row2.get("status") == "DISCHARGED_v0_DERIVATION_GRADE"
    row2_evidence = row2.get("evidence_tokens")
    assert isinstance(row2_evidence, list)
    assert "qm_full_derivation_cycle6_unitary_exit_row_closure_token_v0" in row2_evidence

    row1 = next(r for r in rows if r.get("row_id") == "QM_FULL_DERIVATION_EXIT_ROW_01_v0")
    assert row1.get("status") == "DISCHARGED_v0_DERIVATION_GRADE"
    row1_evidence = row1.get("evidence_tokens")
    assert isinstance(row1_evidence, list)
    assert "qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0" in row1_evidence

    row4 = next(r for r in rows if r.get("row_id") == "QM_FULL_DERIVATION_EXIT_ROW_04_v0")
    assert row4.get("status") == "DISCHARGED_v0_DERIVATION_GRADE"
    row4_evidence = row4.get("evidence_tokens")
    assert isinstance(row4_evidence, list)
    assert "qm_full_derivation_cycle8_anticircularity_exit_row_closure_token_v0" in row4_evidence

    row3 = next(r for r in rows if r.get("row_id") == "QM_FULL_DERIVATION_EXIT_ROW_03_v0")
    assert row3.get("status") == "DISCHARGED_v0_DERIVATION_GRADE"
    row3_evidence = row3.get("evidence_tokens")
    assert isinstance(row3_evidence, list)
    assert "qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0" in row3_evidence

    status_values = {str(r.get("status")) for r in rows}
    assert status_values == {"DISCHARGED_v0_DERIVATION_GRADE"}

    for row in rows:
        evidence_tokens = row.get("evidence_tokens")
        assert isinstance(evidence_tokens, list) and evidence_tokens
        gap = str(row.get("remaining_gap") or "").strip()
        assert gap

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("seed") == "fixed-none"


def test_qm_cycle19_predischarge_gate_artifact_is_pinned_and_well_formed() -> None:
    qm_target_text = _read(QM_FULL_DERIVATION_TARGET_PATH)
    state_text = _read(STATE_PATH)
    payload = json.loads(_read(QM_FULL_DERIVATION_PREDISCHARGE_GATE_CYCLE19_ARTIFACT_PATH))

    for token in [
        "QM_FULL_DERIVATION_PROGRESS_CYCLE11_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_PREDISCHARGE_GATE_ARTIFACT_v0: qm_full_derivation_predischarge_gate_cycle19_v0",
        "formal/output/qm_full_derivation_predischarge_gate_cycle19_v0.json",
    ]:
        assert token in qm_target_text, f"Missing QM cycle19 target token: {token}"
        assert token in state_text, f"Missing QM cycle19 state token: {token}"

    assert payload.get("record_id") == "QM_FULL_DERIVATION_PREDISCHARGE_GATE_CYCLE19_v0"
    assert payload.get("artifact_id") == "qm_full_derivation_predischarge_gate_cycle19_v0"
    assert payload.get("scope") == "qm_full_derivation_predischarge_gate_bundle_v0"
    assert payload.get("adjudication_posture") == "DISCHARGED_v0_DERIVATION_GRADE"

    gate = payload.get("pre_discharge_gate")
    assert isinstance(gate, dict)
    assert gate.get("rows_1_to_4_closure_witness_complete") is True
    assert gate.get("row_5_adjudication_block_enforced") is False
    assert gate.get("ready_for_discharge_flip") is True
    assert gate.get("blocked_reason") == "none"

    closure_status = payload.get("closure_status_snapshot")
    assert isinstance(closure_status, dict)
    assert closure_status.get("QM_FULL_DERIVATION_EXIT_ROW_01_v0") == "DISCHARGED_v0_DERIVATION_GRADE"
    assert closure_status.get("QM_FULL_DERIVATION_EXIT_ROW_02_v0") == "DISCHARGED_v0_DERIVATION_GRADE"
    assert closure_status.get("QM_FULL_DERIVATION_EXIT_ROW_03_v0") == "DISCHARGED_v0_DERIVATION_GRADE"
    assert closure_status.get("QM_FULL_DERIVATION_EXIT_ROW_04_v0") == "DISCHARGED_v0_DERIVATION_GRADE"
    assert closure_status.get("QM_FULL_DERIVATION_EXIT_ROW_05_v0") == "DISCHARGED_v0_DERIVATION_GRADE"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list)
    assert "qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0" in witness_tokens

    policy_tokens = payload.get("policy_tokens")
    assert isinstance(policy_tokens, list)
    assert "QM_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0_DERIVATION_GRADE" in policy_tokens

    assert _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_ADJUDICATION",
    ) == "DISCHARGED_v0_DERIVATION_GRADE"
    assert _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_ADJUDICATION",
    ) == "DISCHARGED_v0_DERIVATION_GRADE"

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("seed") == "fixed-none"


def test_qm_cycle20_discharge_transition_bundle_is_pinned_and_two_key_gated() -> None:
    qm_target_text = _read(QM_FULL_DERIVATION_TARGET_PATH)
    state_text = _read(STATE_PATH)
    payload = json.loads(_read(QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_CYCLE20_ARTIFACT_PATH))

    for token in [
        "QM_FULL_DERIVATION_PROGRESS_CYCLE12_v0: DISCHARGE_TRANSITION_BUNDLE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0: qm_full_derivation_discharge_transition_bundle_cycle20_v0",
        "formal/output/qm_full_derivation_discharge_transition_bundle_cycle20_v0.json",
    ]:
        assert token in qm_target_text, f"Missing QM cycle20 target token: {token}"
        assert token in state_text, f"Missing QM cycle20 state token: {token}"

    assert payload.get("record_id") == "QM_FULL_DERIVATION_DISCHARGE_TRANSITION_BUNDLE_CYCLE20_v0"
    assert payload.get("artifact_id") == "qm_full_derivation_discharge_transition_bundle_cycle20_v0"
    assert payload.get("scope") == "qm_full_derivation_discharge_transition_bundle_v0"
    assert payload.get("adjudication_posture") == "DISCHARGED_v0_DERIVATION_GRADE"

    release = payload.get("release_condition")
    assert isinstance(release, dict)
    assert release.get("key_a_predischarge_gate_complete") is True
    assert release.get("key_b_discharge_policy_signoff_complete") is True
    assert release.get("two_key_release_satisfied") is True
    assert release.get("blocked_reason") == "none"

    refs = payload.get("input_bundle_refs")
    assert isinstance(refs, dict)
    assert refs.get("predischarge_gate_artifact") == "qm_full_derivation_predischarge_gate_cycle19_v0"
    assert refs.get("exit_criteria_coverage_artifact") == "qm_full_derivation_exit_criteria_coverage_cycle14_v0"
    assert refs.get("key_b_policy_signoff_artifact") == "qm_full_derivation_keyb_policy_signoff_cycle21_v0"

    policy_tokens = payload.get("policy_tokens")
    assert isinstance(policy_tokens, list)
    assert "QM_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0_DERIVATION_GRADE" in policy_tokens

    assert _extract_token_value(
        qm_target_text,
        "QM_FULL_DERIVATION_ADJUDICATION",
    ) == "DISCHARGED_v0_DERIVATION_GRADE"
    assert _extract_token_value(
        state_text,
        "QM_FULL_DERIVATION_ADJUDICATION",
    ) == "DISCHARGED_v0_DERIVATION_GRADE"

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("seed") == "fixed-none"


def test_qm_cycle21_keyb_policy_signoff_artifact_is_pinned_and_completed() -> None:
    qm_target_text = _read(QM_FULL_DERIVATION_TARGET_PATH)
    state_text = _read(STATE_PATH)
    payload = json.loads(_read(QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_CYCLE21_ARTIFACT_PATH))

    for token in [
        "QM_FULL_DERIVATION_PROGRESS_CYCLE13_v0: KEYB_POLICY_SIGNOFF_SURFACE_TOKEN_PINNED",
        "QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_ARTIFACT_v0: qm_full_derivation_keyb_policy_signoff_cycle21_v0",
        "formal/output/qm_full_derivation_keyb_policy_signoff_cycle21_v0.json",
    ]:
        assert token in qm_target_text, f"Missing QM cycle21 target token: {token}"
        assert token in state_text, f"Missing QM cycle21 state token: {token}"

    assert payload.get("record_id") == "QM_FULL_DERIVATION_KEYB_POLICY_SIGNOFF_CYCLE21_v0"
    assert payload.get("artifact_id") == "qm_full_derivation_keyb_policy_signoff_cycle21_v0"
    assert payload.get("scope") == "qm_full_derivation_keyb_policy_signoff_v0"
    assert payload.get("adjudication_posture") == "DISCHARGED_v0_DERIVATION_GRADE"

    keyb = payload.get("key_b_policy_signoff")
    assert isinstance(keyb, dict)
    assert keyb.get("required") is True
    assert keyb.get("signoff_complete") is True
    assert keyb.get("signoff_authority") == "QM_POLICY_BOARD_v0"
    assert keyb.get("signoff_ticket_id") == "QM-DISCHARGE-SIGNOFF-20260216-v0"
    assert keyb.get("blocked_reason") == "none"

    deps = payload.get("dependency_refs")
    assert isinstance(deps, dict)
    assert deps.get("predischarge_gate_artifact") == "qm_full_derivation_predischarge_gate_cycle19_v0"
    assert deps.get("discharge_transition_bundle_artifact") == "qm_full_derivation_discharge_transition_bundle_cycle20_v0"

    policy_tokens = payload.get("policy_tokens")
    assert isinstance(policy_tokens, list)
    assert "QM_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0_DERIVATION_GRADE" in policy_tokens

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("seed") == "fixed-none"
