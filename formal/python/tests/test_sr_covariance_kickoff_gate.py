from __future__ import annotations

import json
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
SR_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md"
)
SR_CYCLE1_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_object_scaffold_cycle1_v0.json"
)
SR_CYCLE2_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_contract_surface_cycle2_v0.json"
)
SR_CYCLE3_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_lorentz_interval_placeholder_cycle3_v0.json"
)
SR_CYCLE4_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_velocity_composition_placeholder_cycle4_v0.json"
)
SR_CYCLE5_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_integrated_kickoff_bundle_cycle5_v0.json"
)
SR_CYCLE6_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_predischarge_gate_bundle_cycle6_v0.json"
)
SR_CYCLE7_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_discharge_transition_bundle_cycle7_v0.json"
)
SR_CYCLE8_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_keyb_policy_signoff_bundle_cycle8_v0.json"
)
SR_CYCLE9_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_final_predischarge_package_cycle9_v0.json"
)
SR_CYCLE10_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_discharge_criteria_cycle10_v0.json"
)
SR_CYCLE11_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_adjudication_posture_cycle11_v0.json"
)
SR_CYCLE12_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_post_adjudication_contract_freeze_cycle12_v0.json"
)
SR_CYCLE13_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_surface_scaffold_cycle13_v0.json"
)
SR_CYCLE14_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_assumption_minimization_cycle14_v0.json"
)
SR_CYCLE15_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0.json"
)
SR_CYCLE16_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_robustness_row1_cycle16_v0.json"
)
SR_CYCLE17_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_negctrl_row1_cycle17_v0.json"
)
SR_CYCLE18_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_robustness_row2_cycle18_v0.json"
)
SR_CYCLE19_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_negctrl_row2_cycle19_v0.json"
)
SR_CYCLE20_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0.json"
)
SR_CYCLE21_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_predischarge_criteria_cycle21_v0.json"
)
SR_CYCLE22_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_adjudication_transition_cycle22_v0.json"
)
SR_CYCLE23_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_theorem_package_freeze_cycle23_v0.json"
)
SR_CYCLE24_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0.json"
)
SR_CYCLE25_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_derivation_promotion_gate_cycle25_v0.json"
)
SR_CYCLE26_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_derivation_completeness_gate_scaffold_cycle26_v0.json"
)
SR_CYCLE27_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_implementation_gate_cycle27_v0.json"
)
SR_CYCLE28_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_discharge_stub_cycle28_v0.json"
)
SR_CYCLE29_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_phase_exit_binding_cycle29_v0.json"
)
SR_CYCLE30_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_discharge_progression_cycle30_v0.json"
)
SR_CYCLE31_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0.json"
)
SR_CYCLE32_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_discharge_row02_lock_cycle32_v0.json"
)
SR_CYCLE33_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_discharge_row03_lock_cycle33_v0.json"
)
SR_CYCLE34_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_discharge_row04_lock_cycle34_v0.json"
)
SR_CYCLE35_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_theorem_object_discharge_phase1_completion_transition_cycle35_v0.json"
)
SR_CYCLE36_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_canonical_equivalence_surface_entry_lock_cycle36_v0.json"
)
SR_CYCLE37_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_canonical_equivalence_theorem_surface_lock_cycle37_v0.json"
)
SR_CYCLE38_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_canonical_equivalence_theorem_object_linkage_lock_cycle38_v0.json"
)
SR_CYCLE39_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_canonical_equivalence_predischarge_criteria_lock_cycle39_v0.json"
)
SR_CYCLE40_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_canonical_equivalence_adjudication_transition_lock_cycle40_v0.json"
)
SR_CYCLE41_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_canonical_equivalence_package_freeze_lock_cycle41_v0.json"
)
SR_CYCLE42_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_assumption_minimization_discharge_surface_entry_lock_cycle42_v0.json"
)
SR_CYCLE43_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_assumption_minimization_discharge_theorem_surface_lock_cycle43_v0.json"
)
SR_CYCLE44_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_assumption_robustness_discharge_surface_entry_lock_cycle44_v0.json"
)
SR_CYCLE45_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_assumption_robustness_discharge_theorem_surface_lock_cycle45_v0.json"
)
SR_CYCLE46_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_assumption_negctrl_discharge_surface_entry_lock_cycle46_v0.json"
)
SR_CYCLE47_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_assumption_negctrl_discharge_theorem_surface_lock_cycle47_v0.json"
)
SR_CYCLE48_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "sr_covariance_assumption_minimization_discharge_package_freeze_lock_cycle48_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sr_cycle1_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-01-OBJECT-SCAFFOLD-v0",
        "SR_COVARIANCE_PROGRESS_v0: CYCLE1_OBJECT_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE1_ARTIFACT_v0: sr_covariance_object_scaffold_cycle1_v0",
        "formal/output/sr_covariance_object_scaffold_cycle1_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR kickoff token in target: {token}"
        assert token in state_text, f"Missing SR kickoff token in state: {token}"


def test_sr_cycle2_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-02-CONTRACT-SURFACE-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE2_v0: CONTRACT_SURFACE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE2_ARTIFACT_v0: sr_covariance_contract_surface_cycle2_v0",
        "formal/output/sr_covariance_contract_surface_cycle2_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-2 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-2 token in state: {token}"


def test_sr_cycle3_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-03-LORENTZ-INTERVAL-PLACEHOLDER-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE3_v0: LORENTZ_INTERVAL_PLACEHOLDER_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE3_ARTIFACT_v0: sr_covariance_lorentz_interval_placeholder_cycle3_v0",
        "formal/output/sr_covariance_lorentz_interval_placeholder_cycle3_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-3 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-3 token in state: {token}"


def test_sr_cycle4_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-04-VELOCITY-COMPOSITION-PLACEHOLDER-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE4_v0: VELOCITY_COMPOSITION_PLACEHOLDER_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE4_ARTIFACT_v0: sr_covariance_velocity_composition_placeholder_cycle4_v0",
        "formal/output/sr_covariance_velocity_composition_placeholder_cycle4_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-4 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-4 token in state: {token}"


def test_sr_cycle5_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-05-INTEGRATED-KICKOFF-BUNDLE-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE5_v0: INTEGRATED_KICKOFF_BUNDLE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE5_ARTIFACT_v0: sr_covariance_integrated_kickoff_bundle_cycle5_v0",
        "formal/output/sr_covariance_integrated_kickoff_bundle_cycle5_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-5 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-5 token in state: {token}"


def test_sr_cycle6_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-06-PREDISCHARGE-GATE-BUNDLE-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE6_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE6_ARTIFACT_v0: sr_covariance_predischarge_gate_bundle_cycle6_v0",
        "formal/output/sr_covariance_predischarge_gate_bundle_cycle6_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-6 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-6 token in state: {token}"


def test_sr_cycle7_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-07-DISCHARGE-TRANSITION-BUNDLE-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE7_v0: DISCHARGE_TRANSITION_BUNDLE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE7_ARTIFACT_v0: sr_covariance_discharge_transition_bundle_cycle7_v0",
        "formal/output/sr_covariance_discharge_transition_bundle_cycle7_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-7 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-7 token in state: {token}"


def test_sr_cycle8_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-08-KEYB-POLICY-SIGNOFF-BUNDLE-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE8_v0: KEYB_POLICY_SIGNOFF_BUNDLE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE8_ARTIFACT_v0: sr_covariance_keyb_policy_signoff_bundle_cycle8_v0",
        "formal/output/sr_covariance_keyb_policy_signoff_bundle_cycle8_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-8 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-8 token in state: {token}"


def test_sr_cycle9_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-09-FINAL-PREDISCHARGE-PACKAGE-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE9_v0: FINAL_PREDISCHARGE_PACKAGE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE9_ARTIFACT_v0: sr_covariance_final_predischarge_package_cycle9_v0",
        "formal/output/sr_covariance_final_predischarge_package_cycle9_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-9 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-9 token in state: {token}"


def test_sr_cycle10_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "SR_COVARIANCE_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_01_v0: OBJECT_SCAFFOLD_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_02_v0: CONTRACT_SURFACE_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_03_v0: LORENTZ_INTERVAL_PLACEHOLDER_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_04_v0: VELOCITY_COMPOSITION_PLACEHOLDER_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_05_v0: STATE_GATE_SYNC_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE10_v0: DISCHARGE_CRITERIA_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE10_ARTIFACT_v0: sr_covariance_discharge_criteria_cycle10_v0",
        "formal/output/sr_covariance_discharge_criteria_cycle10_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-10 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-10 token in state: {token}"


def test_sr_cycle11_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "SR_COVARIANCE_ADJUDICATION_v0: DISCHARGED_v0_PLANNING_CRITERIA_LOCKED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE11_v0: ADJUDICATION_POSTURE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE11_ARTIFACT_v0: sr_covariance_adjudication_posture_cycle11_v0",
        "formal/output/sr_covariance_adjudication_posture_cycle11_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-11 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-11 token in state: {token}"


def test_sr_cycle12_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-12-POST-ADJUDICATION-CONTRACT-FREEZE-v0",
        "SR_COVARIANCE_CONTRACT_FREEZE_v0: CYCLE12_POST_ADJUDICATION_CONTRACT_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE12_v0: POST_ADJUDICATION_CONTRACT_FREEZE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE12_ARTIFACT_v0: sr_covariance_post_adjudication_contract_freeze_cycle12_v0",
        "formal/output/sr_covariance_post_adjudication_contract_freeze_cycle12_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-12 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-12 token in state: {token}"


def test_sr_cycle13_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-13-THEOREM-SURFACE-SCAFFOLD-v0",
        "formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0.md",
        "SR_COVARIANCE_PROGRESS_CYCLE13_v0: THEOREM_SURFACE_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE13_ARTIFACT_v0: sr_covariance_theorem_surface_scaffold_cycle13_v0",
        "formal/output/sr_covariance_theorem_surface_scaffold_cycle13_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-13 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-13 token in state: {token}"


def test_sr_cycle14_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-14-THEOREM-ASSUMPTION-MINIMIZATION-v0",
        "SR_COVARIANCE_THEOREM_ASSUMPTION_MINIMIZATION_v0: CYCLE14_MIN1_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE14_v0: THEOREM_ASSUMPTION_MINIMIZATION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE14_ARTIFACT_v0: sr_covariance_theorem_assumption_minimization_cycle14_v0",
        "formal/output/sr_covariance_theorem_assumption_minimization_cycle14_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-14 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-14 token in state: {token}"


def test_sr_cycle15_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-15-THEOREM-ROBUSTNESS-NEGCTRL-SCAFFOLD-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_v0: CYCLE15_SCAFFOLD_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE15_v0: THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE15_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0",
        "formal/output/sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-15 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-15 token in state: {token}"


def test_sr_cycle16_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-16-THEOREM-ROBUSTNESS-ROW1-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_01_v0: PERTURB_INTERVAL_SCALE_SMALL_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE16_v0: THEOREM_ROBUSTNESS_ROW1_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE16_ARTIFACT_v0: sr_covariance_theorem_robustness_row1_cycle16_v0",
        "formal/output/sr_covariance_theorem_robustness_row1_cycle16_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-16 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-16 token in state: {token}"


def test_sr_cycle17_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-17-THEOREM-NEGCTRL-ROW1-v0",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_01_v0: BROKEN_INTERVAL_INVARIANCE_ASSUMPTION_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE17_v0: THEOREM_NEGCTRL_ROW1_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE17_ARTIFACT_v0: sr_covariance_theorem_negctrl_row1_cycle17_v0",
        "formal/output/sr_covariance_theorem_negctrl_row1_cycle17_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-17 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-17 token in state: {token}"


def test_sr_cycle18_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-18-THEOREM-ROBUSTNESS-ROW2-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_02_v0: PERTURB_VELOCITY_COMPOSITION_SMALL_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE18_v0: THEOREM_ROBUSTNESS_ROW2_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE18_ARTIFACT_v0: sr_covariance_theorem_robustness_row2_cycle18_v0",
        "formal/output/sr_covariance_theorem_robustness_row2_cycle18_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-18 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-18 token in state: {token}"


def test_sr_cycle19_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-19-THEOREM-NEGCTRL-ROW2-v0",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_02_v0: BROKEN_VELOCITY_COMPOSITION_CLOSURE_ASSUMPTION_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE19_v0: THEOREM_NEGCTRL_ROW2_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE19_ARTIFACT_v0: sr_covariance_theorem_negctrl_row2_cycle19_v0",
        "formal/output/sr_covariance_theorem_negctrl_row2_cycle19_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-19 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-19 token in state: {token}"


def test_sr_cycle20_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-20-THEOREM-ROBUSTNESS-NEGCTRL-FAMILY-COMPLETE-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_v0: CYCLE20_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE20_v0: THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE20_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0",
        "formal/output/sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-20 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-20 token in state: {token}"


def test_sr_cycle21_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-21-THEOREM-PREDISCHARGE-CRITERIA-v0",
        "SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_v0: CYCLE21_ROW_LEVEL_CRITERIA_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE21_v0: THEOREM_PREDISCHARGE_CRITERIA_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE21_ARTIFACT_v0: sr_covariance_theorem_predischarge_criteria_cycle21_v0",
        "formal/output/sr_covariance_theorem_predischarge_criteria_cycle21_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-21 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-21 token in state: {token}"


def test_sr_cycle22_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-22-THEOREM-ADJUDICATION-TRANSITION-v0",
        "SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_PREDISCHARGE_CRITERIA_LOCKED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE22_v0: THEOREM_ADJUDICATION_TRANSITION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE22_ARTIFACT_v0: sr_covariance_theorem_adjudication_transition_cycle22_v0",
        "formal/output/sr_covariance_theorem_adjudication_transition_cycle22_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-22 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-22 token in state: {token}"


def test_sr_cycle23_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-23-THEOREM-PACKAGE-FREEZE-v0",
        "SR_COVARIANCE_THEOREM_PACKAGE_FREEZE_v0: CYCLE23_FROZEN_CONTENTS_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE23_v0: THEOREM_PACKAGE_FREEZE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE23_ARTIFACT_v0: sr_covariance_theorem_package_freeze_cycle23_v0",
        "formal/output/sr_covariance_theorem_package_freeze_cycle23_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-23 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-23 token in state: {token}"


def test_sr_cycle24_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-24-THEOREM-FROZEN-WATCH-REOPEN-POLICY-v0",
        "SR_COVARIANCE_THEOREM_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "SR_COVARIANCE_PROGRESS_CYCLE24_v0: THEOREM_FROZEN_WATCH_REOPEN_POLICY_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE24_ARTIFACT_v0: sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0",
        "formal/output/sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-24 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-24 token in state: {token}"


def test_sr_cycle25_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-25-THEOREM-DERIVATION-PROMOTION-GATE-v0",
        "SR_COVARIANCE_THEOREM_DERIVATION_PROMOTION_GATE_v0: CYCLE25_CRITERIA_LOCKED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE25_v0: THEOREM_DERIVATION_PROMOTION_GATE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE25_ARTIFACT_v0: sr_covariance_theorem_derivation_promotion_gate_cycle25_v0",
        "formal/output/sr_covariance_theorem_derivation_promotion_gate_cycle25_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-25 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-25 token in state: {token}"


def test_sr_cycle26_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-26-DERIVATION-COMPLETENESS-GATE-SCAFFOLD-v0",
        "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_SR_DERIVATION_COMPLETENESS_GATE_v0.md",
        "SR_DERIVATION_COMPLETENESS_GATE_v0: CYCLE26_SCAFFOLD_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE26_v0: DERIVATION_COMPLETENESS_GATE_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE26_ARTIFACT_v0: sr_covariance_derivation_completeness_gate_scaffold_cycle26_v0",
        "formal/output/sr_covariance_derivation_completeness_gate_scaffold_cycle26_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-26 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-26 token in state: {token}"


def test_sr_cycle27_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-27-THEOREM-OBJECT-IMPLEMENTATION-GATE-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_IMPLEMENTATION_GATE_v0: CYCLE27_BASE_OBJECT_SET_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE27_v0: THEOREM_OBJECT_IMPLEMENTATION_GATE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE27_ARTIFACT_v0: sr_covariance_theorem_object_implementation_gate_cycle27_v0",
        "formal/output/sr_covariance_theorem_object_implementation_gate_cycle27_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-27 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-27 token in state: {token}"


def test_sr_cycle28_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-28-THEOREM-OBJECT-DISCHARGE-STUB-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_STUB_v0: CYCLE28_BASE_THEOREM_SIGNATURES_PINNED_NONCLAIM",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE28_v0: THEOREM_OBJECT_DISCHARGE_STUB_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE28_ARTIFACT_v0: sr_covariance_theorem_object_discharge_stub_cycle28_v0",
        "formal/output/sr_covariance_theorem_object_discharge_stub_cycle28_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-28 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-28 token in state: {token}"


def test_sr_cycle29_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-29-THEOREM-OBJECT-PHASE-EXIT-BINDING-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_PHASE_EXIT_BINDING_v0: CYCLE29_PHASE_EXIT_TOKENS_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_EXIT_v0: OBJECT_THEOREM_SURFACES_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_EXIT_v0: CANONICAL_EQUIVALENCE_SURFACE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE3_EXIT_v0: ASSUMPTION_MINIMIZATION_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE4_EXIT_v0: ROBUSTNESS_NEGCTRL_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE5_EXIT_v0: DERIVATION_COMPLETENESS_GATE_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE6_EXIT_v0: INEVITABILITY_GATE_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE7_EXIT_v0: PACKAGE_FREEZE_REOPEN_POLICY_BOUND_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE29_v0: THEOREM_OBJECT_PHASE_EXIT_BINDING_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE29_ARTIFACT_v0: sr_covariance_theorem_object_phase_exit_binding_cycle29_v0",
        "formal/output/sr_covariance_theorem_object_phase_exit_binding_cycle29_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-29 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-29 token in state: {token}"


def test_sr_cycle30_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-30-THEOREM-OBJECT-DISCHARGE-PROGRESSION-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PROGRESSION_v0: CYCLE30_PHASE1_DISCHARGE_PROGRESS_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_02_v0: INTERVAL_INVARIANCE_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_03_v0: VELOCITY_COMPOSITION_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_04_v0: COVARIANCE_CONTRACT_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_PROGRESS_v0: ROWS_01_04_POPULATED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE30_v0: THEOREM_OBJECT_DISCHARGE_PROGRESSION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE30_ARTIFACT_v0: sr_covariance_theorem_object_discharge_progression_cycle30_v0",
        "formal/output/sr_covariance_theorem_object_discharge_progression_cycle30_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-30 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-30 token in state: {token}"


def test_sr_cycle31_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-31-THEOREM-OBJECT-DISCHARGE-ROW01-LOCK-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_v0: CYCLE31_PHASE1_ROW01_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_STATUS_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE31_v0: THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE31_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0",
        "formal/output/sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-31 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-31 token in state: {token}"


def test_sr_cycle32_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-32-THEOREM-OBJECT-DISCHARGE-ROW02-LOCK-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW02_LOCK_v0: CYCLE32_PHASE1_ROW02_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_02_STATUS_v0: INTERVAL_INVARIANCE_SURFACE_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE32_v0: THEOREM_OBJECT_DISCHARGE_ROW02_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE32_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row02_lock_cycle32_v0",
        "formal/output/sr_covariance_theorem_object_discharge_row02_lock_cycle32_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-32 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-32 token in state: {token}"


def test_sr_cycle33_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-33-THEOREM-OBJECT-DISCHARGE-ROW03-LOCK-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW03_LOCK_v0: CYCLE33_PHASE1_ROW03_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_03_STATUS_v0: VELOCITY_COMPOSITION_SURFACE_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE33_v0: THEOREM_OBJECT_DISCHARGE_ROW03_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE33_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row03_lock_cycle33_v0",
        "formal/output/sr_covariance_theorem_object_discharge_row03_lock_cycle33_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-33 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-33 token in state: {token}"


def test_sr_cycle34_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-34-THEOREM-OBJECT-DISCHARGE-ROW04-LOCK-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW04_LOCK_v0: CYCLE34_PHASE1_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_04_STATUS_v0: COVARIANCE_CONTRACT_SURFACE_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE34_v0: THEOREM_OBJECT_DISCHARGE_ROW04_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE34_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row04_lock_cycle34_v0",
        "formal/output/sr_covariance_theorem_object_discharge_row04_lock_cycle34_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-34 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-34 token in state: {token}"


def test_sr_cycle35_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-35-THEOREM-OBJECT-DISCHARGE-PHASE1-COMPLETE-TRANSITION-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PHASE1_COMPLETION_v0: CYCLE35_PHASE1_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE35_v0: THEOREM_OBJECT_DISCHARGE_PHASE1_COMPLETION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE35_ARTIFACT_v0: sr_covariance_theorem_object_discharge_phase1_completion_transition_cycle35_v0",
        "formal/output/sr_covariance_theorem_object_discharge_phase1_completion_transition_cycle35_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-35 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-35 token in state: {token}"


def test_sr_cycle36_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-36-CANONICAL-EQUIVALENCE-SURFACE-ENTRY-LOCK-v0",
        "SR_COVARIANCE_CANONICAL_EQUIVALENCE_SURFACE_ENTRY_LOCK_v0: CYCLE36_PHASE2_ENTRY_SURFACE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE36_v0: PHASE2_CANONICAL_EQUIVALENCE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE36_ARTIFACT_v0: sr_covariance_canonical_equivalence_surface_entry_lock_cycle36_v0",
        "formal/output/sr_covariance_canonical_equivalence_surface_entry_lock_cycle36_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-36 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-36 token in state: {token}"


def test_sr_cycle37_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-37-CANONICAL-EQUIVALENCE-THEOREM-SURFACE-LOCK-v0",
        "SR_COVARIANCE_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_LOCK_v0: CYCLE37_PHASE2_THEOREM_SURFACE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE37_v0: PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE37_ARTIFACT_v0: sr_covariance_canonical_equivalence_theorem_surface_lock_cycle37_v0",
        "formal/output/sr_covariance_canonical_equivalence_theorem_surface_lock_cycle37_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-37 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-37 token in state: {token}"


def test_sr_cycle38_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-38-CANONICAL-EQUIVALENCE-THEOREM-OBJECT-LINKAGE-LOCK-v0",
        "SR_COVARIANCE_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_LOCK_v0: CYCLE38_PHASE2_THEOREM_OBJECT_LINKAGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE38_v0: PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE38_ARTIFACT_v0: sr_covariance_canonical_equivalence_theorem_object_linkage_lock_cycle38_v0",
        "formal/output/sr_covariance_canonical_equivalence_theorem_object_linkage_lock_cycle38_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-38 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-38 token in state: {token}"


def test_sr_cycle39_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-39-CANONICAL-EQUIVALENCE-PREDISCHARGE-CRITERIA-LOCK-v0",
        "SR_COVARIANCE_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_LOCK_v0: CYCLE39_PHASE2_PREDISCHARGE_CRITERIA_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE39_v0: PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE39_ARTIFACT_v0: sr_covariance_canonical_equivalence_predischarge_criteria_lock_cycle39_v0",
        "formal/output/sr_covariance_canonical_equivalence_predischarge_criteria_lock_cycle39_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-39 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-39 token in state: {token}"


def test_sr_cycle40_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-40-CANONICAL-EQUIVALENCE-ADJUDICATION-TRANSITION-LOCK-v0",
        "SR_COVARIANCE_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_LOCK_v0: CYCLE40_PHASE2_ADJUDICATION_TRANSITION_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE40_v0: PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE40_ARTIFACT_v0: sr_covariance_canonical_equivalence_adjudication_transition_lock_cycle40_v0",
        "formal/output/sr_covariance_canonical_equivalence_adjudication_transition_lock_cycle40_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-40 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-40 token in state: {token}"


def test_sr_cycle41_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-41-CANONICAL-EQUIVALENCE-PACKAGE-FREEZE-LOCK-v0",
        "SR_COVARIANCE_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_LOCK_v0: CYCLE41_PHASE2_PACKAGE_FREEZE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_STATUS_v0: PACKAGE_FREEZE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE41_v0: PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE41_ARTIFACT_v0: sr_covariance_canonical_equivalence_package_freeze_lock_cycle41_v0",
        "formal/output/sr_covariance_canonical_equivalence_package_freeze_lock_cycle41_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-41 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-41 token in state: {token}"


def test_sr_cycle42_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-42-ASSUMPTION-MINIMIZATION-DISCHARGE-SURFACE-ENTRY-LOCK-v0",
        "SR_COVARIANCE_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE42_PHASE3_ENTRY_SURFACE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_STATUS_v0: PACKAGE_FREEZE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE42_v0: PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE42_ARTIFACT_v0: sr_covariance_assumption_minimization_discharge_surface_entry_lock_cycle42_v0",
        "formal/output/sr_covariance_assumption_minimization_discharge_surface_entry_lock_cycle42_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-42 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-42 token in state: {token}"


def test_sr_cycle43_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-43-ASSUMPTION-MINIMIZATION-DISCHARGE-THEOREM-SURFACE-LOCK-v0",
        "SR_COVARIANCE_ASSUMPTION_MINIMIZATION_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE43_PHASE3_THEOREM_SURFACE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_STATUS_v0: PACKAGE_FREEZE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "SR_COVARIANCE_PROGRESS_CYCLE43_v0: PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE43_ARTIFACT_v0: sr_covariance_assumption_minimization_discharge_theorem_surface_lock_cycle43_v0",
        "formal/output/sr_covariance_assumption_minimization_discharge_theorem_surface_lock_cycle43_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-43 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-43 token in state: {token}"


def test_sr_cycle44_to_cycle48_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    cycle_token_sets = {
        "44": [
            "TARGET-SR-COV-MICRO-44-ROBUSTNESS-DISCHARGE-SURFACE-ENTRY-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_ROBUSTNESS_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE44_PHASE3_ROBUSTNESS_ENTRY_SURFACE_PINNED_NONCLAIM",
            "SR_FULL_DERIVATION_PHASE3_ROBUSTNESS_DISCHARGE_ENTRY_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE44_v0: PHASE3_ROBUSTNESS_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
            "SR_COVARIANCE_CYCLE44_ARTIFACT_v0: sr_covariance_assumption_robustness_discharge_surface_entry_lock_cycle44_v0",
            "formal/output/sr_covariance_assumption_robustness_discharge_surface_entry_lock_cycle44_v0.json",
        ],
        "45": [
            "TARGET-SR-COV-MICRO-45-ROBUSTNESS-DISCHARGE-THEOREM-SURFACE-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_ROBUSTNESS_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE45_PHASE3_ROBUSTNESS_THEOREM_SURFACE_PINNED_NONCLAIM",
            "SR_FULL_DERIVATION_PHASE3_ROBUSTNESS_DISCHARGE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE45_v0: PHASE3_ROBUSTNESS_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
            "SR_COVARIANCE_CYCLE45_ARTIFACT_v0: sr_covariance_assumption_robustness_discharge_theorem_surface_lock_cycle45_v0",
            "formal/output/sr_covariance_assumption_robustness_discharge_theorem_surface_lock_cycle45_v0.json",
        ],
        "46": [
            "TARGET-SR-COV-MICRO-46-NEGCTRL-DISCHARGE-SURFACE-ENTRY-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_NEGCTRL_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE46_PHASE3_NEGCTRL_ENTRY_SURFACE_PINNED_NONCLAIM",
            "SR_FULL_DERIVATION_PHASE3_NEGCTRL_DISCHARGE_ENTRY_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE46_v0: PHASE3_NEGCTRL_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
            "SR_COVARIANCE_CYCLE46_ARTIFACT_v0: sr_covariance_assumption_negctrl_discharge_surface_entry_lock_cycle46_v0",
            "formal/output/sr_covariance_assumption_negctrl_discharge_surface_entry_lock_cycle46_v0.json",
        ],
        "47": [
            "TARGET-SR-COV-MICRO-47-NEGCTRL-DISCHARGE-THEOREM-SURFACE-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_NEGCTRL_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE47_PHASE3_NEGCTRL_THEOREM_SURFACE_PINNED_NONCLAIM",
            "SR_FULL_DERIVATION_PHASE3_NEGCTRL_DISCHARGE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE47_v0: PHASE3_NEGCTRL_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
            "SR_COVARIANCE_CYCLE47_ARTIFACT_v0: sr_covariance_assumption_negctrl_discharge_theorem_surface_lock_cycle47_v0",
            "formal/output/sr_covariance_assumption_negctrl_discharge_theorem_surface_lock_cycle47_v0.json",
        ],
        "48": [
            "TARGET-SR-COV-MICRO-48-ASSUMPTION-MINIMIZATION-DISCHARGE-PACKAGE-FREEZE-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_MINIMIZATION_DISCHARGE_PACKAGE_FREEZE_LOCK_v0: CYCLE48_PHASE3_PACKAGE_FREEZE_PINNED_NONCLAIM",
            "SR_FULL_DERIVATION_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_PACKAGE_FREEZE_STATUS_v0: PACKAGE_FREEZE_SCAFFOLD_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE48_v0: PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_PACKAGE_FREEZE_LOCK_TOKEN_PINNED",
            "SR_COVARIANCE_CYCLE48_ARTIFACT_v0: sr_covariance_assumption_minimization_discharge_package_freeze_lock_cycle48_v0",
            "formal/output/sr_covariance_assumption_minimization_discharge_package_freeze_lock_cycle48_v0.json",
        ],
    }

    for cycle, tokens in cycle_token_sets.items():
        for token in tokens:
            assert token in target_text, f"Missing SR cycle-{cycle} token in target: {token}"
            assert token in state_text, f"Missing SR cycle-{cycle} token in state: {token}"


def test_sr_cycle1_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE1_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_object_scaffold_cycle1_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-001"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-01-OBJECT-SCAFFOLD-v0"
    assert payload.get("status") == "LOCKED_OBJECT_SCAFFOLD_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-1 artifact."
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_object_scaffold_cycle1_v0"


def test_sr_cycle2_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE2_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_contract_surface_cycle2_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-002"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-02-CONTRACT-SURFACE-v0"
    assert payload.get("status") == "LOCKED_CONTRACT_SURFACE_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-2 artifact."
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_contract_surface_cycle2_v0"


def test_sr_cycle3_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE3_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_lorentz_interval_placeholder_cycle3_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-003"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-03-LORENTZ-INTERVAL-PLACEHOLDER-v0"
    assert payload.get("status") == "LOCKED_LORENTZ_INTERVAL_PLACEHOLDER_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-3 artifact."
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_lorentz_interval_placeholder_cycle3_v0"
    )


def test_sr_cycle4_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE4_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_velocity_composition_placeholder_cycle4_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-004"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-04-VELOCITY-COMPOSITION-PLACEHOLDER-v0"
    assert payload.get("status") == "LOCKED_VELOCITY_COMPOSITION_PLACEHOLDER_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-4 artifact."
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_velocity_composition_placeholder_cycle4_v0"
    )


def test_sr_cycle5_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE5_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_integrated_kickoff_bundle_cycle5_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-005"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-05-INTEGRATED-KICKOFF-BUNDLE-v0"
    assert payload.get("status") == "LOCKED_INTEGRATED_KICKOFF_BUNDLE_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    covered_cycles = payload.get("covered_cycles")
    assert covered_cycles == [
        "CYCLE-001",
        "CYCLE-002",
        "CYCLE-003",
        "CYCLE-004",
        "CYCLE-005",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-5 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE5_v0: INTEGRATED_KICKOFF_BUNDLE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_integrated_kickoff_bundle_cycle5_v0"
    )


def test_sr_cycle6_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE6_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_predischarge_gate_bundle_cycle6_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-006"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-06-PREDISCHARGE-GATE-BUNDLE-v0"
    assert payload.get("status") == "LOCKED_PREDISCHARGE_GATE_BUNDLE_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    covered_cycles = payload.get("covered_cycles")
    assert covered_cycles == [
        "CYCLE-001",
        "CYCLE-002",
        "CYCLE-003",
        "CYCLE-004",
        "CYCLE-005",
        "CYCLE-006",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-6 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE6_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_predischarge_gate_bundle_cycle6_v0"
    )


def test_sr_cycle7_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE7_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_discharge_transition_bundle_cycle7_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-007"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-07-DISCHARGE-TRANSITION-BUNDLE-v0"
    assert payload.get("status") == "LOCKED_DISCHARGE_TRANSITION_BUNDLE_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    covered_cycles = payload.get("covered_cycles")
    assert covered_cycles == [
        "CYCLE-001",
        "CYCLE-002",
        "CYCLE-003",
        "CYCLE-004",
        "CYCLE-005",
        "CYCLE-006",
        "CYCLE-007",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-7 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE7_v0: DISCHARGE_TRANSITION_BUNDLE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_discharge_transition_bundle_cycle7_v0"
    )


def test_sr_cycle8_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE8_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_keyb_policy_signoff_bundle_cycle8_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-008"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-08-KEYB-POLICY-SIGNOFF-BUNDLE-v0"
    assert payload.get("status") == "LOCKED_KEYB_POLICY_SIGNOFF_BUNDLE_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    covered_cycles = payload.get("covered_cycles")
    assert covered_cycles == [
        "CYCLE-001",
        "CYCLE-002",
        "CYCLE-003",
        "CYCLE-004",
        "CYCLE-005",
        "CYCLE-006",
        "CYCLE-007",
        "CYCLE-008",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-8 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE8_v0: KEYB_POLICY_SIGNOFF_BUNDLE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_keyb_policy_signoff_bundle_cycle8_v0"
    )


def test_sr_cycle9_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE9_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_final_predischarge_package_cycle9_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-009"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-09-FINAL-PREDISCHARGE-PACKAGE-v0"
    assert payload.get("status") == "LOCKED_FINAL_PREDISCHARGE_PACKAGE_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    covered_cycles = payload.get("covered_cycles")
    assert covered_cycles == [
        "CYCLE-001",
        "CYCLE-002",
        "CYCLE-003",
        "CYCLE-004",
        "CYCLE-005",
        "CYCLE-006",
        "CYCLE-007",
        "CYCLE-008",
        "CYCLE-009",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-9 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE9_v0: FINAL_PREDISCHARGE_PACKAGE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_final_predischarge_package_cycle9_v0"
    )


def test_sr_cycle10_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE10_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_discharge_criteria_cycle10_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-010"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_CRITERIA_CYCLE10_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("discharge_criteria_token")
        == "SR_COVARIANCE_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED"
    )

    criteria_rows = payload.get("criteria_rows")
    assert criteria_rows == [
        "SR_COVARIANCE_CRITERIA_ROW_01_v0: OBJECT_SCAFFOLD_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_02_v0: CONTRACT_SURFACE_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_03_v0: LORENTZ_INTERVAL_PLACEHOLDER_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_04_v0: VELOCITY_COMPOSITION_PLACEHOLDER_PINNED",
        "SR_COVARIANCE_CRITERIA_ROW_05_v0: STATE_GATE_SYNC_PINNED",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-10 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE10_v0: DISCHARGE_CRITERIA_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_discharge_criteria_cycle10_v0"
    )


def test_sr_cycle11_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE11_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_adjudication_posture_cycle11_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-011"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_ADJUDICATION_POSTURE_CYCLE11_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("adjudication_token")
        == "SR_COVARIANCE_ADJUDICATION_v0: DISCHARGED_v0_PLANNING_CRITERIA_LOCKED_NONCLAIM"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-11 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE11_v0: ADJUDICATION_POSTURE_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_adjudication_posture_cycle11_v0"
    )


def test_sr_cycle12_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE12_ARTIFACT_PATH))

    assert (
        payload.get("artifact_id")
        == "sr_covariance_post_adjudication_contract_freeze_cycle12_v0"
    )
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-012"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_POST_ADJUDICATION_CONTRACT_FREEZE_CYCLE12_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-12-POST-ADJUDICATION-CONTRACT-FREEZE-v0"
    )
    assert (
        payload.get("contract_freeze_token")
        == "SR_COVARIANCE_CONTRACT_FREEZE_v0: CYCLE12_POST_ADJUDICATION_CONTRACT_LOCKED"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-12 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE12_v0: POST_ADJUDICATION_CONTRACT_FREEZE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_post_adjudication_contract_freeze_cycle12_v0"
    )


def test_sr_cycle13_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE13_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_surface_scaffold_cycle13_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-013"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_SURFACE_SCAFFOLD_CYCLE13_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-13-THEOREM-SURFACE-SCAFFOLD-v0"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-13 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE13_v0: THEOREM_SURFACE_SCAFFOLD_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_surface_scaffold_cycle13_v0"
    )


def test_sr_cycle14_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE14_ARTIFACT_PATH))

    assert (
        payload.get("artifact_id")
        == "sr_covariance_theorem_assumption_minimization_cycle14_v0"
    )
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-014"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_ASSUMPTION_MINIMIZATION_CYCLE14_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-14-THEOREM-ASSUMPTION-MINIMIZATION-v0"
    )
    assert payload.get("minimized_bundle_token") == "SR_COVARIANCE_THEOREM_ASSUMPTIONS_v0_min1"
    assert (
        payload.get("reclassification_token")
        == "SR_COVARIANCE_THEOREM_RECLASSIFICATION_v0_MIN1: hInertialFrameTimeHomogeneity_POLICY_TO_MATH_via_sr_interval_invariance_surface_definition"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-14 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE14_v0: THEOREM_ASSUMPTION_MINIMIZATION_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_assumption_minimization_cycle14_v0"
    )


def test_sr_cycle15_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE15_ARTIFACT_PATH))

    assert (
        payload.get("artifact_id")
        == "sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0"
    )
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-015"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_CYCLE15_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-15-THEOREM-ROBUSTNESS-NEGCTRL-SCAFFOLD-v0"
    )

    scaffold_tokens = payload.get("scaffold_tokens")
    assert scaffold_tokens == [
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_SCAFFOLD_v0: TEMPLATE_PINNED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_SCAFFOLD_v0: TEMPLATE_PINNED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_v0: CYCLE15_SCAFFOLD_LOCKED",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-15 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE15_v0: THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0"
    )


def test_sr_cycle16_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE16_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_robustness_row1_cycle16_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-016"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW1_CYCLE16_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-16-THEOREM-ROBUSTNESS-ROW1-v0"
    assert (
        payload.get("robustness_row_token")
        == "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_01_v0: PERTURB_INTERVAL_SCALE_SMALL_PINNED"
    )
    assert (
        payload.get("robustness_progress_token")
        == "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_01_POPULATED"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-16 artifact."
    )
    assert "SR_COVARIANCE_PROGRESS_CYCLE16_v0: THEOREM_ROBUSTNESS_ROW1_TOKEN_PINNED" in witness_tokens

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_theorem_robustness_row1_cycle16_v0"


def test_sr_cycle17_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE17_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_negctrl_row1_cycle17_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-017"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_NEGCTRL_ROW1_CYCLE17_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-17-THEOREM-NEGCTRL-ROW1-v0"
    assert (
        payload.get("negctrl_row_token")
        == "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_01_v0: BROKEN_INTERVAL_INVARIANCE_ASSUMPTION_PINNED"
    )
    assert (
        payload.get("negctrl_progress_token")
        == "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_01_POPULATED"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-17 artifact."
    )
    assert "SR_COVARIANCE_PROGRESS_CYCLE17_v0: THEOREM_NEGCTRL_ROW1_TOKEN_PINNED" in witness_tokens

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_theorem_negctrl_row1_cycle17_v0"


def test_sr_cycle18_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE18_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_robustness_row2_cycle18_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-018"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW2_CYCLE18_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-18-THEOREM-ROBUSTNESS-ROW2-v0"
    assert (
        payload.get("robustness_row_token")
        == "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_02_v0: PERTURB_VELOCITY_COMPOSITION_SMALL_PINNED"
    )
    assert (
        payload.get("robustness_progress_token")
        == "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_02_POPULATED"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-18 artifact."
    )
    assert "SR_COVARIANCE_PROGRESS_CYCLE18_v0: THEOREM_ROBUSTNESS_ROW2_TOKEN_PINNED" in witness_tokens

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_theorem_robustness_row2_cycle18_v0"


def test_sr_cycle19_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE19_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_negctrl_row2_cycle19_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-019"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_NEGCTRL_ROW2_CYCLE19_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-19-THEOREM-NEGCTRL-ROW2-v0"
    assert (
        payload.get("negctrl_row_token")
        == "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_02_v0: BROKEN_VELOCITY_COMPOSITION_CLOSURE_ASSUMPTION_PINNED"
    )
    assert (
        payload.get("negctrl_progress_token")
        == "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_02_POPULATED"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-19 artifact."
    )
    assert "SR_COVARIANCE_PROGRESS_CYCLE19_v0: THEOREM_NEGCTRL_ROW2_TOKEN_PINNED" in witness_tokens

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_theorem_negctrl_row2_cycle19_v0"


def test_sr_cycle20_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE20_ARTIFACT_PATH))

    assert (
        payload.get("artifact_id")
        == "sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0"
    )
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-020"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_CYCLE20_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-20-THEOREM-ROBUSTNESS-NEGCTRL-FAMILY-COMPLETE-v0"
    )
    assert (
        payload.get("family_completion_token")
        == "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_v0: CYCLE20_LOCKED"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-20 artifact."
    )
    assert "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED" in witness_tokens
    assert "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED" in witness_tokens
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE20_v0: THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0"
    )


def test_sr_cycle21_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE21_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_predischarge_criteria_cycle21_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-021"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_CYCLE21_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-21-THEOREM-PREDISCHARGE-CRITERIA-v0"
    assert (
        payload.get("predischarge_criteria_token")
        == "SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_v0: CYCLE21_ROW_LEVEL_CRITERIA_PINNED"
    )

    criteria_rows = payload.get("criteria_rows")
    assert criteria_rows == [
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_01_v0: ASSUMPTION_MINIMIZATION_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_02_v0: ROBUSTNESS_ROWS_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_03_v0: NEGCTRL_ROWS_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_04_v0: RESULTS_SYNC_LOCKED",
    ]

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-21 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE21_v0: THEOREM_PREDISCHARGE_CRITERIA_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_predischarge_criteria_cycle21_v0"
    )


def test_sr_cycle22_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE22_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_adjudication_transition_cycle22_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-022"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_ADJUDICATION_TRANSITION_CYCLE22_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-22-THEOREM-ADJUDICATION-TRANSITION-v0"
    )
    assert (
        payload.get("adjudication_token")
        == "SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_PREDISCHARGE_CRITERIA_LOCKED_NONCLAIM"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-22 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE22_v0: THEOREM_ADJUDICATION_TRANSITION_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_adjudication_transition_cycle22_v0"
    )


def test_sr_cycle23_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE23_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_package_freeze_cycle23_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-023"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_PACKAGE_FREEZE_CYCLE23_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-23-THEOREM-PACKAGE-FREEZE-v0"
    assert (
        payload.get("package_freeze_token")
        == "SR_COVARIANCE_THEOREM_PACKAGE_FREEZE_v0: CYCLE23_FROZEN_CONTENTS_PINNED"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-23 artifact."
    )
    assert "SR_COVARIANCE_PROGRESS_CYCLE23_v0: THEOREM_PACKAGE_FREEZE_TOKEN_PINNED" in witness_tokens

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_theorem_package_freeze_cycle23_v0"


def test_sr_cycle24_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE24_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-024"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_FROZEN_WATCH_REOPEN_POLICY_CYCLE24_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-24-THEOREM-FROZEN-WATCH-REOPEN-POLICY-v0"
    )
    assert (
        payload.get("reopen_policy_token")
        == "SR_COVARIANCE_THEOREM_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-24 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE24_v0: THEOREM_FROZEN_WATCH_REOPEN_POLICY_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0"
    )


def test_sr_cycle25_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE25_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_derivation_promotion_gate_cycle25_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-025"
    assert (
        payload.get("status")
        == "LOCKED_SR_COVARIANCE_THEOREM_DERIVATION_PROMOTION_GATE_CYCLE25_PINNED"
    )
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-25-THEOREM-DERIVATION-PROMOTION-GATE-v0"
    )
    assert (
        payload.get("derivation_promotion_gate_token")
        == "SR_COVARIANCE_THEOREM_DERIVATION_PROMOTION_GATE_v0: CYCLE25_CRITERIA_LOCKED_NONCLAIM"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-25 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE25_v0: THEOREM_DERIVATION_PROMOTION_GATE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_derivation_promotion_gate_cycle25_v0"
    )


def test_sr_cycle26_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE26_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_derivation_completeness_gate_scaffold_cycle26_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-026"
    assert payload.get("status") == "LOCKED_SR_DERIVATION_COMPLETENESS_GATE_SCAFFOLD_CYCLE26_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-26-DERIVATION-COMPLETENESS-GATE-SCAFFOLD-v0"
    )
    assert (
        payload.get("derivation_completeness_gate_token")
        == "SR_DERIVATION_COMPLETENESS_GATE_v0: CYCLE26_SCAFFOLD_PINNED_NONCLAIM"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-26 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE26_v0: DERIVATION_COMPLETENESS_GATE_SCAFFOLD_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_derivation_completeness_gate_scaffold_cycle26_v0"
    )


def test_sr_cycle27_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE27_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_implementation_gate_cycle27_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-027"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_IMPLEMENTATION_GATE_CYCLE27_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-27-THEOREM-OBJECT-IMPLEMENTATION-GATE-v0"
    )
    assert (
        payload.get("theorem_object_implementation_gate_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_IMPLEMENTATION_GATE_v0: CYCLE27_BASE_OBJECT_SET_PINNED_NONCLAIM"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-27 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE27_v0: THEOREM_OBJECT_IMPLEMENTATION_GATE_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_implementation_gate_cycle27_v0"
    )


def test_sr_cycle28_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE28_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_discharge_stub_cycle28_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-028"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_STUB_CYCLE28_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-28-THEOREM-OBJECT-DISCHARGE-STUB-v0"
    )
    assert (
        payload.get("theorem_object_discharge_stub_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_STUB_v0: CYCLE28_BASE_THEOREM_SIGNATURES_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-28 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE28_v0: THEOREM_OBJECT_DISCHARGE_STUB_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_discharge_stub_cycle28_v0"
    )


def test_sr_cycle29_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE29_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_phase_exit_binding_cycle29_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-029"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_PHASE_EXIT_BINDING_CYCLE29_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-29-THEOREM-OBJECT-PHASE-EXIT-BINDING-v0"
    )
    assert (
        payload.get("theorem_object_phase_exit_binding_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_PHASE_EXIT_BINDING_v0: CYCLE29_PHASE_EXIT_TOKENS_PINNED_NONCLAIM"
    )

    phase_exit_tokens = payload.get("phase_exit_tokens")
    assert isinstance(phase_exit_tokens, list) and len(phase_exit_tokens) == 7
    assert (
        "SR_FULL_DERIVATION_PHASE1_EXIT_v0: OBJECT_THEOREM_SURFACES_BOUND_NONCLAIM"
        in phase_exit_tokens
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-29 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE29_v0: THEOREM_OBJECT_PHASE_EXIT_BINDING_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_phase_exit_binding_cycle29_v0"
    )


def test_sr_cycle30_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE30_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_discharge_progression_cycle30_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-030"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PROGRESSION_CYCLE30_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-30-THEOREM-OBJECT-DISCHARGE-PROGRESSION-v0"
    )
    assert (
        payload.get("theorem_object_discharge_progression_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PROGRESSION_v0: CYCLE30_PHASE1_DISCHARGE_PROGRESS_PINNED_NONCLAIM"
    )

    phase1_discharge_rows = payload.get("phase1_discharge_rows")
    assert isinstance(phase1_discharge_rows, list) and len(phase1_discharge_rows) == 4
    assert (
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_PROGRESS_PINNED"
        in phase1_discharge_rows
    )
    assert (
        payload.get("phase1_discharge_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_PROGRESS_v0: ROWS_01_04_POPULATED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-30 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE30_v0: THEOREM_OBJECT_DISCHARGE_PROGRESSION_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_discharge_progression_cycle30_v0"
    )


def test_sr_cycle31_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE31_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-031"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_CYCLE31_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-31-THEOREM-OBJECT-DISCHARGE-ROW01-LOCK-v0"
    )
    assert (
        payload.get("theorem_object_discharge_row01_lock_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_v0: CYCLE31_PHASE1_ROW01_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row01_discharge_status_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_STATUS_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-31 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE31_v0: THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0"
    )


def test_sr_cycle32_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE32_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_discharge_row02_lock_cycle32_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-032"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW02_LOCK_CYCLE32_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-32-THEOREM-OBJECT-DISCHARGE-ROW02-LOCK-v0"
    )
    assert (
        payload.get("theorem_object_discharge_row02_lock_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW02_LOCK_v0: CYCLE32_PHASE1_ROW02_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row02_discharge_status_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_02_STATUS_v0: INTERVAL_INVARIANCE_SURFACE_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-32 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE32_v0: THEOREM_OBJECT_DISCHARGE_ROW02_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_discharge_row02_lock_cycle32_v0"
    )


def test_sr_cycle33_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE33_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_discharge_row03_lock_cycle33_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-033"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW03_LOCK_CYCLE33_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-33-THEOREM-OBJECT-DISCHARGE-ROW03-LOCK-v0"
    )
    assert (
        payload.get("theorem_object_discharge_row03_lock_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW03_LOCK_v0: CYCLE33_PHASE1_ROW03_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row03_discharge_status_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_03_STATUS_v0: VELOCITY_COMPOSITION_SURFACE_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-33 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE33_v0: THEOREM_OBJECT_DISCHARGE_ROW03_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_discharge_row03_lock_cycle33_v0"
    )


def test_sr_cycle34_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE34_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_discharge_row04_lock_cycle34_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-034"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW04_LOCK_CYCLE34_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-34-THEOREM-OBJECT-DISCHARGE-ROW04-LOCK-v0"
    )
    assert (
        payload.get("theorem_object_discharge_row04_lock_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW04_LOCK_v0: CYCLE34_PHASE1_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row04_discharge_status_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_04_STATUS_v0: COVARIANCE_CONTRACT_SURFACE_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-34 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE34_v0: THEOREM_OBJECT_DISCHARGE_ROW04_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_discharge_row04_lock_cycle34_v0"
    )


def test_sr_cycle35_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE35_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_theorem_object_discharge_phase1_completion_transition_cycle35_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-035"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PHASE1_COMPLETION_TRANSITION_CYCLE35_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-35-THEOREM-OBJECT-DISCHARGE-PHASE1-COMPLETE-TRANSITION-v0"
    )
    assert (
        payload.get("theorem_object_discharge_phase1_completion_token")
        == "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PHASE1_COMPLETION_v0: CYCLE35_PHASE1_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-35 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE35_v0: THEOREM_OBJECT_DISCHARGE_PHASE1_COMPLETION_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_theorem_object_discharge_phase1_completion_transition_cycle35_v0"
    )


def test_sr_cycle36_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE36_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_canonical_equivalence_surface_entry_lock_cycle36_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-036"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_ENTRY_LOCK_CYCLE36_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-36-CANONICAL-EQUIVALENCE-SURFACE-ENTRY-LOCK-v0"
    )
    assert (
        payload.get("canonical_equivalence_surface_entry_lock_token")
        == "SR_COVARIANCE_CANONICAL_EQUIVALENCE_SURFACE_ENTRY_LOCK_v0: CYCLE36_PHASE2_ENTRY_SURFACE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-36 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE36_v0: PHASE2_CANONICAL_EQUIVALENCE_SURFACE_ENTRY_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_canonical_equivalence_surface_entry_lock_cycle36_v0"
    )


def test_sr_cycle37_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE37_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_canonical_equivalence_theorem_surface_lock_cycle37_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-037"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_LOCK_CYCLE37_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-37-CANONICAL-EQUIVALENCE-THEOREM-SURFACE-LOCK-v0"
    )
    assert (
        payload.get("canonical_equivalence_theorem_surface_lock_token")
        == "SR_COVARIANCE_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_LOCK_v0: CYCLE37_PHASE2_THEOREM_SURFACE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-37 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE37_v0: PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_canonical_equivalence_theorem_surface_lock_cycle37_v0"
    )


def test_sr_cycle38_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE38_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_canonical_equivalence_theorem_object_linkage_lock_cycle38_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-038"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_LOCK_CYCLE38_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-38-CANONICAL-EQUIVALENCE-THEOREM-OBJECT-LINKAGE-LOCK-v0"
    )
    assert (
        payload.get("canonical_equivalence_theorem_object_linkage_lock_token")
        == "SR_COVARIANCE_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_LOCK_v0: CYCLE38_PHASE2_THEOREM_OBJECT_LINKAGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_object_linkage_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-38 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE38_v0: PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_canonical_equivalence_theorem_object_linkage_lock_cycle38_v0"
    )


def test_sr_cycle39_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE39_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_canonical_equivalence_predischarge_criteria_lock_cycle39_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-039"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_LOCK_CYCLE39_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-39-CANONICAL-EQUIVALENCE-PREDISCHARGE-CRITERIA-LOCK-v0"
    )
    assert (
        payload.get("canonical_equivalence_predischarge_criteria_lock_token")
        == "SR_COVARIANCE_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_LOCK_v0: CYCLE39_PHASE2_PREDISCHARGE_CRITERIA_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_object_linkage_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_predischarge_criteria_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-39 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE39_v0: PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_canonical_equivalence_predischarge_criteria_lock_cycle39_v0"
    )


def test_sr_cycle40_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE40_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_canonical_equivalence_adjudication_transition_lock_cycle40_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-040"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_LOCK_CYCLE40_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-40-CANONICAL-EQUIVALENCE-ADJUDICATION-TRANSITION-LOCK-v0"
    )
    assert (
        payload.get("canonical_equivalence_adjudication_transition_lock_token")
        == "SR_COVARIANCE_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_LOCK_v0: CYCLE40_PHASE2_ADJUDICATION_TRANSITION_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_object_linkage_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_predischarge_criteria_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_adjudication_transition_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-40 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE40_v0: PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_canonical_equivalence_adjudication_transition_lock_cycle40_v0"
    )


def test_sr_cycle41_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE41_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_canonical_equivalence_package_freeze_lock_cycle41_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-041"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_LOCK_CYCLE41_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-41-CANONICAL-EQUIVALENCE-PACKAGE-FREEZE-LOCK-v0"
    )
    assert (
        payload.get("canonical_equivalence_package_freeze_lock_token")
        == "SR_COVARIANCE_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_LOCK_v0: CYCLE41_PHASE2_PACKAGE_FREEZE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_object_linkage_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_predischarge_criteria_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_adjudication_transition_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_package_freeze_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_STATUS_v0: PACKAGE_FREEZE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-41 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE41_v0: PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_canonical_equivalence_package_freeze_lock_cycle41_v0"
    )


def test_sr_cycle42_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE42_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_assumption_minimization_discharge_surface_entry_lock_cycle42_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-042"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_ENTRY_LOCK_CYCLE42_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-42-ASSUMPTION-MINIMIZATION-DISCHARGE-SURFACE-ENTRY-LOCK-v0"
    )
    assert (
        payload.get("assumption_minimization_discharge_surface_entry_lock_token")
        == "SR_COVARIANCE_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE42_PHASE3_ENTRY_SURFACE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_object_linkage_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_predischarge_criteria_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_adjudication_transition_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_package_freeze_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_STATUS_v0: PACKAGE_FREEZE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase3_assumption_minimization_discharge_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-42 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE42_v0: PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_assumption_minimization_discharge_surface_entry_lock_cycle42_v0"
    )


def test_sr_cycle43_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE43_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_assumption_minimization_discharge_theorem_surface_lock_cycle43_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
    assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
    assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-043"
    assert payload.get("status") == "LOCKED_SR_COVARIANCE_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_THEOREM_SURFACE_LOCK_CYCLE43_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"
    assert (
        payload.get("micro_target")
        == "TARGET-SR-COV-MICRO-43-ASSUMPTION-MINIMIZATION-DISCHARGE-THEOREM-SURFACE-LOCK-v0"
    )
    assert (
        payload.get("assumption_minimization_discharge_theorem_surface_lock_token")
        == "SR_COVARIANCE_ASSUMPTION_MINIMIZATION_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE43_PHASE3_THEOREM_SURFACE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_completion_status_token")
        == "SR_FULL_DERIVATION_PHASE1_COMPLETION_STATUS_v0: THEOREM_OBJECT_ROWS_01_04_DISCHARGED_NONCLAIM"
    )
    assert (
        payload.get("phase2_entry_status_token")
        == "SR_FULL_DERIVATION_PHASE2_ENTRY_STATUS_v0: CANONICAL_EQUIVALENCE_SURFACE_ENTRY_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_theorem_object_linkage_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_OBJECT_LINKAGE_STATUS_v0: LINKAGE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_predischarge_criteria_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PREDISCHARGE_CRITERIA_STATUS_v0: CRITERIA_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_adjudication_transition_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase2_canonical_equivalence_package_freeze_status_token")
        == "SR_FULL_DERIVATION_PHASE2_CANONICAL_EQUIVALENCE_PACKAGE_FREEZE_STATUS_v0: PACKAGE_FREEZE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase3_assumption_minimization_discharge_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase3_assumption_minimization_discharge_theorem_surface_status_token")
        == "SR_FULL_DERIVATION_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM"
    )
    assert (
        payload.get("phase1_row_lock_progress_token")
        == "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_ROW02_ROW03_ROW04_DISCHARGE_PINNED_NONCLAIM"
    )
    assert (
        payload.get("lean_module")
        == "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean"
    )

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-43 artifact."
    )
    assert (
        "SR_COVARIANCE_PROGRESS_CYCLE43_v0: PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED"
        in witness_tokens
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_assumption_minimization_discharge_theorem_surface_lock_cycle43_v0"
    )


def test_sr_cycle44_to_cycle48_artifact_schema_and_scope_are_locked() -> None:
    artifact_cases = [
        (
            SR_CYCLE44_ARTIFACT_PATH,
            "sr_covariance_assumption_robustness_discharge_surface_entry_lock_cycle44_v0",
            "CYCLE-044",
            "TARGET-SR-COV-MICRO-44-ROBUSTNESS-DISCHARGE-SURFACE-ENTRY-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_ROBUSTNESS_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE44_PHASE3_ROBUSTNESS_ENTRY_SURFACE_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE44_v0: PHASE3_ROBUSTNESS_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
        ),
        (
            SR_CYCLE45_ARTIFACT_PATH,
            "sr_covariance_assumption_robustness_discharge_theorem_surface_lock_cycle45_v0",
            "CYCLE-045",
            "TARGET-SR-COV-MICRO-45-ROBUSTNESS-DISCHARGE-THEOREM-SURFACE-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_ROBUSTNESS_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE45_PHASE3_ROBUSTNESS_THEOREM_SURFACE_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE45_v0: PHASE3_ROBUSTNESS_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        ),
        (
            SR_CYCLE46_ARTIFACT_PATH,
            "sr_covariance_assumption_negctrl_discharge_surface_entry_lock_cycle46_v0",
            "CYCLE-046",
            "TARGET-SR-COV-MICRO-46-NEGCTRL-DISCHARGE-SURFACE-ENTRY-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_NEGCTRL_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE46_PHASE3_NEGCTRL_ENTRY_SURFACE_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE46_v0: PHASE3_NEGCTRL_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
        ),
        (
            SR_CYCLE47_ARTIFACT_PATH,
            "sr_covariance_assumption_negctrl_discharge_theorem_surface_lock_cycle47_v0",
            "CYCLE-047",
            "TARGET-SR-COV-MICRO-47-NEGCTRL-DISCHARGE-THEOREM-SURFACE-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_NEGCTRL_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE47_PHASE3_NEGCTRL_THEOREM_SURFACE_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE47_v0: PHASE3_NEGCTRL_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        ),
        (
            SR_CYCLE48_ARTIFACT_PATH,
            "sr_covariance_assumption_minimization_discharge_package_freeze_lock_cycle48_v0",
            "CYCLE-048",
            "TARGET-SR-COV-MICRO-48-ASSUMPTION-MINIMIZATION-DISCHARGE-PACKAGE-FREEZE-LOCK-v0",
            "SR_COVARIANCE_ASSUMPTION_MINIMIZATION_DISCHARGE_PACKAGE_FREEZE_LOCK_v0: CYCLE48_PHASE3_PACKAGE_FREEZE_PINNED_NONCLAIM",
            "SR_COVARIANCE_PROGRESS_CYCLE48_v0: PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_PACKAGE_FREEZE_LOCK_TOKEN_PINNED",
        ),
    ]

    for artifact_path, artifact_id, cycle, micro_target, gate_token, progress_token in artifact_cases:
        payload = json.loads(_read(artifact_path))

        assert payload.get("artifact_id") == artifact_id
        assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
        assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
        assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
        assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
        assert payload.get("pillar") == "PILLAR-SR"
        assert payload.get("cycle") == cycle
        assert payload.get("micro_target") == micro_target
        assert payload.get("scope") == "planning_only_non_claim_v0"

        witness_tokens = payload.get("witness_tokens")
        assert isinstance(witness_tokens, list) and witness_tokens, (
            f"witness_tokens must be a non-empty list in SR {cycle} artifact."
        )
        assert gate_token in witness_tokens
        assert progress_token in witness_tokens

        determinism = payload.get("determinism")
        assert isinstance(determinism, dict), "determinism block is required."
        assert determinism.get("schema_version") == "v0"
        assert determinism.get("fingerprint_method") == "literal-json-lock"
        assert determinism.get("content_fingerprint") == artifact_id


def test_sr_cycle49_to_cycle74_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-49-PHASE3-COMPLETION-TRANSITION-LOCK-v0",
        "SR_COVARIANCE_PHASE3_DISCHARGE_COMPLETION_LOCK_v0: CYCLE49_PHASE3_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE49_v0: PHASE3_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE49_ARTIFACT_v0: sr_covariance_phase3_discharge_completion_lock_cycle49_v0",
        "formal/output/sr_covariance_phase3_discharge_completion_lock_cycle49_v0.json",
        "TARGET-SR-COV-MICRO-50-PHASE4-ROBUSTNESS-NEGCTRL-DISCHARGE-SURFACE-ENTRY-LOCK-v0",
        "SR_COVARIANCE_PHASE4_ROBUSTNESS_NEGCTRL_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE50_PHASE4_ENTRY_SURFACE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE50_v0: PHASE4_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE50_ARTIFACT_v0: sr_covariance_phase4_robustness_negctrl_discharge_surface_entry_lock_cycle50_v0",
        "formal/output/sr_covariance_phase4_robustness_negctrl_discharge_surface_entry_lock_cycle50_v0.json",
        "TARGET-SR-COV-MICRO-51-PHASE4-ROBUSTNESS-NEGCTRL-DISCHARGE-THEOREM-SURFACE-LOCK-v0",
        "SR_COVARIANCE_PHASE4_ROBUSTNESS_NEGCTRL_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE51_PHASE4_THEOREM_SURFACE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE51_v0: PHASE4_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE51_ARTIFACT_v0: sr_covariance_phase4_robustness_negctrl_discharge_theorem_surface_lock_cycle51_v0",
        "formal/output/sr_covariance_phase4_robustness_negctrl_discharge_theorem_surface_lock_cycle51_v0.json",
        "TARGET-SR-COV-MICRO-52-PHASE4-ROBUSTNESS-NEGCTRL-DISCHARGE-PACKAGE-FREEZE-LOCK-v0",
        "SR_COVARIANCE_PHASE4_ROBUSTNESS_NEGCTRL_DISCHARGE_PACKAGE_FREEZE_LOCK_v0: CYCLE52_PHASE4_PACKAGE_FREEZE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE52_v0: PHASE4_DISCHARGE_PACKAGE_FREEZE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE52_ARTIFACT_v0: sr_covariance_phase4_robustness_negctrl_discharge_package_freeze_lock_cycle52_v0",
        "formal/output/sr_covariance_phase4_robustness_negctrl_discharge_package_freeze_lock_cycle52_v0.json",
        "TARGET-SR-COV-MICRO-53-PHASE4-COMPLETION-TRANSITION-LOCK-v0",
        "SR_COVARIANCE_PHASE4_DISCHARGE_COMPLETION_LOCK_v0: CYCLE53_PHASE4_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE53_v0: PHASE4_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE53_ARTIFACT_v0: sr_covariance_phase4_discharge_completion_transition_lock_cycle53_v0",
        "formal/output/sr_covariance_phase4_discharge_completion_transition_lock_cycle53_v0.json",
        "TARGET-SR-COV-MICRO-54-PHASE5-DERIVATION-COMPLETENESS-DISCHARGE-SURFACE-ENTRY-LOCK-v0",
        "SR_COVARIANCE_PHASE5_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_ENTRY_LOCK_v0: CYCLE54_PHASE5_ENTRY_SURFACE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE54_v0: PHASE5_DISCHARGE_SURFACE_ENTRY_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE54_ARTIFACT_v0: sr_covariance_phase5_derivation_completeness_discharge_surface_entry_lock_cycle54_v0",
        "formal/output/sr_covariance_phase5_derivation_completeness_discharge_surface_entry_lock_cycle54_v0.json",
        "TARGET-SR-COV-MICRO-55-PHASE5-DERIVATION-COMPLETENESS-DISCHARGE-THEOREM-SURFACE-LOCK-v0",
        "SR_COVARIANCE_PHASE5_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_LOCK_v0: CYCLE55_PHASE5_THEOREM_SURFACE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE55_v0: PHASE5_DISCHARGE_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE55_ARTIFACT_v0: sr_covariance_phase5_derivation_completeness_discharge_theorem_surface_lock_cycle55_v0",
        "formal/output/sr_covariance_phase5_derivation_completeness_discharge_theorem_surface_lock_cycle55_v0.json",
        "TARGET-SR-COV-MICRO-56-PHASE5-COMPLETION-TRANSITION-LOCK-v0",
        "SR_COVARIANCE_PHASE5_DISCHARGE_COMPLETION_LOCK_v0: CYCLE56_PHASE5_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE56_v0: PHASE5_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE56_ARTIFACT_v0: sr_covariance_phase5_discharge_completion_transition_lock_cycle56_v0",
        "formal/output/sr_covariance_phase5_discharge_completion_transition_lock_cycle56_v0.json",
        "TARGET-SR-COV-MICRO-57-PHASE6-INEVITABILITY-NECESSITY-THEOREM-SURFACE-LOCK-v0",
        "SR_COVARIANCE_PHASE6_INEVITABILITY_NECESSITY_THEOREM_SURFACE_LOCK_v0: CYCLE57_PHASE6_NECESSITY_SURFACE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE57_v0: PHASE6_NECESSITY_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE57_ARTIFACT_v0: sr_covariance_phase6_inevitability_necessity_theorem_surface_lock_cycle57_v0",
        "formal/output/sr_covariance_phase6_inevitability_necessity_theorem_surface_lock_cycle57_v0.json",
        "TARGET-SR-COV-MICRO-58-PHASE6-INEVITABILITY-COUNTERFACTUAL-NEGCTRL-THEOREM-SURFACE-LOCK-v0",
        "SR_COVARIANCE_PHASE6_INEVITABILITY_COUNTERFACTUAL_NEGCTRL_THEOREM_SURFACE_LOCK_v0: CYCLE58_PHASE6_COUNTERFACTUAL_NEGCTRL_SURFACE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE58_v0: PHASE6_COUNTERFACTUAL_NEGCTRL_THEOREM_SURFACE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE58_ARTIFACT_v0: sr_covariance_phase6_inevitability_counterfactual_negctrl_theorem_surface_lock_cycle58_v0",
        "formal/output/sr_covariance_phase6_inevitability_counterfactual_negctrl_theorem_surface_lock_cycle58_v0.json",
        "TARGET-SR-COV-MICRO-59-PHASE6-COMPLETION-TRANSITION-LOCK-v0",
        "SR_COVARIANCE_PHASE6_DISCHARGE_COMPLETION_LOCK_v0: CYCLE59_PHASE6_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE59_v0: PHASE6_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE59_ARTIFACT_v0: sr_covariance_phase6_discharge_completion_transition_lock_cycle59_v0",
        "formal/output/sr_covariance_phase6_discharge_completion_transition_lock_cycle59_v0.json",
        "TARGET-SR-COV-MICRO-60-PHASE7-PACKAGE-FREEZE-REOPEN-POLICY-LOCK-v0",
        "SR_COVARIANCE_PHASE7_PACKAGE_FREEZE_REOPEN_POLICY_LOCK_v0: CYCLE60_PHASE7_FREEZE_REOPEN_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE60_v0: PHASE7_FREEZE_REOPEN_POLICY_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE60_ARTIFACT_v0: sr_covariance_phase7_package_freeze_reopen_policy_lock_cycle60_v0",
        "formal/output/sr_covariance_phase7_package_freeze_reopen_policy_lock_cycle60_v0.json",
        "TARGET-SR-COV-MICRO-61-PHASE1-DISCHARGE-GRADE-THEOREM-OBJECT-REPLACEMENT-LOCK-v0",
        "SR_COVARIANCE_PHASE1_DISCHARGE_GRADE_THEOREM_OBJECTS_LOCK_v0: CYCLE61_PHASE1_DISCHARGE_GRADE_OBJECTS_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE61_v0: PHASE1_DISCHARGE_GRADE_THEOREM_OBJECT_REPLACEMENT_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE61_ARTIFACT_v0: sr_covariance_phase1_discharge_grade_theorem_object_replacement_lock_cycle61_v0",
        "formal/output/sr_covariance_phase1_discharge_grade_theorem_object_replacement_lock_cycle61_v0.json",
        "TARGET-SR-COV-MICRO-62-PHASE2-CANONICAL-EQUIVALENCE-THEOREM-DISCHARGE-LOCK-v0",
        "SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_DISCHARGE_LOCK_v0: CYCLE62_PHASE2_EQUIVALENCE_DISCHARGE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE62_v0: PHASE2_CANONICAL_EQUIVALENCE_THEOREM_DISCHARGE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE62_ARTIFACT_v0: sr_covariance_phase2_canonical_equivalence_theorem_discharge_lock_cycle62_v0",
        "formal/output/sr_covariance_phase2_canonical_equivalence_theorem_discharge_lock_cycle62_v0.json",
        "TARGET-SR-COV-MICRO-63-PHASE3-ASSUMPTION-MINIMIZATION-DISCHARGE-COMPLETION-LOCK-v0",
        "SR_COVARIANCE_PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_COMPLETION_LOCK_v0: CYCLE63_PHASE3_ASSUMPTION_MINIMIZATION_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE63_v0: PHASE3_ASSUMPTION_MINIMIZATION_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE63_ARTIFACT_v0: sr_covariance_phase3_assumption_minimization_discharge_completion_lock_cycle63_v0",
        "formal/output/sr_covariance_phase3_assumption_minimization_discharge_completion_lock_cycle63_v0.json",
        "TARGET-SR-COV-MICRO-64-PHASE4-THEOREM-LINKED-ROBUSTNESS-NEGCTRL-DISCHARGE-COMPLETION-LOCK-v0",
        "SR_COVARIANCE_PHASE4_THEOREM_LINKED_ROBUSTNESS_NEGCTRL_DISCHARGE_COMPLETION_LOCK_v0: CYCLE64_PHASE4_THEOREM_LINKED_ROBUSTNESS_NEGCTRL_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE64_v0: PHASE4_THEOREM_LINKED_ROBUSTNESS_NEGCTRL_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE64_ARTIFACT_v0: sr_covariance_phase4_theorem_linked_robustness_negctrl_discharge_completion_lock_cycle64_v0",
        "formal/output/sr_covariance_phase4_theorem_linked_robustness_negctrl_discharge_completion_lock_cycle64_v0.json",
        "TARGET-SR-COV-MICRO-65-PHASE5-DERIVATION-COMPLETENESS-GATE-CLOSURE-LOCK-v0",
        "SR_DERIVATION_COMPLETENESS_GATE_CLOSURE_LOCK_v0: CYCLE65_PHASE5_GATE_CLOSURE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE65_v0: PHASE5_DERIVATION_COMPLETENESS_GATE_CLOSURE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE65_ARTIFACT_v0: sr_covariance_phase5_derivation_completeness_gate_closure_lock_cycle65_v0",
        "formal/output/sr_covariance_phase5_derivation_completeness_gate_closure_lock_cycle65_v0.json",
        "TARGET-SR-COV-MICRO-66-PHASE6-INEVITABILITY-NECESSITY-COUNTERFACTUAL-DISCHARGE-COMPLETION-LOCK-v0",
        "SR_COVARIANCE_PHASE6_INEVITABILITY_NECESSITY_COUNTERFACTUAL_DISCHARGE_COMPLETION_LOCK_v0: CYCLE66_PHASE6_NECESSITY_COUNTERFACTUAL_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE66_v0: PHASE6_INEVITABILITY_NECESSITY_COUNTERFACTUAL_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE66_ARTIFACT_v0: sr_covariance_phase6_inevitability_necessity_counterfactual_discharge_completion_lock_cycle66_v0",
        "formal/output/sr_covariance_phase6_inevitability_necessity_counterfactual_discharge_completion_lock_cycle66_v0.json",
        "TARGET-SR-COV-MICRO-67-PHASE7-GOVERNANCE-PROMOTION-READINESS-LOCK-v0",
        "SR_COVARIANCE_PHASE7_GOVERNANCE_PROMOTION_READINESS_LOCK_v0: CYCLE67_PHASE7_PROMOTION_READINESS_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE67_v0: PHASE7_GOVERNANCE_PROMOTION_READINESS_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE67_ARTIFACT_v0: sr_covariance_phase7_governance_promotion_readiness_lock_cycle67_v0",
        "formal/output/sr_covariance_phase7_governance_promotion_readiness_lock_cycle67_v0.json",
        "TARGET-SR-COV-MICRO-68-PHASE1-DISCHARGE-GRADE-THEOREM-REPLACEMENT-CLOSURE-LOCK-v0",
        "SR_COVARIANCE_PHASE1_DISCHARGE_GRADE_THEOREM_REPLACEMENT_CLOSURE_LOCK_v0: CYCLE68_PHASE1_REPLACEMENT_CLOSURE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE68_v0: PHASE1_DISCHARGE_GRADE_THEOREM_REPLACEMENT_CLOSURE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE68_ARTIFACT_v0: sr_covariance_phase1_discharge_grade_theorem_replacement_closure_lock_cycle68_v0",
        "formal/output/sr_covariance_phase1_discharge_grade_theorem_replacement_closure_lock_cycle68_v0.json",
        "TARGET-SR-COV-MICRO-69-PHASE2-CANONICAL-EQUIVALENCE-THEOREM-DISCHARGE-COMPLETION-LOCK-v0",
        "SR_COVARIANCE_PHASE2_CANONICAL_EQUIVALENCE_THEOREM_DISCHARGE_COMPLETION_LOCK_v0: CYCLE69_PHASE2_EQUIVALENCE_DISCHARGE_COMPLETION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE69_v0: PHASE2_CANONICAL_EQUIVALENCE_THEOREM_DISCHARGE_COMPLETION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE69_ARTIFACT_v0: sr_covariance_phase2_canonical_equivalence_theorem_discharge_completion_lock_cycle69_v0",
        "formal/output/sr_covariance_phase2_canonical_equivalence_theorem_discharge_completion_lock_cycle69_v0.json",
        "TARGET-SR-COV-MICRO-70-PHASE5-DERIVATION-COMPLETENESS-FAILURE-TRIGGER-DISCHARGE-LOCK-v0",
        "SR_DERIVATION_COMPLETENESS_FAILURE_TRIGGER_DISCHARGE_LOCK_v0: CYCLE70_PHASE5_FAILURE_TRIGGER_DISCHARGE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE70_v0: PHASE5_FAILURE_TRIGGER_DISCHARGE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE70_ARTIFACT_v0: sr_covariance_phase5_derivation_completeness_failure_trigger_discharge_lock_cycle70_v0",
        "formal/output/sr_covariance_phase5_derivation_completeness_failure_trigger_discharge_lock_cycle70_v0.json",
        "TARGET-SR-COV-MICRO-71-PHASE6-INEVITABILITY-THEOREM-DISCHARGE-CLOSURE-LOCK-v0",
        "SR_COVARIANCE_PHASE6_INEVITABILITY_THEOREM_DISCHARGE_CLOSURE_LOCK_v0: CYCLE71_PHASE6_INEVITABILITY_THEOREM_CLOSURE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE71_v0: PHASE6_INEVITABILITY_THEOREM_DISCHARGE_CLOSURE_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE71_ARTIFACT_v0: sr_covariance_phase6_inevitability_theorem_discharge_closure_lock_cycle71_v0",
        "formal/output/sr_covariance_phase6_inevitability_theorem_discharge_closure_lock_cycle71_v0.json",
        "TARGET-SR-COV-MICRO-72-PHASE7-GOVERNANCE-CLAIM-PROMOTION-EXECUTION-LOCK-v0",
        "SR_COVARIANCE_PHASE7_GOVERNANCE_CLAIM_PROMOTION_EXECUTION_LOCK_v0: CYCLE72_PHASE7_PROMOTION_EXECUTION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE72_v0: PHASE7_GOVERNANCE_CLAIM_PROMOTION_EXECUTION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE72_ARTIFACT_v0: sr_covariance_phase7_governance_claim_promotion_execution_lock_cycle72_v0",
        "formal/output/sr_covariance_phase7_governance_claim_promotion_execution_lock_cycle72_v0.json",
        "TARGET-SR-COV-MICRO-73-PHASE5-PHASE6-THEOREM-DISCHARGE-ADJUDICATION-TRANSITION-LOCK-v0",
        "SR_COVARIANCE_PHASE5_PHASE6_THEOREM_DISCHARGE_ADJUDICATION_LOCK_v0: CYCLE73_PHASE5_PHASE6_ADJUDICATION_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE73_v0: PHASE5_PHASE6_THEOREM_DISCHARGE_ADJUDICATION_TRANSITION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE73_ARTIFACT_v0: sr_covariance_phase5_phase6_theorem_discharge_adjudication_transition_lock_cycle73_v0",
        "formal/output/sr_covariance_phase5_phase6_theorem_discharge_adjudication_transition_lock_cycle73_v0.json",
        "TARGET-SR-COV-MICRO-74-CLAIM-LABEL-AND-PILLAR-CLOSURE-TRANSITION-LOCK-v0",
        "SR_COVARIANCE_CLAIM_LABEL_AND_PILLAR_CLOSURE_TRANSITION_LOCK_v0: CYCLE74_RESULTS_MATRIX_CLOSURE_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE74_v0: CLAIM_LABEL_AND_PILLAR_CLOSURE_TRANSITION_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE74_ARTIFACT_v0: sr_covariance_claim_label_and_pillar_closure_transition_lock_cycle74_v0",
        "formal/output/sr_covariance_claim_label_and_pillar_closure_transition_lock_cycle74_v0.json",
    ]

    missing_target = [tok for tok in required_tokens if tok not in target_text]
    missing_state = [tok for tok in required_tokens if tok not in state_text]
    assert not missing_target, "Missing cycle49-74 token(s) in SR target: " + ", ".join(missing_target)
    assert not missing_state, "Missing cycle49-74 token(s) in State of the Theory: " + ", ".join(missing_state)


def test_sr_cycle49_to_cycle74_artifact_schema_and_scope_are_locked() -> None:
    artifact_cases = [
        ("sr_covariance_phase3_discharge_completion_lock_cycle49_v0.json", "sr_covariance_phase3_discharge_completion_lock_cycle49_v0", "CYCLE-049"),
        ("sr_covariance_phase4_robustness_negctrl_discharge_surface_entry_lock_cycle50_v0.json", "sr_covariance_phase4_robustness_negctrl_discharge_surface_entry_lock_cycle50_v0", "CYCLE-050"),
        ("sr_covariance_phase4_robustness_negctrl_discharge_theorem_surface_lock_cycle51_v0.json", "sr_covariance_phase4_robustness_negctrl_discharge_theorem_surface_lock_cycle51_v0", "CYCLE-051"),
        ("sr_covariance_phase4_robustness_negctrl_discharge_package_freeze_lock_cycle52_v0.json", "sr_covariance_phase4_robustness_negctrl_discharge_package_freeze_lock_cycle52_v0", "CYCLE-052"),
        ("sr_covariance_phase4_discharge_completion_transition_lock_cycle53_v0.json", "sr_covariance_phase4_discharge_completion_transition_lock_cycle53_v0", "CYCLE-053"),
        ("sr_covariance_phase5_derivation_completeness_discharge_surface_entry_lock_cycle54_v0.json", "sr_covariance_phase5_derivation_completeness_discharge_surface_entry_lock_cycle54_v0", "CYCLE-054"),
        ("sr_covariance_phase5_derivation_completeness_discharge_theorem_surface_lock_cycle55_v0.json", "sr_covariance_phase5_derivation_completeness_discharge_theorem_surface_lock_cycle55_v0", "CYCLE-055"),
        ("sr_covariance_phase5_discharge_completion_transition_lock_cycle56_v0.json", "sr_covariance_phase5_discharge_completion_transition_lock_cycle56_v0", "CYCLE-056"),
        ("sr_covariance_phase6_inevitability_necessity_theorem_surface_lock_cycle57_v0.json", "sr_covariance_phase6_inevitability_necessity_theorem_surface_lock_cycle57_v0", "CYCLE-057"),
        ("sr_covariance_phase6_inevitability_counterfactual_negctrl_theorem_surface_lock_cycle58_v0.json", "sr_covariance_phase6_inevitability_counterfactual_negctrl_theorem_surface_lock_cycle58_v0", "CYCLE-058"),
        ("sr_covariance_phase6_discharge_completion_transition_lock_cycle59_v0.json", "sr_covariance_phase6_discharge_completion_transition_lock_cycle59_v0", "CYCLE-059"),
        ("sr_covariance_phase7_package_freeze_reopen_policy_lock_cycle60_v0.json", "sr_covariance_phase7_package_freeze_reopen_policy_lock_cycle60_v0", "CYCLE-060"),
        ("sr_covariance_phase1_discharge_grade_theorem_object_replacement_lock_cycle61_v0.json", "sr_covariance_phase1_discharge_grade_theorem_object_replacement_lock_cycle61_v0", "CYCLE-061"),
        ("sr_covariance_phase2_canonical_equivalence_theorem_discharge_lock_cycle62_v0.json", "sr_covariance_phase2_canonical_equivalence_theorem_discharge_lock_cycle62_v0", "CYCLE-062"),
        ("sr_covariance_phase3_assumption_minimization_discharge_completion_lock_cycle63_v0.json", "sr_covariance_phase3_assumption_minimization_discharge_completion_lock_cycle63_v0", "CYCLE-063"),
        ("sr_covariance_phase4_theorem_linked_robustness_negctrl_discharge_completion_lock_cycle64_v0.json", "sr_covariance_phase4_theorem_linked_robustness_negctrl_discharge_completion_lock_cycle64_v0", "CYCLE-064"),
        ("sr_covariance_phase5_derivation_completeness_gate_closure_lock_cycle65_v0.json", "sr_covariance_phase5_derivation_completeness_gate_closure_lock_cycle65_v0", "CYCLE-065"),
        ("sr_covariance_phase6_inevitability_necessity_counterfactual_discharge_completion_lock_cycle66_v0.json", "sr_covariance_phase6_inevitability_necessity_counterfactual_discharge_completion_lock_cycle66_v0", "CYCLE-066"),
        ("sr_covariance_phase7_governance_promotion_readiness_lock_cycle67_v0.json", "sr_covariance_phase7_governance_promotion_readiness_lock_cycle67_v0", "CYCLE-067"),
        ("sr_covariance_phase1_discharge_grade_theorem_replacement_closure_lock_cycle68_v0.json", "sr_covariance_phase1_discharge_grade_theorem_replacement_closure_lock_cycle68_v0", "CYCLE-068"),
        ("sr_covariance_phase2_canonical_equivalence_theorem_discharge_completion_lock_cycle69_v0.json", "sr_covariance_phase2_canonical_equivalence_theorem_discharge_completion_lock_cycle69_v0", "CYCLE-069"),
        ("sr_covariance_phase5_derivation_completeness_failure_trigger_discharge_lock_cycle70_v0.json", "sr_covariance_phase5_derivation_completeness_failure_trigger_discharge_lock_cycle70_v0", "CYCLE-070"),
        ("sr_covariance_phase6_inevitability_theorem_discharge_closure_lock_cycle71_v0.json", "sr_covariance_phase6_inevitability_theorem_discharge_closure_lock_cycle71_v0", "CYCLE-071"),
        ("sr_covariance_phase7_governance_claim_promotion_execution_lock_cycle72_v0.json", "sr_covariance_phase7_governance_claim_promotion_execution_lock_cycle72_v0", "CYCLE-072"),
        ("sr_covariance_phase5_phase6_theorem_discharge_adjudication_transition_lock_cycle73_v0.json", "sr_covariance_phase5_phase6_theorem_discharge_adjudication_transition_lock_cycle73_v0", "CYCLE-073"),
        ("sr_covariance_claim_label_and_pillar_closure_transition_lock_cycle74_v0.json", "sr_covariance_claim_label_and_pillar_closure_transition_lock_cycle74_v0", "CYCLE-074"),
    ]

    for filename, artifact_id, cycle in artifact_cases:
        artifact_path = REPO_ROOT / "formal" / "output" / filename
        payload = json.loads(_read(artifact_path))

        assert payload.get("artifact_id") == artifact_id
        assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
        assert payload.get("subtarget_id") == "TARGET-SR-COV-THEOREM-SURFACE-PLAN"
        assert payload.get("derivation_gate_target_id") == "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN"
        assert payload.get("enforcement_roadmap_target_id") == "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN"
        assert payload.get("pillar") == "PILLAR-SR"
        assert payload.get("cycle") == cycle
        assert payload.get("scope") == "planning_only_non_claim_v0"

        witness_tokens = payload.get("witness_tokens")
        assert isinstance(witness_tokens, list) and witness_tokens

        determinism = payload.get("determinism")
        assert isinstance(determinism, dict)
        assert determinism.get("schema_version") == "v0"
        assert determinism.get("fingerprint_method") == "literal-json-lock"
        assert determinism.get("content_fingerprint") == artifact_id
