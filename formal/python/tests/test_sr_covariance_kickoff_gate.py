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
