from __future__ import annotations

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
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
SR_THEOREM_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sr_theorem_surface_target_pins_required_tokens() -> None:
    text = _read(SR_THEOREM_TARGET_PATH)

    required_tokens = [
        "DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0",
        "TARGET-SR-COV-THEOREM-SURFACE-PLAN",
        "TARGET-SR-COV-PLAN",
        "SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_SCAFFOLD_CONDITIONAL_NONCLAIM",
        "sr_covariance_interval_invariance_surface_v0",
        "SR_COVARIANCE_THEOREM_ASSUMPTIONS_v0",
        "SR_COVARIANCE_DOMAIN_LIMITS_v0: INERTIAL_FRAMES_BOUNDED_SCOPE",
        "SR_COVARIANCE_FALSIFIABILITY_HOOK_v0: EXPLICIT_INVALIDATION_CONDITION_DECLARED",
        "TARGET-SR-COV-MICRO-13-THEOREM-SURFACE-SCAFFOLD-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE13_v0: THEOREM_SURFACE_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE13_ARTIFACT_v0: sr_covariance_theorem_surface_scaffold_cycle13_v0",
        "formal/output/sr_covariance_theorem_surface_scaffold_cycle13_v0.json",
        "SR_COVARIANCE_THEOREM_ASSUMPTIONS_v0_min1",
        "SR_COVARIANCE_THEOREM_RECLASSIFICATION_v0_MIN1: hInertialFrameTimeHomogeneity_POLICY_TO_MATH_via_sr_interval_invariance_surface_definition",
        "SR_COVARIANCE_THEOREM_ASSUMPTION_LEDGER_PROGRESS_v0: BUNDLE_MIN1_POPULATED",
        "TARGET-SR-COV-MICRO-14-THEOREM-ASSUMPTION-MINIMIZATION-v0",
        "SR_COVARIANCE_THEOREM_ASSUMPTION_MINIMIZATION_v0: CYCLE14_MIN1_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE14_v0: THEOREM_ASSUMPTION_MINIMIZATION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE14_ARTIFACT_v0: sr_covariance_theorem_assumption_minimization_cycle14_v0",
        "formal/output/sr_covariance_theorem_assumption_minimization_cycle14_v0.json",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_SCAFFOLD_v0: TEMPLATE_PINNED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_SCAFFOLD_v0: TEMPLATE_PINNED",
        "TARGET-SR-COV-MICRO-15-THEOREM-ROBUSTNESS-NEGCTRL-SCAFFOLD-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_v0: CYCLE15_SCAFFOLD_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE15_v0: THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE15_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0",
        "formal/output/sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0.json",
        "TARGET-SR-COV-MICRO-16-THEOREM-ROBUSTNESS-ROW1-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_01_v0: PERTURB_INTERVAL_SCALE_SMALL_PINNED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_01_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE16_v0: THEOREM_ROBUSTNESS_ROW1_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE16_ARTIFACT_v0: sr_covariance_theorem_robustness_row1_cycle16_v0",
        "formal/output/sr_covariance_theorem_robustness_row1_cycle16_v0.json",
        "TARGET-SR-COV-MICRO-17-THEOREM-NEGCTRL-ROW1-v0",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_01_v0: BROKEN_INTERVAL_INVARIANCE_ASSUMPTION_PINNED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_01_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE17_v0: THEOREM_NEGCTRL_ROW1_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE17_ARTIFACT_v0: sr_covariance_theorem_negctrl_row1_cycle17_v0",
        "formal/output/sr_covariance_theorem_negctrl_row1_cycle17_v0.json",
        "TARGET-SR-COV-MICRO-18-THEOREM-ROBUSTNESS-ROW2-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_02_v0: PERTURB_VELOCITY_COMPOSITION_SMALL_PINNED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_02_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE18_v0: THEOREM_ROBUSTNESS_ROW2_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE18_ARTIFACT_v0: sr_covariance_theorem_robustness_row2_cycle18_v0",
        "formal/output/sr_covariance_theorem_robustness_row2_cycle18_v0.json",
        "TARGET-SR-COV-MICRO-19-THEOREM-NEGCTRL-ROW2-v0",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_02_v0: BROKEN_VELOCITY_COMPOSITION_CLOSURE_ASSUMPTION_PINNED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_02_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE19_v0: THEOREM_NEGCTRL_ROW2_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE19_ARTIFACT_v0: sr_covariance_theorem_negctrl_row2_cycle19_v0",
        "formal/output/sr_covariance_theorem_negctrl_row2_cycle19_v0.json",
        "TARGET-SR-COV-MICRO-20-THEOREM-ROBUSTNESS-NEGCTRL-FAMILY-COMPLETE-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_v0: CYCLE20_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE20_v0: THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE20_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0",
        "formal/output/sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0.json",
        "TARGET-SR-COV-MICRO-21-THEOREM-PREDISCHARGE-CRITERIA-v0",
        "SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_v0: CYCLE21_ROW_LEVEL_CRITERIA_PINNED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_01_v0: ASSUMPTION_MINIMIZATION_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_02_v0: ROBUSTNESS_ROWS_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_03_v0: NEGCTRL_ROWS_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_04_v0: RESULTS_SYNC_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE21_v0: THEOREM_PREDISCHARGE_CRITERIA_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE21_ARTIFACT_v0: sr_covariance_theorem_predischarge_criteria_cycle21_v0",
        "formal/output/sr_covariance_theorem_predischarge_criteria_cycle21_v0.json",
        "TARGET-SR-COV-MICRO-22-THEOREM-ADJUDICATION-TRANSITION-v0",
        "SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_PREDISCHARGE_CRITERIA_LOCKED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE22_v0: THEOREM_ADJUDICATION_TRANSITION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE22_ARTIFACT_v0: sr_covariance_theorem_adjudication_transition_cycle22_v0",
        "formal/output/sr_covariance_theorem_adjudication_transition_cycle22_v0.json",
        "TARGET-SR-COV-MICRO-23-THEOREM-PACKAGE-FREEZE-v0",
        "SR_COVARIANCE_THEOREM_PACKAGE_FREEZE_v0: CYCLE23_FROZEN_CONTENTS_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE23_v0: THEOREM_PACKAGE_FREEZE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE23_ARTIFACT_v0: sr_covariance_theorem_package_freeze_cycle23_v0",
        "formal/output/sr_covariance_theorem_package_freeze_cycle23_v0.json",
        "TARGET-SR-COV-MICRO-24-THEOREM-FROZEN-WATCH-REOPEN-POLICY-v0",
        "SR_COVARIANCE_THEOREM_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "SR_COVARIANCE_PROGRESS_CYCLE24_v0: THEOREM_FROZEN_WATCH_REOPEN_POLICY_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE24_ARTIFACT_v0: sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0",
        "formal/output/sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0.json",
        "TARGET-SR-COV-MICRO-25-THEOREM-DERIVATION-PROMOTION-GATE-v0",
        "SR_COVARIANCE_THEOREM_DERIVATION_PROMOTION_GATE_v0: CYCLE25_CRITERIA_LOCKED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE25_v0: THEOREM_DERIVATION_PROMOTION_GATE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE25_ARTIFACT_v0: sr_covariance_theorem_derivation_promotion_gate_cycle25_v0",
        "formal/output/sr_covariance_theorem_derivation_promotion_gate_cycle25_v0.json",
    ]

    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Missing required SR theorem-surface target token(s): " + ", ".join(missing)


def test_sr_theorem_surface_tokens_are_synced_in_state_and_results() -> None:
    state_text = _read(STATE_PATH)
    results_text = _read(RESULTS_PATH)

    state_tokens = [
        "TARGET-SR-COV-MICRO-13-THEOREM-SURFACE-SCAFFOLD-v0",
        "formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0.md",
        "SR_COVARIANCE_PROGRESS_CYCLE13_v0: THEOREM_SURFACE_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE13_ARTIFACT_v0: sr_covariance_theorem_surface_scaffold_cycle13_v0",
        "TARGET-SR-COV-MICRO-14-THEOREM-ASSUMPTION-MINIMIZATION-v0",
        "SR_COVARIANCE_THEOREM_ASSUMPTION_MINIMIZATION_v0: CYCLE14_MIN1_LOCKED",
        "SR_COVARIANCE_THEOREM_ASSUMPTIONS_v0_min1",
        "SR_COVARIANCE_PROGRESS_CYCLE14_v0: THEOREM_ASSUMPTION_MINIMIZATION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE14_ARTIFACT_v0: sr_covariance_theorem_assumption_minimization_cycle14_v0",
        "TARGET-SR-COV-MICRO-15-THEOREM-ROBUSTNESS-NEGCTRL-SCAFFOLD-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_SCAFFOLD_v0: TEMPLATE_PINNED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_SCAFFOLD_v0: TEMPLATE_PINNED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_v0: CYCLE15_SCAFFOLD_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE15_v0: THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE15_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0",
        "TARGET-SR-COV-MICRO-16-THEOREM-ROBUSTNESS-ROW1-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_01_v0: PERTURB_INTERVAL_SCALE_SMALL_PINNED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_01_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE16_v0: THEOREM_ROBUSTNESS_ROW1_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE16_ARTIFACT_v0: sr_covariance_theorem_robustness_row1_cycle16_v0",
        "TARGET-SR-COV-MICRO-17-THEOREM-NEGCTRL-ROW1-v0",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_01_v0: BROKEN_INTERVAL_INVARIANCE_ASSUMPTION_PINNED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_01_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE17_v0: THEOREM_NEGCTRL_ROW1_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE17_ARTIFACT_v0: sr_covariance_theorem_negctrl_row1_cycle17_v0",
        "TARGET-SR-COV-MICRO-18-THEOREM-ROBUSTNESS-ROW2-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_02_v0: PERTURB_VELOCITY_COMPOSITION_SMALL_PINNED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ROW_02_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE18_v0: THEOREM_ROBUSTNESS_ROW2_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE18_ARTIFACT_v0: sr_covariance_theorem_robustness_row2_cycle18_v0",
        "TARGET-SR-COV-MICRO-19-THEOREM-NEGCTRL-ROW2-v0",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_02_v0: BROKEN_VELOCITY_COMPOSITION_CLOSURE_ASSUMPTION_PINNED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ROW_02_POPULATED",
        "SR_COVARIANCE_PROGRESS_CYCLE19_v0: THEOREM_NEGCTRL_ROW2_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE19_ARTIFACT_v0: sr_covariance_theorem_negctrl_row2_cycle19_v0",
        "TARGET-SR-COV-MICRO-20-THEOREM-ROBUSTNESS-NEGCTRL-FAMILY-COMPLETE-v0",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED",
        "SR_COVARIANCE_THEOREM_NEGCTRL_PROGRESS_v0: ALL_REQUIRED_ROWS_POPULATED",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_v0: CYCLE20_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE20_v0: THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE20_ARTIFACT_v0: sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0",
        "TARGET-SR-COV-MICRO-21-THEOREM-PREDISCHARGE-CRITERIA-v0",
        "SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_v0: CYCLE21_ROW_LEVEL_CRITERIA_PINNED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_01_v0: ASSUMPTION_MINIMIZATION_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_02_v0: ROBUSTNESS_ROWS_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_03_v0: NEGCTRL_ROWS_LOCKED",
        "SR_COVARIANCE_THEOREM_CRITERIA_ROW_04_v0: RESULTS_SYNC_LOCKED",
        "SR_COVARIANCE_PROGRESS_CYCLE21_v0: THEOREM_PREDISCHARGE_CRITERIA_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE21_ARTIFACT_v0: sr_covariance_theorem_predischarge_criteria_cycle21_v0",
        "TARGET-SR-COV-MICRO-22-THEOREM-ADJUDICATION-TRANSITION-v0",
        "SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_PREDISCHARGE_CRITERIA_LOCKED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE22_v0: THEOREM_ADJUDICATION_TRANSITION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE22_ARTIFACT_v0: sr_covariance_theorem_adjudication_transition_cycle22_v0",
        "TARGET-SR-COV-MICRO-23-THEOREM-PACKAGE-FREEZE-v0",
        "SR_COVARIANCE_THEOREM_PACKAGE_FREEZE_v0: CYCLE23_FROZEN_CONTENTS_PINNED",
        "SR_COVARIANCE_PROGRESS_CYCLE23_v0: THEOREM_PACKAGE_FREEZE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE23_ARTIFACT_v0: sr_covariance_theorem_package_freeze_cycle23_v0",
        "TARGET-SR-COV-MICRO-24-THEOREM-FROZEN-WATCH-REOPEN-POLICY-v0",
        "SR_COVARIANCE_THEOREM_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "SR_COVARIANCE_PROGRESS_CYCLE24_v0: THEOREM_FROZEN_WATCH_REOPEN_POLICY_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE24_ARTIFACT_v0: sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0",
        "TARGET-SR-COV-MICRO-25-THEOREM-DERIVATION-PROMOTION-GATE-v0",
        "SR_COVARIANCE_THEOREM_DERIVATION_PROMOTION_GATE_v0: CYCLE25_CRITERIA_LOCKED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE25_v0: THEOREM_DERIVATION_PROMOTION_GATE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE25_ARTIFACT_v0: sr_covariance_theorem_derivation_promotion_gate_cycle25_v0",
    ]
    for token in state_tokens:
        assert token in state_text, f"Missing SR theorem-surface token in state: {token}"

    results_tokens = [
        "TOE-SR-THM-01",
        "`T-CONDITIONAL`",
        "formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0.md",
        "formal/docs/paper/ASSUMPTION_REGISTRY_v1.md",
        "SR_COVARIANCE_THEOREM_ASSUMPTION_MINIMIZATION_v0: CYCLE14_MIN1_LOCKED",
        "formal/output/sr_covariance_theorem_assumption_minimization_cycle14_v0.json",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_SCAFFOLD_v0: CYCLE15_SCAFFOLD_LOCKED",
        "formal/output/sr_covariance_theorem_robustness_negctrl_scaffold_cycle15_v0.json",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_01_v0: PERTURB_INTERVAL_SCALE_SMALL_PINNED",
        "formal/output/sr_covariance_theorem_robustness_row1_cycle16_v0.json",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_01_v0: BROKEN_INTERVAL_INVARIANCE_ASSUMPTION_PINNED",
        "formal/output/sr_covariance_theorem_negctrl_row1_cycle17_v0.json",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_ROW_02_v0: PERTURB_VELOCITY_COMPOSITION_SMALL_PINNED",
        "formal/output/sr_covariance_theorem_robustness_row2_cycle18_v0.json",
        "SR_COVARIANCE_THEOREM_NEGCTRL_ROW_02_v0: BROKEN_VELOCITY_COMPOSITION_CLOSURE_ASSUMPTION_PINNED",
        "formal/output/sr_covariance_theorem_negctrl_row2_cycle19_v0.json",
        "SR_COVARIANCE_THEOREM_ROBUSTNESS_NEGCTRL_FAMILY_COMPLETION_v0: CYCLE20_LOCKED",
        "formal/output/sr_covariance_theorem_robustness_negctrl_family_completion_cycle20_v0.json",
        "SR_COVARIANCE_THEOREM_PREDISCHARGE_CRITERIA_v0: CYCLE21_ROW_LEVEL_CRITERIA_PINNED",
        "formal/output/sr_covariance_theorem_predischarge_criteria_cycle21_v0.json",
        "SR_COVARIANCE_THEOREM_SURFACE_ADJUDICATION_v0: DISCHARGED_v0_PREDISCHARGE_CRITERIA_LOCKED_NONCLAIM",
        "formal/output/sr_covariance_theorem_adjudication_transition_cycle22_v0.json",
        "SR_COVARIANCE_THEOREM_PACKAGE_FREEZE_v0: CYCLE23_FROZEN_CONTENTS_PINNED",
        "formal/output/sr_covariance_theorem_package_freeze_cycle23_v0.json",
        "SR_COVARIANCE_THEOREM_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "formal/output/sr_covariance_theorem_frozen_watch_reopen_policy_cycle24_v0.json",
        "SR_COVARIANCE_THEOREM_DERIVATION_PROMOTION_GATE_v0: CYCLE25_CRITERIA_LOCKED_NONCLAIM",
        "formal/output/sr_covariance_theorem_derivation_promotion_gate_cycle25_v0.json",
        "Not a full SR dynamics derivation claim and not an inevitability claim.",
    ]
    for token in results_tokens:
        assert token in results_text, f"Missing SR theorem-surface token in results table: {token}"


def test_sr_roadmap_active_row_includes_theorem_surface_target() -> None:
    roadmap_text = _read(ROADMAP_PATH)

    required_tokens = [
        "| `PILLAR-SR` | `ACTIVE` | `TARGET-SR-COV-PLAN;TARGET-SR-COV-THEOREM-SURFACE-PLAN`",
        "formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md;formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0.md",
    ]

    for token in required_tokens:
        assert token in roadmap_text, f"Missing SR theorem-surface roadmap token: {token}"
