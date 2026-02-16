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
SR_ENFORCEMENT_ROADMAP_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sr_enforcement_roadmap_exists_and_pins_authoritative_tokens() -> None:
    text = _read(SR_ENFORCEMENT_ROADMAP_PATH)

    required_tokens = [
        "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0",
        "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN",
        "SR_FULL_DERIVATION_ENFORCEMENT_ADJUDICATION: DISCHARGED_v0_ROADMAP_PINNED",
        "Authoritative no-deviation rule",
        "Phase I — Theorem-object realization",
        "Phase II — Canonical equivalence theorem",
        "Phase III — Assumption minimization discharge",
        "Phase IV — Robustness + negative-control discharge",
        "Phase V — Derivation-completeness gate discharge",
        "Phase VI — Inevitability gate discharge",
        "Phase VII — Package freeze and reopen policy",
        "Cycle-029 phase-exit token binding lock",
        "TARGET-SR-COV-MICRO-29-THEOREM-OBJECT-PHASE-EXIT-BINDING-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_PHASE_EXIT_BINDING_v0: CYCLE29_PHASE_EXIT_TOKENS_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_EXIT_v0: OBJECT_THEOREM_SURFACES_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_EXIT_v0: CANONICAL_EQUIVALENCE_SURFACE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE3_EXIT_v0: ASSUMPTION_MINIMIZATION_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE4_EXIT_v0: ROBUSTNESS_NEGCTRL_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE5_EXIT_v0: DERIVATION_COMPLETENESS_GATE_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE6_EXIT_v0: INEVITABILITY_GATE_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE7_EXIT_v0: PACKAGE_FREEZE_REOPEN_POLICY_BOUND_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE29_v0: THEOREM_OBJECT_PHASE_EXIT_BINDING_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE29_ARTIFACT_v0: sr_covariance_theorem_object_phase_exit_binding_cycle29_v0",
        "formal/output/sr_covariance_theorem_object_phase_exit_binding_cycle29_v0.json",
        "Cycle-030 phase-I theorem-object discharge progression lock",
        "TARGET-SR-COV-MICRO-30-THEOREM-OBJECT-DISCHARGE-PROGRESSION-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PROGRESSION_v0: CYCLE30_PHASE1_DISCHARGE_PROGRESS_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_02_v0: INTERVAL_INVARIANCE_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_03_v0: VELOCITY_COMPOSITION_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_04_v0: COVARIANCE_CONTRACT_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_PROGRESS_v0: ROWS_01_04_POPULATED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE30_v0: THEOREM_OBJECT_DISCHARGE_PROGRESSION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE30_ARTIFACT_v0: sr_covariance_theorem_object_discharge_progression_cycle30_v0",
        "formal/output/sr_covariance_theorem_object_discharge_progression_cycle30_v0.json",
        "Cycle-031 phase-I theorem-object discharge row-01 lock",
        "TARGET-SR-COV-MICRO-31-THEOREM-OBJECT-DISCHARGE-ROW01-LOCK-v0",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_v0: CYCLE31_PHASE1_ROW01_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_STATUS_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_DISCHARGE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE31_v0: THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE31_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0",
        "formal/output/sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0.json",
        "MATH|DEF|POLICY|SCOPE",
        "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN",
        "TOE-SR-THM-01",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "test_sr_full_derivation_enforcement_roadmap_gate.py",
    ]

    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required SR enforcement-roadmap token(s): " + ", ".join(missing)


def test_sr_enforcement_roadmap_is_synced_with_state_and_physics_roadmap() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_state_tokens = [
        "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "SR_FULL_DERIVATION_ENFORCEMENT_ADJUDICATION: DISCHARGED_v0_ROADMAP_PINNED",
        "SR_FULL_DERIVATION_ENFORCEMENT_MODE_v0: AUTHORITATIVE_NO_DEVIATION",
        "SR_FULL_DERIVATION_ENFORCEMENT_PHASE_ORDER_v0: PHASE1_OBJECTS>PHASE2_EQUIV>PHASE3_ASSUMPTIONS>PHASE4_ROBUST_NEGCTRL>PHASE5_DERIVATION_GATE>PHASE6_INEVITABILITY>PHASE7_FREEZE",
        "SR_COVARIANCE_THEOREM_OBJECT_PHASE_EXIT_BINDING_v0: CYCLE29_PHASE_EXIT_TOKENS_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_EXIT_v0: OBJECT_THEOREM_SURFACES_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE2_EXIT_v0: CANONICAL_EQUIVALENCE_SURFACE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE3_EXIT_v0: ASSUMPTION_MINIMIZATION_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE4_EXIT_v0: ROBUSTNESS_NEGCTRL_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE5_EXIT_v0: DERIVATION_COMPLETENESS_GATE_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE6_EXIT_v0: INEVITABILITY_GATE_DISCHARGE_BOUND_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE7_EXIT_v0: PACKAGE_FREEZE_REOPEN_POLICY_BOUND_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE29_v0: THEOREM_OBJECT_PHASE_EXIT_BINDING_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE29_ARTIFACT_v0: sr_covariance_theorem_object_phase_exit_binding_cycle29_v0",
        "formal/output/sr_covariance_theorem_object_phase_exit_binding_cycle29_v0.json",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_PROGRESSION_v0: CYCLE30_PHASE1_DISCHARGE_PROGRESS_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_02_v0: INTERVAL_INVARIANCE_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_03_v0: VELOCITY_COMPOSITION_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_04_v0: COVARIANCE_CONTRACT_SURFACE_PROGRESS_PINNED",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_PROGRESS_v0: ROWS_01_04_POPULATED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE30_v0: THEOREM_OBJECT_DISCHARGE_PROGRESSION_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE30_ARTIFACT_v0: sr_covariance_theorem_object_discharge_progression_cycle30_v0",
        "formal/output/sr_covariance_theorem_object_discharge_progression_cycle30_v0.json",
        "SR_COVARIANCE_THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_v0: CYCLE31_PHASE1_ROW01_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_01_STATUS_v0: LORENTZ_TRANSFORM_OBJECT_SURFACE_DISCHARGE_PINNED_NONCLAIM",
        "SR_FULL_DERIVATION_PHASE1_DISCHARGE_ROW_LOCK_PROGRESS_v0: ROW01_DISCHARGE_PINNED_NONCLAIM",
        "SR_COVARIANCE_PROGRESS_CYCLE31_v0: THEOREM_OBJECT_DISCHARGE_ROW01_LOCK_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE31_ARTIFACT_v0: sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0",
        "formal/output/sr_covariance_theorem_object_discharge_row01_lock_cycle31_v0.json",
    ]
    for token in required_state_tokens:
        assert token in state_text, f"Missing SR enforcement token in state: {token}"

    required_roadmap_tokens = [
        "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "authoritative no-deviation full-derivation/discharge/inevitability roadmap",
    ]
    for token in required_roadmap_tokens:
        assert token in roadmap_text, f"Missing SR enforcement token in physics roadmap: {token}"
