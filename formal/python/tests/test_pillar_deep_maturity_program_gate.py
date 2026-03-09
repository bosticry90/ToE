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
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_PROGRAM_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"

PROGRAM_REL = "formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md"
REGISTRY_REL = "formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
GATE_REL = "formal/python/tests/test_pillar_deep_maturity_program_gate.py"


VALID_M1 = {"COMPLETE_BOUNDED_v0", "COMPLETE_v0"}
VALID_M2 = {"NOT_STARTED_v0", "IN_PROGRESS_v0", "COMPLETE_v0", "COMPLETE_BOUNDED_v0"}
VALID_M3 = {"NOT_STARTED_v0", "IN_PROGRESS_v0", "COMPLETE_v0", "COMPLETE_BOUNDED_v0"}
VALID_M4 = {"NOT_STARTED_v0", "IN_PROGRESS_v0", "COMPLETE_v0", "COMPLETE_BOUNDED_v0"}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_deep_maturity_program_pointers_and_tokens_are_pinned() -> None:
    program_text = _read(PROGRAM_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for token in (
        "PILLAR_DEEP_MATURITY_PROGRAM_v0",
        "M1_THEOREM_CLOSED",
        "M2_DERIVATION_COMPLETE",
        "M3_EMPIRICALLY_DISCRIMINATIVE",
        "M4_CROSS_PILLAR_INEVITABLE",
        "M5_THEORY_PARITY_LINKED",
        "PILLAR_DEEP_MATURITY_PROGRAM_STATUS_v0: ACTIVE_v0",
        "PILLAR_DEEP_MATURITY_CURRENT_PHASE_v0: PHASE_5_M5_THEORY_PARITY_LINK_EXECUTION_v0",
        "PILLAR_DEEP_MATURITY_ACTIVE_TARGET_v0: TARGET-SR-M5-THEORY-PARITY-LINK-v0",
        "PILLAR_DEEP_MATURITY_NEXT_TARGET_v0: TARGET-SR-M5-THEORY-PARITY-LINK-v0",
        "formal/python/tests/test_pillar_deep_maturity_m2_completion_gate.py",
        "formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py",
        "formal/python/tests/test_gr_empirical_discriminator_emp_gr_01_scaffold_gate.py",
        "formal/python/tests/test_stat_empirical_discriminator_emp_stat_01_scaffold_gate.py",
        "formal/python/tests/test_cosmo_empirical_discriminator_emp_cosmo_01_scaffold_gate.py",
        "formal/python/tests/test_em_empirical_discriminator_emp_em_01_scaffold_gate.py",
        "formal/python/tests/test_qft_empirical_discriminator_emp_qft_01_scaffold_gate.py",
        "formal/python/tests/test_sr_empirical_discriminator_emp_sr_01_scaffold_gate.py",
        "formal/docs/release/PHASE3_M3_CONSOLIDATION_PROMOTION_v0.md",
        "formal/python/tests/test_phase3_m3_consolidation_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_QM_M3_COMPLETION_PROMOTION_v0.md",
        "formal/python/tests/test_qm_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md",
        "formal/python/tests/test_gr_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_STAT_M3_COMPLETION_PROMOTION_v0.md",
        "formal/python/tests/test_stat_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_COSMO_M3_COMPLETION_PROMOTION_v0.md",
        "formal/python/tests/test_cosmo_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_EM_M3_COMPLETION_PROMOTION_v0.md",
        "formal/python/tests/test_em_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_QFT_M3_COMPLETION_PROMOTION_v0.md",
        "formal/python/tests/test_qft_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_SR_M3_COMPLETION_PROMOTION_v0.md",
        "formal/python/tests/test_sr_m3_completion_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_QM_M4_SEAM_CLOSURE_PROMOTION_v0.md",
        "formal/python/tests/test_qm_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_GR_M4_SEAM_CLOSURE_PROMOTION_v0.md",
        "formal/python/tests/test_gr_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_STAT_M4_SEAM_CLOSURE_PROMOTION_v0.md",
        "formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_COSMO_M4_SEAM_CLOSURE_PROMOTION_v0.md",
        "formal/python/tests/test_cosmo_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_EM_M4_SEAM_CLOSURE_PROMOTION_v0.md",
        "formal/python/tests/test_em_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_QFT_M4_SEAM_CLOSURE_PROMOTION_v0.md",
        "formal/python/tests/test_qft_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_SR_M4_SEAM_CLOSURE_PROMOTION_v0.md",
        "formal/python/tests/test_sr_m4_seam_closure_promotion_cycle01_gate.py",
        "formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md",
        "formal/python/tests/test_sr_m5_theory_parity_link_cycle36_gate.py",
        REGISTRY_REL,
        GATE_REL,
    ):
        assert token in program_text, f"Deep maturity program missing token `{token}`."

    for surface_text, label in ((roadmap_text, "roadmap"), (state_text, "state")):
        assert PROGRAM_REL in surface_text, f"{label} must pin deep maturity program pointer."
        assert REGISTRY_REL in surface_text, f"{label} must pin deep maturity registry pointer."
        assert GATE_REL in surface_text, f"{label} must pin deep maturity gate pointer."


def test_deep_maturity_registry_covers_all_matrix_pillars() -> None:
    registry = _read_json(REGISTRY_PATH)
    matrix = _read_json(MATRIX_PATH)

    assert registry.get("registry_id") == "PILLAR_DEEP_MATURITY_REGISTRY_v0"
    assert registry.get("registry_version") == 1
    assert registry.get("program_doc") == PROGRAM_REL
    assert registry.get("gate_path") == GATE_REL
    assert registry.get("m3_consolidation_gate_path") == (
        "formal/python/tests/test_phase3_m3_consolidation_promotion_cycle01_gate.py"
    )
    assert registry.get("qm_m3_completion_gate_path") == "formal/python/tests/test_qm_m3_completion_promotion_cycle01_gate.py"
    assert registry.get("qm_m4_seam_closure_gate_path") == (
        "formal/python/tests/test_qm_m4_seam_closure_promotion_cycle01_gate.py"
    )
    assert registry.get("gr_m4_seam_closure_gate_path") == (
        "formal/python/tests/test_gr_m4_seam_closure_promotion_cycle01_gate.py"
    )
    assert registry.get("stat_m4_seam_closure_gate_path") == (
        "formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py"
    )
    assert registry.get("cosmo_m4_seam_closure_gate_path") == (
        "formal/python/tests/test_cosmo_m4_seam_closure_promotion_cycle01_gate.py"
    )
    assert registry.get("em_m4_seam_closure_gate_path") == (
        "formal/python/tests/test_em_m4_seam_closure_promotion_cycle01_gate.py"
    )
    assert registry.get("qft_m4_seam_closure_gate_path") == (
        "formal/python/tests/test_qft_m4_seam_closure_promotion_cycle01_gate.py"
    )
    assert registry.get("sr_m4_seam_closure_gate_path") == (
        "formal/python/tests/test_sr_m4_seam_closure_promotion_cycle01_gate.py"
    )
    assert registry.get("sr_m5_theory_parity_gate_path") == (
        "formal/python/tests/test_sr_m5_theory_parity_link_cycle36_gate.py"
    )
    assert registry.get("gr_m3_completion_gate_path") == "formal/python/tests/test_gr_m3_completion_promotion_cycle01_gate.py"
    assert registry.get("stat_m3_completion_gate_path") == "formal/python/tests/test_stat_m3_completion_promotion_cycle01_gate.py"
    assert registry.get("cosmo_m3_completion_gate_path") == (
        "formal/python/tests/test_cosmo_m3_completion_promotion_cycle01_gate.py"
    )
    assert registry.get("em_m3_completion_gate_path") == "formal/python/tests/test_em_m3_completion_promotion_cycle01_gate.py"
    assert registry.get("qft_m3_completion_gate_path") == "formal/python/tests/test_qft_m3_completion_promotion_cycle01_gate.py"
    assert registry.get("sr_m3_completion_gate_path") == "formal/python/tests/test_sr_m3_completion_promotion_cycle01_gate.py"

    status = registry.get("program_status", {})
    assert status.get("PILLAR_DEEP_MATURITY_PROGRAM_STATUS_v0") == "ACTIVE_v0"
    assert status.get("PILLAR_DEEP_MATURITY_CURRENT_PHASE_v0") == "PHASE_5_M5_THEORY_PARITY_LINK_EXECUTION_v0"
    assert status.get("PILLAR_DEEP_MATURITY_ACTIVE_TARGET_v0") == "TARGET-SR-M5-THEORY-PARITY-LINK-v0"
    assert status.get("PILLAR_DEEP_MATURITY_NEXT_TARGET_v0") == "TARGET-SR-M5-THEORY-PARITY-LINK-v0"

    consolidation = registry.get("m3_consolidation", {})
    assert consolidation.get("target_id") == "TARGET-PHASE3-M3-CONSOLIDATION-PROMOTION-v0"
    assert consolidation.get("doc_path") == "formal/docs/release/PHASE3_M3_CONSOLIDATION_PROMOTION_v0.md"
    assert consolidation.get("artifact_path") == "formal/output/phase3_m3_consolidation_promotion_cycle01_v0.json"
    assert consolidation.get("gate_path") == "formal/python/tests/test_phase3_m3_consolidation_promotion_cycle01_gate.py"

    assert registry.get("tier_tokens") == {
        "m1": "M1_THEOREM_CLOSED",
        "m2": "M2_DERIVATION_COMPLETE",
        "m3": "M3_EMPIRICALLY_DISCRIMINATIVE",
        "m4": "M4_CROSS_PILLAR_INEVITABLE",
        "m5": "M5_THEORY_PARITY_LINKED",
    }

    matrix_pillars = set(matrix.get("pillars", {}).keys())
    registry_rows = registry.get("pillars", [])
    assert isinstance(registry_rows, list) and registry_rows, "Deep maturity registry must define pillar rows."

    qm_row = next((row for row in registry_rows if row.get("pillar_id") == "PILLAR-QM"), None)
    assert qm_row is not None, "PILLAR-QM row is required."
    assert qm_row.get("m3_status") == "COMPLETE_BOUNDED_v0"
    qm_m3_completion = qm_row.get("m3_completion", {})
    assert qm_m3_completion.get("target_id") == "TARGET-QM-M3-COMPLETION-PROMOTION-v0"
    assert qm_m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_QM_M3_COMPLETION_PROMOTION_v0.md"
    assert qm_m3_completion.get("artifact_path") == "formal/output/qm_m3_completion_promotion_cycle01_v0.json"
    assert qm_m3_completion.get("gate_path") == "formal/python/tests/test_qm_m3_completion_promotion_cycle01_gate.py"
    assert qm_row.get("m4_status") == "COMPLETE_BOUNDED_v0"
    qm_m4_completion = qm_row.get("m4_completion", {})
    assert qm_m4_completion.get("target_id") == "TARGET-QM-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert qm_m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_QM_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert qm_m4_completion.get("artifact_path") == "formal/output/qm_m4_seam_closure_promotion_cycle01_v0.json"
    assert qm_m4_completion.get("gate_path") == "formal/python/tests/test_qm_m4_seam_closure_promotion_cycle01_gate.py"

    gr_row = next((row for row in registry_rows if row.get("pillar_id") == "PILLAR-GR"), None)
    assert gr_row is not None, "PILLAR-GR row is required."
    assert gr_row.get("m3_status") == "COMPLETE_BOUNDED_v0"
    gr_m3_completion = gr_row.get("m3_completion", {})
    assert gr_m3_completion.get("target_id") == "TARGET-GR-M3-COMPLETION-PROMOTION-v0"
    assert gr_m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md"
    assert gr_m3_completion.get("artifact_path") == "formal/output/gr_m3_completion_promotion_cycle01_v0.json"
    assert gr_m3_completion.get("gate_path") == "formal/python/tests/test_gr_m3_completion_promotion_cycle01_gate.py"
    assert gr_row.get("m4_status") == "COMPLETE_BOUNDED_v0"
    gr_m4_completion = gr_row.get("m4_completion", {})
    assert gr_m4_completion.get("target_id") == "TARGET-GR-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert gr_m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_GR_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert gr_m4_completion.get("artifact_path") == "formal/output/gr_m4_seam_closure_promotion_cycle01_v0.json"
    assert gr_m4_completion.get("gate_path") == "formal/python/tests/test_gr_m4_seam_closure_promotion_cycle01_gate.py"

    stat_row = next((row for row in registry_rows if row.get("pillar_id") == "PILLAR-STAT"), None)
    assert stat_row is not None, "PILLAR-STAT row is required."
    assert stat_row.get("m3_status") == "COMPLETE_BOUNDED_v0"
    stat_m3_completion = stat_row.get("m3_completion", {})
    assert stat_m3_completion.get("target_id") == "TARGET-STAT-M3-COMPLETION-PROMOTION-v0"
    assert stat_m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_STAT_M3_COMPLETION_PROMOTION_v0.md"
    assert stat_m3_completion.get("artifact_path") == "formal/output/stat_m3_completion_promotion_cycle01_v0.json"
    assert stat_m3_completion.get("gate_path") == "formal/python/tests/test_stat_m3_completion_promotion_cycle01_gate.py"
    assert stat_row.get("m4_status") == "COMPLETE_BOUNDED_v0"
    stat_m4_completion = stat_row.get("m4_completion", {})
    assert stat_m4_completion.get("target_id") == "TARGET-STAT-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert stat_m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_STAT_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert stat_m4_completion.get("artifact_path") == "formal/output/stat_m4_seam_closure_promotion_cycle01_v0.json"
    assert stat_m4_completion.get("gate_path") == "formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py"

    cosmo_row = next((row for row in registry_rows if row.get("pillar_id") == "PILLAR-COSMO"), None)
    assert cosmo_row is not None, "PILLAR-COSMO row is required."
    assert cosmo_row.get("m3_status") == "COMPLETE_BOUNDED_v0"
    cosmo_m3_completion = cosmo_row.get("m3_completion", {})
    assert cosmo_m3_completion.get("target_id") == "TARGET-COSMO-M3-COMPLETION-PROMOTION-v0"
    assert cosmo_m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_COSMO_M3_COMPLETION_PROMOTION_v0.md"
    assert cosmo_m3_completion.get("artifact_path") == "formal/output/cosmo_m3_completion_promotion_cycle01_v0.json"
    assert cosmo_m3_completion.get("gate_path") == "formal/python/tests/test_cosmo_m3_completion_promotion_cycle01_gate.py"
    assert cosmo_row.get("m4_status") == "COMPLETE_BOUNDED_v0"
    cosmo_m4_completion = cosmo_row.get("m4_completion", {})
    assert cosmo_m4_completion.get("target_id") == "TARGET-COSMO-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert cosmo_m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_COSMO_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert cosmo_m4_completion.get("artifact_path") == "formal/output/cosmo_m4_seam_closure_promotion_cycle01_v0.json"
    assert cosmo_m4_completion.get("gate_path") == "formal/python/tests/test_cosmo_m4_seam_closure_promotion_cycle01_gate.py"

    em_row = next((row for row in registry_rows if row.get("pillar_id") == "PILLAR-EM"), None)
    assert em_row is not None, "PILLAR-EM row is required."
    assert em_row.get("m3_status") == "COMPLETE_BOUNDED_v0"
    em_m3_completion = em_row.get("m3_completion", {})
    assert em_m3_completion.get("target_id") == "TARGET-EM-M3-COMPLETION-PROMOTION-v0"
    assert em_m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_EM_M3_COMPLETION_PROMOTION_v0.md"
    assert em_m3_completion.get("artifact_path") == "formal/output/em_m3_completion_promotion_cycle01_v0.json"
    assert em_m3_completion.get("gate_path") == "formal/python/tests/test_em_m3_completion_promotion_cycle01_gate.py"
    assert em_row.get("m4_status") == "COMPLETE_BOUNDED_v0"
    em_m4_completion = em_row.get("m4_completion", {})
    assert em_m4_completion.get("target_id") == "TARGET-EM-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert em_m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_EM_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert em_m4_completion.get("artifact_path") == "formal/output/em_m4_seam_closure_promotion_cycle01_v0.json"
    assert em_m4_completion.get("gate_path") == "formal/python/tests/test_em_m4_seam_closure_promotion_cycle01_gate.py"

    qft_row = next((row for row in registry_rows if row.get("pillar_id") == "PILLAR-QFT"), None)
    assert qft_row is not None, "PILLAR-QFT row is required."
    assert qft_row.get("next_target") == "TARGET-SR-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert qft_row.get("m3_status") == "COMPLETE_BOUNDED_v0"
    qft_m3_completion = qft_row.get("m3_completion", {})
    assert qft_m3_completion.get("target_id") == "TARGET-QFT-M3-COMPLETION-PROMOTION-v0"
    assert qft_m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_QFT_M3_COMPLETION_PROMOTION_v0.md"
    assert qft_m3_completion.get("artifact_path") == "formal/output/qft_m3_completion_promotion_cycle01_v0.json"
    assert qft_m3_completion.get("gate_path") == "formal/python/tests/test_qft_m3_completion_promotion_cycle01_gate.py"
    assert qft_row.get("m4_status") == "COMPLETE_BOUNDED_v0"
    qft_m4_completion = qft_row.get("m4_completion", {})
    assert qft_m4_completion.get("target_id") == "TARGET-QFT-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert qft_m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_QFT_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert qft_m4_completion.get("artifact_path") == "formal/output/qft_m4_seam_closure_promotion_cycle01_v0.json"
    assert qft_m4_completion.get("gate_path") == "formal/python/tests/test_qft_m4_seam_closure_promotion_cycle01_gate.py"

    sr_row = next((row for row in registry_rows if row.get("pillar_id") == "PILLAR-SR"), None)
    assert sr_row is not None, "PILLAR-SR row is required."
    assert sr_row.get("next_target") == "TARGET-SR-M5-THEORY-PARITY-LINK-v0"
    assert sr_row.get("m3_status") == "COMPLETE_BOUNDED_v0"
    sr_m3_completion = sr_row.get("m3_completion", {})
    assert sr_m3_completion.get("target_id") == "TARGET-SR-M3-COMPLETION-PROMOTION-v0"
    assert sr_m3_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_SR_M3_COMPLETION_PROMOTION_v0.md"
    assert sr_m3_completion.get("artifact_path") == "formal/output/sr_m3_completion_promotion_cycle01_v0.json"
    assert sr_m3_completion.get("gate_path") == "formal/python/tests/test_sr_m3_completion_promotion_cycle01_gate.py"
    assert sr_row.get("m4_status") == "COMPLETE_BOUNDED_v0"
    sr_m4_completion = sr_row.get("m4_completion", {})
    assert sr_m4_completion.get("target_id") == "TARGET-SR-M4-SEAM-CLOSURE-PROMOTION-v0"
    assert sr_m4_completion.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_SR_M4_SEAM_CLOSURE_PROMOTION_v0.md"
    assert sr_m4_completion.get("artifact_path") == "formal/output/sr_m4_seam_closure_promotion_cycle01_v0.json"
    assert sr_m4_completion.get("gate_path") == "formal/python/tests/test_sr_m4_seam_closure_promotion_cycle01_gate.py"
    sr_m5_theory_parity = sr_row.get("m5_theory_parity", {})
    assert sr_m5_theory_parity.get("target_id") == "TARGET-SR-M5-THEORY-PARITY-LINK-v0"
    assert sr_m5_theory_parity.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md"
    assert sr_m5_theory_parity.get("artifact_path") == "formal/output/sr_m5_theory_parity_link_cycle36_v0.json"
    assert sr_m5_theory_parity.get("gate_path") == "formal/python/tests/test_sr_m5_theory_parity_link_cycle36_gate.py"

    registry_pillars = {row.get("pillar_id") for row in registry_rows}
    assert registry_pillars == matrix_pillars, "Deep maturity registry must cover all matrix pillars exactly."

    priorities = [row.get("priority") for row in registry_rows]
    assert sorted(priorities) == list(range(1, len(registry_rows) + 1)), "Priorities must be unique and contiguous."

    for row in registry_rows:
        assert row.get("m1_status") in VALID_M1, f"Invalid m1_status for {row.get('pillar_id')}"
        assert row.get("m2_status") in VALID_M2, f"Invalid m2_status for {row.get('pillar_id')}"
        assert row.get("m3_status") in VALID_M3, f"Invalid m3_status for {row.get('pillar_id')}"
        assert row.get("m4_status") in VALID_M4, f"Invalid m4_status for {row.get('pillar_id')}"
        assert isinstance(row.get("next_target"), str) and row.get("next_target"), (
            f"next_target must be non-empty for {row.get('pillar_id')}"
        )

        if str(row.get("m4_status", "")).startswith("COMPLETE"):
            assert str(row.get("m3_status", "")).startswith("COMPLETE"), (
                f"{row.get('pillar_id')}: M4 completion requires M3 completion."
            )
        if str(row.get("m3_status", "")).startswith("COMPLETE"):
            assert str(row.get("m2_status", "")).startswith("COMPLETE"), (
                f"{row.get('pillar_id')}: M3 completion requires M2 completion."
            )



