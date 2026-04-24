from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REQUIRED_DELTA = (
    "PREFIX_TRANSITION_CURVATURE_LAPLACIAN_GRADIENT_MAGNITUDE_STABILITY_"
    "GRADIENT_SIGN_MAGNITUDE_DRIFT_BOUND_GRADIENT_SIGN_MAGNITUDE_STABILITY_"
    "GRADIENT_SIGN_MAGNITUDE_STABILITY_GRADIENT_SIGN_MAGNITUDE_STABILITY_"
    "STABILITY_COHERENCE_DEPENDENCY"
)


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT66_v0.md"
)


def _read() -> str:
    assert DOC_PATH.exists(), f"Missing Increment66 doc: {DOC_PATH}"
    return DOC_PATH.read_text(encoding="utf-8")


def test_increment66_doc_exists_and_anchors() -> None:
    text = _read()

    assert "stress_energy_to_weak_curvature_handoff_strengthening" in text
    assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in text
    assert "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json" in text
    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT65_EXECUTION_PACKET_v0.md" in text


def test_increment66_status_and_nonclaim_tokens_present() -> None:
    text = _read()

    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT66_STATUS_v0: T-CONDITIONAL_BOUNDED_NONCLAIM" in text
    assert f"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT66_DELTA_v0: {REQUIRED_DELTA}" in text
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT66_ADJUDICATION: DISCHARGED_v0_BOUNDED" in text
    assert "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0" in text
    assert "SCALAR_FREEZE_INVARIANCE_v0: ENFORCED" in text
    assert "WORKFLOW_CLOSURE_INVARIANCE_v0: ENFORCED" in text
    assert "GR_QM_COMPLETION_LANE_REOPEN_v0: NO" in text
    assert "does not claim seam closure" in text
    assert "does not claim QFT-GR unification completeness" in text
    assert "does not authorize packet42 hold release" in text


def test_increment66_template_and_governance_pointers_present() -> None:
    text = _read()

    assert "## Architecture phase coverage (v1)" in text
    assert "claim_traceability" in text
    assert "formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py" in text
    assert "formal/python/tests/test_pillar_status_matrix_consistency_gate.py" in text
    assert "formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py" in text
