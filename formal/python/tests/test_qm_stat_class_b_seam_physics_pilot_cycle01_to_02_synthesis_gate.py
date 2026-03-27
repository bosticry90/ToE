from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
SYNTH_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_v0.md"
)
CYCLE01_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0.md"
)
CYCLE02_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_v0.md"
)
CYCLE01_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle01_v0.json"
CYCLE02_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle02_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qm_stat_cycle01_to_02_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE01_DOC_PATH, CYCLE02_DOC_PATH, CYCLE01_ARTIFACT_PATH, CYCLE02_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_qm_stat_cycle01_to_02_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_v0",
        "TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-TO-02-SYNTHESIS-v0",
        "QM_STAT_CYCLE01_CONTRIBUTION_v0: BOUNDED_COMPATIBILITY_WITNESS_PINNED",
        "QM_STAT_CYCLE02_CONTRIBUTION_v0: BLOCKER_CRITERIA_AND_INCOMPATIBILITY_EXCLUSION_PINNED",
        "QM_STAT_BLOCKER_DISCHARGE_STATE_v0: MASS_NORMALIZATION_AND_MOMENT_PARITY_CRITERIA_PINNED_NONCLAIM",
        "QM_STAT_INCOMPATIBILITY_EXCLUSION_STATE_v0: NONCOMPATIBLE_EXCLUDED_VIA_MASS_DRIFT_COUNTEREXAMPLE",
        "QM_STAT_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "QM_STAT_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_PAYLOAD_IS_READY_THEN_CYCLE03_ELSE_OPEN_COSMO_SR_CYCLE01",
        "QM_STAT_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle01_to_02_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "QM-STAT synthesis doc missing required token(s): " + ", ".join(missing)


def test_qm_stat_cycle01_to_02_contributions_match_artifacts() -> None:
    cycle01 = _json(CYCLE01_ARTIFACT_PATH)
    cycle02 = _json(CYCLE02_ARTIFACT_PATH)

    assert cycle01["status"] == "WITNESS_AND_BOUNDED_PAYLOAD_PINNED_NONCLAIM"
    assert cycle02["status"] == "CRITERIA_AND_EXCLUSION_PAYLOAD_PINNED_NONCLAIM"

    criteria = cycle02["blocker_discharge_criteria"]
    assert criteria["token"] == "MASS_NORMALIZATION_AND_MOMENT_PARITY_REQUIRED"

    xs = [Fraction(x) for x in criteria["shared_support"]]
    qm_p = [Fraction(x) for x in criteria["qm_probability_mass"]]
    stat_p = [Fraction(x) for x in criteria["stat_probability_mass"]]

    assert sum(qm_p) == Fraction(criteria["normalization"]["qm_sum"])
    assert sum(stat_p) == Fraction(criteria["normalization"]["stat_sum"])

    qm_mu = sum(p * x for p, x in zip(qm_p, xs))
    stat_mu = sum(p * x for p, x in zip(stat_p, xs))
    assert qm_mu == Fraction(criteria["first_moment"]["qm_mu"])
    assert stat_mu == Fraction(criteria["first_moment"]["stat_mu"])
    assert qm_mu == stat_mu

    exclusion = cycle02["bounded_incompatibility_exclusion"]
    xs_ex = [Fraction(x) for x in exclusion["shared_support"]]
    qm_ex = [Fraction(x) for x in exclusion["qm_probability_mass"]]
    stat_ex = [Fraction(x) for x in exclusion["stat_probability_mass"]]
    qm_mu_ex = sum(p * x for p, x in zip(qm_ex, xs_ex))
    stat_mu_ex = sum(p * x for p, x in zip(stat_ex, xs_ex))
    assert qm_mu_ex == Fraction(exclusion["first_moment"]["qm_mu"])
    assert stat_mu_ex == Fraction(exclusion["first_moment"]["stat_mu"])
    assert qm_mu_ex != stat_mu_ex
    assert exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"


def test_qm_stat_cycle01_to_02_nonclaim_boundary_preserved() -> None:
    for artifact in (_json(CYCLE01_ARTIFACT_PATH), _json(CYCLE02_ARTIFACT_PATH)):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["continuum_statistical_closure_claimed"] is False
        assert bounded["external_truth_claimed"] is False
