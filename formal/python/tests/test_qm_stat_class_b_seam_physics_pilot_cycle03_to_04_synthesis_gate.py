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
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_v0.md"
)
CYCLE03_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_v0.md"
)
CYCLE04_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_v0.md"
)
CYCLE03_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle03_v0.json"
CYCLE04_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle04_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _moments3(support: list[Fraction], probs: list[Fraction]) -> tuple[Fraction, Fraction, Fraction]:
    mu = sum(p * x for p, x in zip(probs, support))
    var = sum(p * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m3 = sum(p * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    return mu, var, m3


def _moments4(support: list[Fraction], probs: list[Fraction]) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    mu = sum(p * x for p, x in zip(probs, support))
    var = sum(p * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m3 = sum(p * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m4 = sum(p * (x - mu) * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    return mu, var, m3, m4


def test_qm_stat_cycle03_to_04_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE03_DOC_PATH, CYCLE04_DOC_PATH, CYCLE03_ARTIFACT_PATH, CYCLE04_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_qm_stat_cycle03_to_04_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_v0",
        "TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE03-TO-04-SYNTHESIS-v0",
        "QM_STAT_CYCLE03_BASELINE_v0: THIRD_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
        "QM_STAT_CYCLE04_ADDITIVE_DELTA_v0: FOURTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
        "QM_STAT_BLOCKER_DISCHARGE_IMPACT_v0: CRITERIA_STRENGTHENED_BUT_ADJUDICATION_STILL_OPEN",
        "QM_STAT_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "QM_STAT_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "QM_STAT_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_QM_STAT_PAYLOAD_IS_READY_THEN_CYCLE05_ELSE_OPEN_COSMO_SR_CYCLE03",
        "QM_STAT_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle03_to_04_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "QM-STAT Cycle03-to-04 synthesis doc missing required token(s): " + ", ".join(missing)


def test_qm_stat_cycle03_to_04_additive_delta_is_material() -> None:
    cycle03 = _json(CYCLE03_ARTIFACT_PATH)
    cycle04 = _json(CYCLE04_ARTIFACT_PATH)

    c3 = cycle03["blocker_discharge_criteria"]
    c4 = cycle04["blocker_discharge_criteria"]

    assert c3["token"] == "MASS_MEAN_VARIANCE_THIRD_MOMENT_PARITY_REQUIRED"
    assert c4["token"] == "MASS_MEAN_VARIANCE_THIRD_AND_FOURTH_MOMENT_PARITY_REQUIRED"

    assert "fourth_central_moment" not in c3
    assert "fourth_central_moment" in c4

    xs3 = [Fraction(x) for x in c3["shared_support"]]
    qm3 = [Fraction(x) for x in c3["qm_probability_mass"]]
    st3 = [Fraction(x) for x in c3["stat_probability_mass"]]
    _, _, qm_m3 = _moments3(xs3, qm3)
    _, _, st_m3 = _moments3(xs3, st3)
    assert qm_m3 == st_m3

    xs4 = [Fraction(x) for x in c4["shared_support"]]
    qm4 = [Fraction(x) for x in c4["qm_probability_mass"]]
    st4 = [Fraction(x) for x in c4["stat_probability_mass"]]
    _, _, qm_m3_4, qm_m4 = _moments4(xs4, qm4)
    _, _, st_m3_4, st_m4 = _moments4(xs4, st4)
    assert qm_m3_4 == st_m3_4
    assert qm_m4 == st_m4


def test_qm_stat_cycle03_to_04_exclusion_strengthening_present() -> None:
    cycle03_ex = _json(CYCLE03_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]
    cycle04_ex = _json(CYCLE04_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]

    assert cycle03_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert cycle04_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    assert "fourth_central_moment" not in cycle03_ex
    assert "fourth_central_moment" in cycle04_ex

    xs = [Fraction(x) for x in cycle04_ex["shared_support"]]
    qm = [Fraction(x) for x in cycle04_ex["qm_probability_mass"]]
    st = [Fraction(x) for x in cycle04_ex["stat_probability_mass"]]
    qm_mu, qm_var, qm_m3, qm_m4 = _moments4(xs, qm)
    st_mu, st_var, st_m3, st_m4 = _moments4(xs, st)

    assert qm_mu == st_mu
    assert qm_var == st_var
    assert qm_m3 == st_m3
    assert qm_m4 != st_m4


def test_qm_stat_cycle03_to_04_promotion_still_blocked() -> None:
    cycle03 = _json(CYCLE03_ARTIFACT_PATH)
    cycle04 = _json(CYCLE04_ARTIFACT_PATH)

    assert cycle03["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle04["adjudication"]["value"] == "NOT_YET_DISCHARGED"

    for artifact in (cycle03, cycle04):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["continuum_statistical_closure_claimed"] is False
        assert bounded["external_truth_claimed"] is False
