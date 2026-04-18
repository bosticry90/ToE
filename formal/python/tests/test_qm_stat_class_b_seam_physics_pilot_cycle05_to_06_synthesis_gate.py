from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
SYNTH_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_TO_06_SYNTHESIS_v0.md"
)
CYCLE05_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_v0.md"
)
CYCLE06_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_v0.md"
)
CYCLE05_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle05_v0.json"
CYCLE06_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle06_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _moments6(
    support: list[Fraction], probs: list[Fraction]
) -> tuple[Fraction, Fraction, Fraction, Fraction, Fraction]:
    mu = sum(p * x for p, x in zip(probs, support))
    var = sum(p * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m3 = sum(p * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m4 = sum(p * (x - mu) * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m6 = sum(p * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    return mu, var, m3, m4, m6


def _moments8(
    support: list[Fraction], probs: list[Fraction]
) -> tuple[Fraction, Fraction, Fraction, Fraction, Fraction, Fraction]:
    mu = sum(p * x for p, x in zip(probs, support))
    var = sum(p * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m3 = sum(p * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m4 = sum(p * (x - mu) * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m6 = sum(p * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m8 = sum(
        p * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu)
        for p, x in zip(probs, support)
    )
    return mu, var, m3, m4, m6, m8


def test_qm_stat_cycle05_to_06_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE05_DOC_PATH, CYCLE06_DOC_PATH, CYCLE05_ARTIFACT_PATH, CYCLE06_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_qm_stat_cycle05_to_06_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_TO_06_SYNTHESIS_v0",
        "TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE05-TO-06-SYNTHESIS-v0",
        "QM_STAT_CYCLE05_BASELINE_v0: SIXTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
        "QM_STAT_CYCLE06_ADDITIVE_DELTA_v0: EIGHTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
        "QM_STAT_BLOCKER_DISCHARGE_IMPACT_v0: CRITERIA_STRENGTHENED_BUT_ADJUDICATION_STILL_OPEN",
        "QM_STAT_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "QM_STAT_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "QM_STAT_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_QM_STAT_PAYLOAD_IS_READY_THEN_CYCLE07_ELSE_OPEN_COSMO_SR_CYCLE06",
        "QM_STAT_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_TO_06_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_TO_06_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle05_to_06_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "QM-STAT Cycle05-to-06 synthesis doc missing required token(s): " + ", ".join(missing)


def test_qm_stat_cycle05_to_06_additive_delta_is_material() -> None:
    cycle05 = _json(CYCLE05_ARTIFACT_PATH)
    cycle06 = _json(CYCLE06_ARTIFACT_PATH)

    c5 = cycle05["blocker_discharge_criteria"]
    c6 = cycle06["blocker_discharge_criteria"]

    assert c5["token"] == "MASS_MEAN_VARIANCE_THIRD_FOURTH_AND_SIXTH_MOMENT_PARITY_REQUIRED"
    assert c6["token"] == "MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_AND_EIGHTH_MOMENT_PARITY_REQUIRED"

    assert "eighth_central_moment" not in c5
    assert "eighth_central_moment" in c6

    xs5 = [Fraction(x) for x in c5["shared_support"]]
    qm5 = [Fraction(x) for x in c5["qm_probability_mass"]]
    st5 = [Fraction(x) for x in c5["stat_probability_mass"]]
    _, _, qm_m3_5, qm_m4_5, qm_m6_5 = _moments6(xs5, qm5)
    _, _, st_m3_5, st_m4_5, st_m6_5 = _moments6(xs5, st5)
    assert qm_m3_5 == st_m3_5
    assert qm_m4_5 == st_m4_5
    assert qm_m6_5 == st_m6_5

    xs6 = [Fraction(x) for x in c6["shared_support"]]
    qm6 = [Fraction(x) for x in c6["qm_probability_mass"]]
    st6 = [Fraction(x) for x in c6["stat_probability_mass"]]
    _, _, qm_m3_6, qm_m4_6, qm_m6_6, qm_m8 = _moments8(xs6, qm6)
    _, _, st_m3_6, st_m4_6, st_m6_6, st_m8 = _moments8(xs6, st6)
    assert qm_m3_6 == st_m3_6
    assert qm_m4_6 == st_m4_6
    assert qm_m6_6 == st_m6_6
    assert qm_m8 == st_m8


def test_qm_stat_cycle05_to_06_exclusion_strengthening_present() -> None:
    cycle05_ex = _json(CYCLE05_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]
    cycle06_ex = _json(CYCLE06_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]

    assert cycle05_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert cycle06_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    assert "eighth_central_moment" not in cycle05_ex
    assert "eighth_central_moment" in cycle06_ex

    xs = [Fraction(x) for x in cycle06_ex["shared_support"]]
    qm = [Fraction(x) for x in cycle06_ex["qm_probability_mass"]]
    st = [Fraction(x) for x in cycle06_ex["stat_probability_mass"]]
    qm_mu, qm_var, qm_m3, qm_m4, qm_m6, qm_m8 = _moments8(xs, qm)
    st_mu, st_var, st_m3, st_m4, st_m6, st_m8 = _moments8(xs, st)

    assert qm_mu == st_mu
    assert qm_var == st_var
    assert qm_m3 == st_m3
    assert qm_m4 == st_m4
    assert qm_m6 == st_m6
    assert qm_m8 != st_m8


def test_qm_stat_cycle05_to_06_promotion_still_blocked() -> None:
    cycle05 = _json(CYCLE05_ARTIFACT_PATH)
    cycle06 = _json(CYCLE06_ARTIFACT_PATH)

    assert cycle05["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle06["adjudication"]["value"] == "NOT_YET_DISCHARGED"

    for artifact in (cycle05, cycle06):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["continuum_statistical_closure_claimed"] is False
        assert bounded["external_truth_claimed"] is False
