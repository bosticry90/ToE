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
DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle07_v0.json"
PREV_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle06_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _frac_list(values: list[str]) -> list[Fraction]:
    return [Fraction(v) for v in values]


def _moments10(
    support: list[Fraction], probs: list[Fraction]
) -> tuple[Fraction, Fraction, Fraction, Fraction, Fraction, Fraction, Fraction]:
    mu = sum(p * x for p, x in zip(probs, support))
    var = sum(p * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m3 = sum(p * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m4 = sum(p * (x - mu) * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m6 = sum(p * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m8 = sum(
        p * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu) * (x - mu)
        for p, x in zip(probs, support)
    )
    m10 = sum(
        p
        * (x - mu)
        * (x - mu)
        * (x - mu)
        * (x - mu)
        * (x - mu)
        * (x - mu)
        * (x - mu)
        * (x - mu)
        * (x - mu)
        * (x - mu)
        for p, x in zip(probs, support)
    )
    return mu, var, m3, m4, m6, m8, m10


def test_qm_stat_cycle07_artifacts_exist() -> None:
    assert DOC_PATH.exists(), "Missing QM-STAT Cycle07 target doc."
    assert ARTIFACT_PATH.exists(), "Missing QM-STAT Cycle07 artifact."
    assert PREV_ARTIFACT_PATH.exists(), "Missing QM-STAT Cycle06 predecessor artifact."


def test_qm_stat_cycle07_doc_contains_required_tokens() -> None:
    text = _read(DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0",
        "TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE07-v0",
        "QM_STAT_CYCLE07_STATUS_v0: TENTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
        "QM_STAT_CYCLE07_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_AND_TENTH_MOMENT_PARITY_REQUIRED",
        "QM_STAT_CYCLE07_INCOMPATIBILITY_EXCLUSION_v0: TENTH_MOMENT_MISMATCH_FLAGGED_AS_NONCOMPATIBLE",
        "QM_STAT_CYCLE07_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_STATUS_v0: CRITERIA_AND_TENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
        "formal/output/qm_stat_class_b_seam_physics_pilot_cycle07_v0.json",
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle07_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "QM-STAT Cycle07 doc missing required token(s): " + ", ".join(missing)


def test_qm_stat_cycle07_artifact_schema_and_predecessor_tieback() -> None:
    artifact = _json(ARTIFACT_PATH)
    assert artifact["artifact_id"] == "qm_stat_class_b_seam_physics_pilot_cycle07_v0"
    assert artifact["seam_id"] == "SEAM-QM-STAT"
    assert artifact["class_token"] == "TOE_CK_CLASS_COMPATIBILITY_v0"
    assert artifact["status"] == "CRITERIA_AND_TENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM"

    derived = artifact["derived_from"]
    assert derived["artifact_id"] == "qm_stat_class_b_seam_physics_pilot_cycle06_v0"
    assert derived["artifact_path"] == "formal/output/qm_stat_class_b_seam_physics_pilot_cycle06_v0.json"


def test_qm_stat_cycle07_blocker_criteria_include_tenth_moment_parity() -> None:
    artifact = _json(ARTIFACT_PATH)
    criteria = artifact["blocker_discharge_criteria"]

    assert criteria["token"] == "MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_AND_TENTH_MOMENT_PARITY_REQUIRED"

    xs = [Fraction(x) for x in criteria["shared_support"]]
    qm_p = _frac_list(criteria["qm_probability_mass"])
    stat_p = _frac_list(criteria["stat_probability_mass"])

    assert sum(qm_p) == Fraction(criteria["normalization"]["qm_sum"])
    assert sum(stat_p) == Fraction(criteria["normalization"]["stat_sum"])

    qm_mu, qm_var, qm_m3, qm_m4, qm_m6, qm_m8, qm_m10 = _moments10(xs, qm_p)
    st_mu, st_var, st_m3, st_m4, st_m6, st_m8, st_m10 = _moments10(xs, stat_p)

    assert qm_mu == Fraction(criteria["first_moment"]["qm_mu"])
    assert st_mu == Fraction(criteria["first_moment"]["stat_mu"])
    assert qm_mu == st_mu

    assert qm_var == Fraction(criteria["second_central_moment"]["qm_var"])
    assert st_var == Fraction(criteria["second_central_moment"]["stat_var"])
    assert qm_var == st_var

    assert qm_m3 == Fraction(criteria["third_central_moment"]["qm_m3"])
    assert st_m3 == Fraction(criteria["third_central_moment"]["stat_m3"])
    assert qm_m3 == st_m3

    assert qm_m4 == Fraction(criteria["fourth_central_moment"]["qm_m4"])
    assert st_m4 == Fraction(criteria["fourth_central_moment"]["stat_m4"])
    assert qm_m4 == st_m4

    assert qm_m6 == Fraction(criteria["sixth_central_moment"]["qm_m6"])
    assert st_m6 == Fraction(criteria["sixth_central_moment"]["stat_m6"])
    assert qm_m6 == st_m6

    assert qm_m8 == Fraction(criteria["eighth_central_moment"]["qm_m8"])
    assert st_m8 == Fraction(criteria["eighth_central_moment"]["stat_m8"])
    assert qm_m8 == st_m8

    assert qm_m10 == Fraction(criteria["tenth_central_moment"]["qm_m10"])
    assert st_m10 == Fraction(criteria["tenth_central_moment"]["stat_m10"])
    assert qm_m10 == st_m10


def test_qm_stat_cycle07_tenth_moment_exclusion_is_explicit() -> None:
    artifact = _json(ARTIFACT_PATH)
    exclusion = artifact["bounded_incompatibility_exclusion"]

    xs = [Fraction(x) for x in exclusion["shared_support"]]
    qm_p = _frac_list(exclusion["qm_probability_mass"])
    st_p = _frac_list(exclusion["stat_probability_mass"])

    qm_mu, qm_var, qm_m3, qm_m4, qm_m6, qm_m8, qm_m10 = _moments10(xs, qm_p)
    st_mu, st_var, st_m3, st_m4, st_m6, st_m8, st_m10 = _moments10(xs, st_p)

    assert qm_mu == Fraction(exclusion["first_moment"]["qm_mu"])
    assert st_mu == Fraction(exclusion["first_moment"]["stat_mu"])
    assert qm_mu == st_mu

    assert qm_var == Fraction(exclusion["second_central_moment"]["qm_var"])
    assert st_var == Fraction(exclusion["second_central_moment"]["stat_var"])
    assert qm_var == st_var

    assert qm_m3 == Fraction(exclusion["third_central_moment"]["qm_m3"])
    assert st_m3 == Fraction(exclusion["third_central_moment"]["stat_m3"])
    assert qm_m3 == st_m3

    assert qm_m4 == Fraction(exclusion["fourth_central_moment"]["qm_m4"])
    assert st_m4 == Fraction(exclusion["fourth_central_moment"]["stat_m4"])
    assert qm_m4 == st_m4

    assert qm_m6 == Fraction(exclusion["sixth_central_moment"]["qm_m6"])
    assert st_m6 == Fraction(exclusion["sixth_central_moment"]["stat_m6"])
    assert qm_m6 == st_m6

    assert qm_m8 == Fraction(exclusion["eighth_central_moment"]["qm_m8"])
    assert st_m8 == Fraction(exclusion["eighth_central_moment"]["stat_m8"])
    assert qm_m8 != st_m8

    assert qm_m10 == Fraction(exclusion["tenth_central_moment"]["qm_m10"])
    assert st_m10 == Fraction(exclusion["tenth_central_moment"]["stat_m10"])
    assert qm_m10 != st_m10

    assert exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"


def test_qm_stat_cycle07_nonclaim_boundary_and_adjudication() -> None:
    artifact = _json(ARTIFACT_PATH)
    bounded = artifact["bounded_scope"]

    assert bounded["class_flip_claimed"] is False
    assert bounded["full_theorem_discharge_claimed"] is False
    assert bounded["continuum_statistical_closure_claimed"] is False
    assert bounded["external_truth_claimed"] is False

    adjudication = artifact["adjudication"]
    assert adjudication["token"] == "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"
