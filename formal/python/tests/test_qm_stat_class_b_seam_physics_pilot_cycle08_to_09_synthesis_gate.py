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
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_TO_09_SYNTHESIS_v0.md"
)
CYCLE08_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0.md"
)
CYCLE09_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE09_v0.md"
)
CYCLE08_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle08_v0.json"
CYCLE09_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle09_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _moments14(
    support: list[Fraction], probs: list[Fraction]
) -> tuple[Fraction, Fraction, Fraction, Fraction, Fraction, Fraction, Fraction, Fraction, Fraction]:
    mu = sum(p * x for p, x in zip(probs, support))
    var = sum(p * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m3 = sum(p * (x - mu) ** 3 for p, x in zip(probs, support))
    m4 = sum(p * (x - mu) ** 4 for p, x in zip(probs, support))
    m6 = sum(p * (x - mu) ** 6 for p, x in zip(probs, support))
    m8 = sum(p * (x - mu) ** 8 for p, x in zip(probs, support))
    m10 = sum(p * (x - mu) ** 10 for p, x in zip(probs, support))
    m12 = sum(p * (x - mu) ** 12 for p, x in zip(probs, support))
    m14 = sum(p * (x - mu) ** 14 for p, x in zip(probs, support))
    return mu, var, m3, m4, m6, m8, m10, m12, m14


def test_qm_stat_cycle08_to_09_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE08_DOC_PATH, CYCLE09_DOC_PATH, CYCLE08_ARTIFACT_PATH, CYCLE09_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_qm_stat_cycle08_to_09_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_TO_09_SYNTHESIS_v0",
        "TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE08-TO-09-SYNTHESIS-v0",
        "QM_STAT_CYCLE08_BASELINE_v0: TWELFTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
        "QM_STAT_CYCLE09_ADDITIVE_DELTA_v0: FOURTEENTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED",
        "QM_STAT_BLOCKER_DISCHARGE_IMPACT_v0: CRITERIA_STRENGTHENED_BUT_ADJUDICATION_STILL_OPEN",
        "QM_STAT_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "QM_STAT_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "QM_STAT_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_QM_STAT_PAYLOAD_IS_READY_THEN_CONTINUE_CYCLE09_ELSE_STOP_AT_CYCLE08_TO_09_SYNTHESIS_BOUNDARY",
        "QM_STAT_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "QM_STAT_NON_ACTIVE_LANE_ASSERTION_v0: COSMO_SR_REMAINS_PAUSED_UNLESS_EXPLICIT_ADDITIVE_PAYLOAD_DECLARATION",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_TO_09_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_TO_09_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle08_to_09_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "QM-STAT Cycle08-to-09 synthesis doc missing required token(s): " + ", ".join(missing)


def test_qm_stat_cycle08_to_09_additive_delta_is_material() -> None:
    cycle08 = _json(CYCLE08_ARTIFACT_PATH)
    cycle09 = _json(CYCLE09_ARTIFACT_PATH)

    c8 = cycle08["blocker_discharge_criteria"]
    c9 = cycle09["blocker_discharge_criteria"]

    assert c8["token"] == "MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_AND_TWELFTH_MOMENT_PARITY_REQUIRED"
    assert c9["token"] == "MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_TWELFTH_AND_FOURTEENTH_MOMENT_PARITY_REQUIRED"

    assert "fourteenth_central_moment" not in c8
    assert "fourteenth_central_moment" in c9

    xs9 = [Fraction(x) for x in c9["shared_support"]]
    qm9 = [Fraction(x) for x in c9["qm_probability_mass"]]
    st9 = [Fraction(x) for x in c9["stat_probability_mass"]]
    _, _, qm_m3_9, qm_m4_9, qm_m6_9, qm_m8_9, qm_m10_9, qm_m12_9, qm_m14_9 = _moments14(xs9, qm9)
    _, _, st_m3_9, st_m4_9, st_m6_9, st_m8_9, st_m10_9, st_m12_9, st_m14_9 = _moments14(xs9, st9)
    assert qm_m3_9 == st_m3_9
    assert qm_m4_9 == st_m4_9
    assert qm_m6_9 == st_m6_9
    assert qm_m8_9 == st_m8_9
    assert qm_m10_9 == st_m10_9
    assert qm_m12_9 == st_m12_9
    assert qm_m14_9 == st_m14_9


def test_qm_stat_cycle08_to_09_exclusion_strengthening_present() -> None:
    cycle08_ex = _json(CYCLE08_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]
    cycle09_ex = _json(CYCLE09_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]

    assert cycle08_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert cycle09_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    assert "fourteenth_central_moment" not in cycle08_ex
    assert "fourteenth_central_moment" in cycle09_ex

    xs = [Fraction(x) for x in cycle09_ex["shared_support"]]
    qm = [Fraction(x) for x in cycle09_ex["qm_probability_mass"]]
    st = [Fraction(x) for x in cycle09_ex["stat_probability_mass"]]
    qm_mu, qm_var, qm_m3, qm_m4, qm_m6, qm_m8, qm_m10, qm_m12, qm_m14 = _moments14(xs, qm)
    st_mu, st_var, st_m3, st_m4, st_m6, st_m8, st_m10, st_m12, st_m14 = _moments14(xs, st)

    assert qm_mu == st_mu
    assert qm_var == st_var
    assert qm_m3 == st_m3
    assert qm_m4 == st_m4
    assert qm_m6 == st_m6
    assert qm_m8 != st_m8
    assert qm_m10 != st_m10
    assert qm_m12 != st_m12
    assert qm_m14 != st_m14


def test_qm_stat_cycle08_to_09_promotion_still_blocked() -> None:
    cycle08 = _json(CYCLE08_ARTIFACT_PATH)
    cycle09 = _json(CYCLE09_ARTIFACT_PATH)

    assert cycle08["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle09["adjudication"]["value"] == "NOT_YET_DISCHARGED"

    for artifact in (cycle08, cycle09):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["continuum_statistical_closure_claimed"] is False
        assert bounded["external_truth_claimed"] is False
