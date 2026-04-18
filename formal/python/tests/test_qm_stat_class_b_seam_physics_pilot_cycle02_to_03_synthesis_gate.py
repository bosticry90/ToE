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
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_TO_03_SYNTHESIS_v0.md"
)
CYCLE02_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_v0.md"
)
CYCLE03_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_v0.md"
)
CYCLE02_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle02_v0.json"
CYCLE03_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle03_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _moments(support: list[Fraction], probs: list[Fraction]) -> tuple[Fraction, Fraction, Fraction]:
    mu = sum(p * x for p, x in zip(probs, support))
    var = sum(p * (x - mu) * (x - mu) for p, x in zip(probs, support))
    m3 = sum(p * (x - mu) * (x - mu) * (x - mu) for p, x in zip(probs, support))
    return mu, var, m3


def test_qm_stat_cycle02_to_03_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE02_DOC_PATH, CYCLE03_DOC_PATH, CYCLE02_ARTIFACT_PATH, CYCLE03_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_qm_stat_cycle02_to_03_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_TO_03_SYNTHESIS_v0",
        "TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE02-TO-03-SYNTHESIS-v0",
        "QM_STAT_CYCLE02_BASELINE_v0: MASS_NORMALIZATION_AND_SECOND_MOMENT_PARITY_CRITERIA_PINNED",
        "QM_STAT_CYCLE03_ADDITIVE_DELTA_v0: THIRD_CENTRAL_MOMENT_PARITY_AND_HIGHER_MOMENT_EXCLUSION_PINNED",
        "QM_STAT_BLOCKER_DISCHARGE_IMPACT_v0: CRITERIA_STRENGTHENED_BUT_ADJUDICATION_STILL_OPEN",
        "QM_STAT_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "QM_STAT_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "QM_STAT_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_QM_STAT_PAYLOAD_IS_READY_THEN_CYCLE04_ELSE_OPEN_COSMO_SR_CYCLE02",
        "QM_STAT_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_TO_03_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_TO_03_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle02_to_03_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "QM-STAT Cycle02-to-03 synthesis doc missing required token(s): " + ", ".join(missing)


def test_qm_stat_cycle02_to_03_additive_delta_is_material() -> None:
    cycle02 = _json(CYCLE02_ARTIFACT_PATH)
    cycle03 = _json(CYCLE03_ARTIFACT_PATH)

    c2 = cycle02["blocker_discharge_criteria"]
    c3 = cycle03["blocker_discharge_criteria"]

    assert c2["token"] == "MASS_NORMALIZATION_AND_MOMENT_PARITY_REQUIRED"
    assert c3["token"] == "MASS_MEAN_VARIANCE_THIRD_MOMENT_PARITY_REQUIRED"

    assert "third_central_moment" not in c2
    assert "third_central_moment" in c3

    xs3 = [Fraction(x) for x in c3["shared_support"]]
    qm3 = [Fraction(x) for x in c3["qm_probability_mass"]]
    st3 = [Fraction(x) for x in c3["stat_probability_mass"]]
    qm_mu3, qm_var3, qm_m3 = _moments(xs3, qm3)
    st_mu3, st_var3, st_m3 = _moments(xs3, st3)

    assert qm_mu3 == st_mu3
    assert qm_var3 == st_var3
    assert qm_m3 == st_m3
    assert qm_m3 == Fraction(c3["third_central_moment"]["qm_m3"])
    assert st_m3 == Fraction(c3["third_central_moment"]["stat_m3"])


def test_qm_stat_cycle02_to_03_promotion_still_blocked() -> None:
    cycle02 = _json(CYCLE02_ARTIFACT_PATH)
    cycle03 = _json(CYCLE03_ARTIFACT_PATH)

    assert cycle02["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle03["adjudication"]["value"] == "NOT_YET_DISCHARGED"

    for artifact in (cycle02, cycle03):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["continuum_statistical_closure_claimed"] is False
        assert bounded["external_truth_claimed"] is False


def test_qm_stat_cycle02_to_03_exclusion_strengthening_present() -> None:
    cycle02_ex = _json(CYCLE02_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]
    cycle03_ex = _json(CYCLE03_ARTIFACT_PATH)["bounded_incompatibility_exclusion"]

    assert cycle02_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert cycle03_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    assert "third_central_moment" not in cycle02_ex
    assert "third_central_moment" in cycle03_ex
