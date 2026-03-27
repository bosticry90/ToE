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
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_v0.md"
)
CYCLE06_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_v0.md"
)
CYCLE07_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md"
)
CYCLE06_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle06_v0.json"
CYCLE07_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _sr_beta_exact(z: Fraction) -> Fraction:
    one_plus_z_sq = (Fraction(1, 1) + z) * (Fraction(1, 1) + z)
    return (one_plus_z_sq - 1) / (one_plus_z_sq + 1)


def _series10(z: Fraction) -> Fraction:
    return z - (z * z) / 2 + (z * z * z * z) / 4 - (z * z * z * z * z * z) / 8 - (z * z * z * z * z * z * z * z) / 16 - (z * z * z * z * z * z * z * z * z * z) / 32


def _series12(z: Fraction) -> Fraction:
    return (
        z
        - (z * z) / 2
        + (z * z * z * z) / 4
        - (z * z * z * z * z * z) / 8
        - (z * z * z * z * z * z * z * z) / 16
        - (z * z * z * z * z * z * z * z * z * z) / 32
        - (z * z * z * z * z * z * z * z * z * z * z * z) / 64
    )


def test_cosmo_sr_cycle06_to_07_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE06_DOC_PATH, CYCLE07_DOC_PATH, CYCLE06_ARTIFACT_PATH, CYCLE07_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_cosmo_sr_cycle06_to_07_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE06-TO-07-SYNTHESIS-v0",
        "COSMO_SR_CYCLE06_BASELINE_v0: LOW_Z_DECIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED",
        "COSMO_SR_CYCLE07_ADDITIVE_DELTA_v0: LOW_Z_DODECIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED",
        "COSMO_SR_LOW_Z_COMPATIBILITY_IMPACT_v0: DODECIC_SURROGATE_REDUCES_OR_MATCHES_DECIC_RESIDUALS_ON_BOUNDED_WINDOW",
        "COSMO_SR_DODECIC_DRIFT_EXCLUSION_MEANING_v0: HIGH_Z_DODECIC_SERIES_DRIFT_EXCLUDED_AS_NONCOMPATIBLE",
        "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE08_ELSE_OPEN_QM_STAT_CYCLE08",
        "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE06_TO_07_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle06_to_07_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR Cycle06-to-07 synthesis doc missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle06_to_07_additive_delta_is_material() -> None:
    cycle06 = _json(CYCLE06_ARTIFACT_PATH)
    cycle07 = _json(CYCLE07_ARTIFACT_PATH)

    c6 = cycle06["blocker_discharge_criteria"]
    c7 = cycle07["blocker_discharge_criteria"]

    assert c6["token"] == "EXACT_SR_DOPPLER_MATCH_DECIC_IMPROVEMENT_REQUIRED"
    assert c7["token"] == "EXACT_SR_DOPPLER_MATCH_DODECIC_IMPROVEMENT_REQUIRED"

    for s6, s7 in zip(c6["samples"], c7["samples"]):
        z6 = Fraction(s6["z"])
        z7 = Fraction(s7["z"])
        assert z6 == z7

        beta_exact6 = Fraction(s6["beta_exact"])
        beta_exact7 = Fraction(s7["beta_exact"])
        assert beta_exact6 == beta_exact7 == _sr_beta_exact(z6)

        assert Fraction(s6["beta_series10"]) == _series10(z6)
        assert Fraction(s7["beta_series10"]) == _series10(z7)
        assert Fraction(s7["beta_series12"]) == _series12(z7)

        abs_delta_s10 = Fraction(s6["abs_delta_series10"])
        abs_delta_s12 = Fraction(s7["abs_delta_series12"])
        assert abs_delta_s12 <= abs_delta_s10


def test_cosmo_sr_cycle06_to_07_dodecic_exclusion_and_blockers() -> None:
    cycle06 = _json(CYCLE06_ARTIFACT_PATH)
    cycle07 = _json(CYCLE07_ARTIFACT_PATH)

    c6_ex = cycle06["bounded_incompatibility_exclusion"]
    c7_ex = cycle07["bounded_incompatibility_exclusion"]

    assert c6_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert c7_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    z = Fraction(c7_ex["z"])
    beta_exact = Fraction(c7_ex["beta_exact"])
    beta_series12 = Fraction(c7_ex["beta_series12"])
    abs_delta = Fraction(c7_ex["abs_delta"])

    assert beta_exact == _sr_beta_exact(z)
    assert beta_series12 == _series12(z)
    assert abs(beta_exact - beta_series12) == abs_delta

    assert cycle06["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle07["adjudication"]["value"] == "NOT_YET_DISCHARGED"


def test_cosmo_sr_cycle06_to_07_nonclaim_boundary_preserved() -> None:
    for artifact in (_json(CYCLE06_ARTIFACT_PATH), _json(CYCLE07_ARTIFACT_PATH)):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["global_cosmology_completion_claimed"] is False
        assert bounded["external_truth_claimed"] is False
