from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SYNTH_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_v0.md"
)
CYCLE03_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_v0.md"
)
CYCLE04_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_v0.md"
)
CYCLE03_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle03_v0.json"
CYCLE04_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle04_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _sr_beta_exact(z: Fraction) -> Fraction:
    one_plus_z_sq = (Fraction(1, 1) + z) * (Fraction(1, 1) + z)
    return (one_plus_z_sq - 1) / (one_plus_z_sq + 1)


def _series4(z: Fraction) -> Fraction:
    return z - (z * z) / 2 + (z * z * z * z) / 4


def _series6(z: Fraction) -> Fraction:
    return z - (z * z) / 2 + (z * z * z * z) / 4 - (z * z * z * z * z * z) / 8


def test_cosmo_sr_cycle03_to_04_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE03_DOC_PATH, CYCLE04_DOC_PATH, CYCLE03_ARTIFACT_PATH, CYCLE04_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_cosmo_sr_cycle03_to_04_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE03-TO-04-SYNTHESIS-v0",
        "COSMO_SR_CYCLE03_BASELINE_v0: LOW_Z_QUARTIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED",
        "COSMO_SR_CYCLE04_ADDITIVE_DELTA_v0: LOW_Z_SEXTIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED",
        "COSMO_SR_LOW_Z_COMPATIBILITY_IMPACT_v0: SEXTIC_SURROGATE_REDUCES_OR_MATCHES_QUARTIC_RESIDUALS_ON_BOUNDED_WINDOW",
        "COSMO_SR_SEXTIC_DRIFT_EXCLUSION_MEANING_v0: HIGH_Z_SEXTIC_SERIES_DRIFT_EXCLUDED_AS_NONCOMPATIBLE",
        "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE05_ELSE_RETURN_QM_STAT_CYCLE05",
        "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE03_TO_04_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle03_to_04_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR Cycle03-to-04 synthesis doc missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle03_to_04_additive_delta_is_material() -> None:
    cycle03 = _json(CYCLE03_ARTIFACT_PATH)
    cycle04 = _json(CYCLE04_ARTIFACT_PATH)

    c3 = cycle03["blocker_discharge_criteria"]
    c4 = cycle04["blocker_discharge_criteria"]

    assert c3["token"] == "EXACT_SR_DOPPLER_MATCH_QUARTIC_IMPROVEMENT_REQUIRED"
    assert c4["token"] == "EXACT_SR_DOPPLER_MATCH_SEXTIC_IMPROVEMENT_REQUIRED"

    for s3, s4 in zip(c3["samples"], c4["samples"]):
        z3 = Fraction(s3["z"])
        z4 = Fraction(s4["z"])
        assert z3 == z4

        beta_exact3 = Fraction(s3["beta_exact"])
        beta_exact4 = Fraction(s4["beta_exact"])
        assert beta_exact3 == beta_exact4 == _sr_beta_exact(z3)

        assert Fraction(s3["beta_series4"]) == _series4(z3)
        assert Fraction(s4["beta_series4"]) == _series4(z4)
        assert Fraction(s4["beta_series6"]) == _series6(z4)

        abs_delta_s4 = Fraction(s3["abs_delta_series4"])
        abs_delta_s6 = Fraction(s4["abs_delta_series6"])
        assert abs_delta_s6 <= abs_delta_s4


def test_cosmo_sr_cycle03_to_04_sextic_exclusion_and_blockers() -> None:
    cycle03 = _json(CYCLE03_ARTIFACT_PATH)
    cycle04 = _json(CYCLE04_ARTIFACT_PATH)

    c3_ex = cycle03["bounded_incompatibility_exclusion"]
    c4_ex = cycle04["bounded_incompatibility_exclusion"]

    assert c3_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert c4_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    z = Fraction(c4_ex["z"])
    beta_exact = Fraction(c4_ex["beta_exact"])
    beta_series6 = Fraction(c4_ex["beta_series6"])
    abs_delta = Fraction(c4_ex["abs_delta"])

    assert beta_exact == _sr_beta_exact(z)
    assert beta_series6 == _series6(z)
    assert abs(beta_exact - beta_series6) == abs_delta

    assert cycle03["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle04["adjudication"]["value"] == "NOT_YET_DISCHARGED"


def test_cosmo_sr_cycle03_to_04_nonclaim_boundary_preserved() -> None:
    for artifact in (_json(CYCLE03_ARTIFACT_PATH), _json(CYCLE04_ARTIFACT_PATH)):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["global_cosmology_completion_claimed"] is False
        assert bounded["external_truth_claimed"] is False
