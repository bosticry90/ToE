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
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_v0.md"
)
CYCLE04_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_v0.md"
)
CYCLE05_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_v0.md"
)
CYCLE04_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle04_v0.json"
CYCLE05_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle05_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _sr_beta_exact(z: Fraction) -> Fraction:
    one_plus_z_sq = (Fraction(1, 1) + z) * (Fraction(1, 1) + z)
    return (one_plus_z_sq - 1) / (one_plus_z_sq + 1)


def _series6(z: Fraction) -> Fraction:
    return z - (z * z) / 2 + (z * z * z * z) / 4 - (z * z * z * z * z * z) / 8


def _series8(z: Fraction) -> Fraction:
    return z - (z * z) / 2 + (z * z * z * z) / 4 - (z * z * z * z * z * z) / 8 - (z * z * z * z * z * z * z * z) / 16


def test_cosmo_sr_cycle04_to_05_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE04_DOC_PATH, CYCLE05_DOC_PATH, CYCLE04_ARTIFACT_PATH, CYCLE05_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_cosmo_sr_cycle04_to_05_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE04-TO-05-SYNTHESIS-v0",
        "COSMO_SR_CYCLE04_BASELINE_v0: LOW_Z_SEXTIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED",
        "COSMO_SR_CYCLE05_ADDITIVE_DELTA_v0: LOW_Z_OCTIC_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED",
        "COSMO_SR_LOW_Z_COMPATIBILITY_IMPACT_v0: OCTIC_SURROGATE_REDUCES_OR_MATCHES_SEXTIC_RESIDUALS_ON_BOUNDED_WINDOW",
        "COSMO_SR_OCTIC_DRIFT_EXCLUSION_MEANING_v0: HIGH_Z_OCTIC_SERIES_DRIFT_EXCLUDED_AS_NONCOMPATIBLE",
        "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE06_ELSE_RETURN_QM_STAT_CYCLE05",
        "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE04_TO_05_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle04_to_05_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR Cycle04-to-05 synthesis doc missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle04_to_05_additive_delta_is_material() -> None:
    cycle04 = _json(CYCLE04_ARTIFACT_PATH)
    cycle05 = _json(CYCLE05_ARTIFACT_PATH)

    c4 = cycle04["blocker_discharge_criteria"]
    c5 = cycle05["blocker_discharge_criteria"]

    assert c4["token"] == "EXACT_SR_DOPPLER_MATCH_SEXTIC_IMPROVEMENT_REQUIRED"
    assert c5["token"] == "EXACT_SR_DOPPLER_MATCH_OCTIC_IMPROVEMENT_REQUIRED"

    for s4, s5 in zip(c4["samples"], c5["samples"]):
        z4 = Fraction(s4["z"])
        z5 = Fraction(s5["z"])
        assert z4 == z5

        beta_exact4 = Fraction(s4["beta_exact"])
        beta_exact5 = Fraction(s5["beta_exact"])
        assert beta_exact4 == beta_exact5 == _sr_beta_exact(z4)

        assert Fraction(s4["beta_series6"]) == _series6(z4)
        assert Fraction(s5["beta_series6"]) == _series6(z5)
        assert Fraction(s5["beta_series8"]) == _series8(z5)

        abs_delta_s6 = Fraction(s4["abs_delta_series6"])
        abs_delta_s8 = Fraction(s5["abs_delta_series8"])
        assert abs_delta_s8 <= abs_delta_s6


def test_cosmo_sr_cycle04_to_05_octic_exclusion_and_blockers() -> None:
    cycle04 = _json(CYCLE04_ARTIFACT_PATH)
    cycle05 = _json(CYCLE05_ARTIFACT_PATH)

    c4_ex = cycle04["bounded_incompatibility_exclusion"]
    c5_ex = cycle05["bounded_incompatibility_exclusion"]

    assert c4_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert c5_ex["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    z = Fraction(c5_ex["z"])
    beta_exact = Fraction(c5_ex["beta_exact"])
    beta_series8 = Fraction(c5_ex["beta_series8"])
    abs_delta = Fraction(c5_ex["abs_delta"])

    assert beta_exact == _sr_beta_exact(z)
    assert beta_series8 == _series8(z)
    assert abs(beta_exact - beta_series8) == abs_delta

    assert cycle04["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle05["adjudication"]["value"] == "NOT_YET_DISCHARGED"


def test_cosmo_sr_cycle04_to_05_nonclaim_boundary_preserved() -> None:
    for artifact in (_json(CYCLE04_ARTIFACT_PATH), _json(CYCLE05_ARTIFACT_PATH)):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["global_cosmology_completion_claimed"] is False
        assert bounded["external_truth_claimed"] is False
