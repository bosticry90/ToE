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
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle05_v0.json"
PREV_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle04_v0.json"


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


def test_cosmo_sr_cycle05_artifacts_exist() -> None:
    assert DOC_PATH.exists(), "Missing COSMO-SR Cycle05 target doc."
    assert ARTIFACT_PATH.exists(), "Missing COSMO-SR Cycle05 artifact."
    assert PREV_ARTIFACT_PATH.exists(), "Missing COSMO-SR Cycle04 predecessor artifact."


def test_cosmo_sr_cycle05_doc_contains_required_tokens() -> None:
    text = _read(DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE05-v0",
        "COSMO_SR_CYCLE05_STATUS_v0: OCTIC_LOW_Z_ALIGNMENT_AND_EXCLUSION_PINNED_NONCLAIM",
        "COSMO_SR_CYCLE05_BLOCKER_DISCHARGE_CRITERIA_v0: EXACT_SR_DOPPLER_MATCH_OCTIC_IMPROVEMENT_REQUIRED",
        "COSMO_SR_CYCLE05_INCOMPATIBILITY_EXCLUSION_v0: HIGH_Z_OCTIC_SERIES_DRIFT_FLAGGED_AS_NONCOMPATIBLE",
        "COSMO_SR_CYCLE05_SCOPE_v0: FINITE_SAMPLE_LOW_Z_OCTIC_AUDIT_ONLY_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_STATUS_v0: CRITERIA_AND_OCTIC_EXCLUSION_PINNED_NONCLAIM",
        "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle05_v0.json",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle05_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR Cycle05 doc missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle05_artifact_schema_and_predecessor_tieback() -> None:
    artifact = _json(ARTIFACT_PATH)
    assert artifact["artifact_id"] == "cosmo_sr_class_b_seam_physics_pilot_cycle05_v0"
    assert artifact["seam_id"] == "SEAM-COSMO-SR"
    assert artifact["class_token"] == "TOE_CK_CLASS_COMPATIBILITY_v0"
    assert artifact["status"] == "CRITERIA_AND_OCTIC_EXCLUSION_PINNED_NONCLAIM"

    derived = artifact["derived_from"]
    assert derived["artifact_id"] == "cosmo_sr_class_b_seam_physics_pilot_cycle04_v0"
    assert derived["artifact_path"] == "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle04_v0.json"


def test_cosmo_sr_cycle05_low_z_octic_improvement() -> None:
    artifact = _json(ARTIFACT_PATH)
    criteria = artifact["blocker_discharge_criteria"]

    assert criteria["token"] == "EXACT_SR_DOPPLER_MATCH_OCTIC_IMPROVEMENT_REQUIRED"

    z_min = Fraction(criteria["z_window"]["z_min"])
    z_max = Fraction(criteria["z_window"]["z_max"])
    eps = Fraction(criteria["epsilon_abs"])

    for sample in criteria["samples"]:
        z = Fraction(sample["z"])
        beta_exact = Fraction(sample["beta_exact"])
        beta_series6 = Fraction(sample["beta_series6"])
        beta_series8 = Fraction(sample["beta_series8"])
        abs_delta_series6 = Fraction(sample["abs_delta_series6"])
        abs_delta_series8 = Fraction(sample["abs_delta_series8"])

        assert z_min <= z <= z_max
        assert beta_exact == _sr_beta_exact(z)
        assert beta_series6 == _series6(z)
        assert beta_series8 == _series8(z)

        assert abs(beta_exact - beta_series6) == abs_delta_series6
        assert abs(beta_exact - beta_series8) == abs_delta_series8

        assert abs_delta_series8 <= abs_delta_series6
        assert abs_delta_series8 <= eps


def test_cosmo_sr_cycle05_high_z_exclusion_and_nonclaim_boundary() -> None:
    artifact = _json(ARTIFACT_PATH)
    exclusion = artifact["bounded_incompatibility_exclusion"]

    z = Fraction(exclusion["z"])
    beta_exact = Fraction(exclusion["beta_exact"])
    beta_series8 = Fraction(exclusion["beta_series8"])
    abs_delta = Fraction(exclusion["abs_delta"])

    assert beta_exact == _sr_beta_exact(z)
    assert beta_series8 == _series8(z)
    assert abs(beta_exact - beta_series8) == abs_delta
    assert exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    bounded = artifact["bounded_scope"]
    assert bounded["class_flip_claimed"] is False
    assert bounded["full_theorem_discharge_claimed"] is False
    assert bounded["global_cosmology_completion_claimed"] is False
    assert bounded["external_truth_claimed"] is False

    adjudication = artifact["adjudication"]
    assert adjudication["token"] == "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE05_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"
