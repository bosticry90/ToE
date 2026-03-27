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
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json"
PREV_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle06_v0.json"


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


def test_cosmo_sr_cycle07_artifacts_exist() -> None:
    assert DOC_PATH.exists(), "Missing COSMO-SR Cycle07 target doc."
    assert ARTIFACT_PATH.exists(), "Missing COSMO-SR Cycle07 artifact."
    assert PREV_ARTIFACT_PATH.exists(), "Missing COSMO-SR Cycle06 predecessor artifact."


def test_cosmo_sr_cycle07_doc_contains_required_tokens() -> None:
    text = _read(DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE07-v0",
        "COSMO_SR_CYCLE07_STATUS_v0: DODECIC_LOW_Z_ALIGNMENT_AND_EXCLUSION_PINNED_NONCLAIM",
        "COSMO_SR_CYCLE07_BLOCKER_DISCHARGE_CRITERIA_v0: EXACT_SR_DOPPLER_MATCH_DODECIC_IMPROVEMENT_REQUIRED",
        "COSMO_SR_CYCLE07_INCOMPATIBILITY_EXCLUSION_v0: HIGH_Z_DODECIC_SERIES_DRIFT_FLAGGED_AS_NONCOMPATIBLE",
        "COSMO_SR_CYCLE07_SCOPE_v0: FINITE_SAMPLE_LOW_Z_DODECIC_AUDIT_ONLY_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_STATUS_v0: CRITERIA_AND_DODECIC_EXCLUSION_PINNED_NONCLAIM",
        "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR Cycle07 doc missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle07_artifact_schema_and_predecessor_tieback() -> None:
    artifact = _json(ARTIFACT_PATH)
    assert artifact["artifact_id"] == "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0"
    assert artifact["seam_id"] == "SEAM-COSMO-SR"
    assert artifact["class_token"] == "TOE_CK_CLASS_COMPATIBILITY_v0"
    assert artifact["status"] == "CRITERIA_AND_DODECIC_EXCLUSION_PINNED_NONCLAIM"

    derived = artifact["derived_from"]
    assert derived["artifact_id"] == "cosmo_sr_class_b_seam_physics_pilot_cycle06_v0"
    assert derived["artifact_path"] == "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle06_v0.json"


def test_cosmo_sr_cycle07_low_z_dodecic_improvement() -> None:
    artifact = _json(ARTIFACT_PATH)
    criteria = artifact["blocker_discharge_criteria"]

    assert criteria["token"] == "EXACT_SR_DOPPLER_MATCH_DODECIC_IMPROVEMENT_REQUIRED"

    z_min = Fraction(criteria["z_window"]["z_min"])
    z_max = Fraction(criteria["z_window"]["z_max"])
    eps = Fraction(criteria["epsilon_abs"])

    for sample in criteria["samples"]:
        z = Fraction(sample["z"])
        beta_exact = Fraction(sample["beta_exact"])
        beta_series10 = Fraction(sample["beta_series10"])
        beta_series12 = Fraction(sample["beta_series12"])
        abs_delta_series10 = Fraction(sample["abs_delta_series10"])
        abs_delta_series12 = Fraction(sample["abs_delta_series12"])

        assert z_min <= z <= z_max
        assert beta_exact == _sr_beta_exact(z)
        assert beta_series10 == _series10(z)
        assert beta_series12 == _series12(z)

        assert abs(beta_exact - beta_series10) == abs_delta_series10
        assert abs(beta_exact - beta_series12) == abs_delta_series12

        assert abs_delta_series12 <= abs_delta_series10
        assert abs_delta_series12 <= eps


def test_cosmo_sr_cycle07_high_z_exclusion_and_nonclaim_boundary() -> None:
    artifact = _json(ARTIFACT_PATH)
    exclusion = artifact["bounded_incompatibility_exclusion"]

    z = Fraction(exclusion["z"])
    beta_exact = Fraction(exclusion["beta_exact"])
    beta_series12 = Fraction(exclusion["beta_series12"])
    abs_delta = Fraction(exclusion["abs_delta"])

    assert beta_exact == _sr_beta_exact(z)
    assert beta_series12 == _series12(z)
    assert abs(beta_exact - beta_series12) == abs_delta
    assert exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    bounded = artifact["bounded_scope"]
    assert bounded["class_flip_claimed"] is False
    assert bounded["full_theorem_discharge_claimed"] is False
    assert bounded["global_cosmology_completion_claimed"] is False
    assert bounded["external_truth_claimed"] is False

    adjudication = artifact["adjudication"]
    assert adjudication["token"] == "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"
