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
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle01_v0.json"
COSMO_M4_PATH = REPO_ROOT / "formal" / "output" / "cosmo_m4_seam_closure_promotion_cycle01_v0.json"
SR_M4_PATH = REPO_ROOT / "formal" / "output" / "sr_m4_seam_closure_promotion_cycle01_v0.json"
WITNESS_PACKAGE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Constraints" / "SeamWitnessPackages.lean"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_sr_cycle01_artifacts_exist() -> None:
    for path in (DOC_PATH, ARTIFACT_PATH, COSMO_M4_PATH, SR_M4_PATH, WITNESS_PACKAGE_PATH, INVENTORY_PATH, REGISTRY_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_cosmo_sr_cycle01_doc_contains_required_tokens() -> None:
    text = _read(DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-v0",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_SEAM_v0: SEAM-COSMO-SR",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CLASS_v0: TOE_CK_CLASS_COMPATIBILITY_v0",
        "COSMO_SR_COMPATIBILITY_PAYLOAD_STATUS_v0: BOUNDED_LOW_Z_KINEMATIC_ALIGNMENT_PINNED_NONCLAIM",
        "COSMO_SR_COMPATIBILITY_ROUTE_v0: LOW_Z_REDSHIFT_TO_SR_BETA_LINEARIZATION_BRIDGE",
        "COSMO_SR_COMPATIBILITY_WITNESS_v0: LOW_Z_LINEAR_POINTWISE_ALIGNMENT",
        "COSMO_SR_COMPATIBILITY_SCOPE_v0: LOW_Z_WINDOW_ONLY_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_STATUS_v0: WITNESS_AND_BOUNDED_PAYLOAD_PINNED_NONCLAIM",
        "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle01_v0.json",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR Cycle01 doc is missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle01_artifact_schema_and_tieback() -> None:
    artifact = _json(ARTIFACT_PATH)
    assert artifact["artifact_id"] == "cosmo_sr_class_b_seam_physics_pilot_cycle01_v0"
    assert artifact["seam_id"] == "SEAM-COSMO-SR"
    assert artifact["class_token"] == "TOE_CK_CLASS_COMPATIBILITY_v0"
    assert artifact["status"] == "WITNESS_AND_BOUNDED_PAYLOAD_PINNED_NONCLAIM"
    assert artifact["witness_package_pointer"] == "formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean"

    assert "formal/output/cosmo_m4_seam_closure_promotion_cycle01_v0.json" in artifact["source_artifacts"]
    assert "formal/output/sr_m4_seam_closure_promotion_cycle01_v0.json" in artifact["source_artifacts"]


def test_cosmo_sr_cycle01_low_z_compatibility_witness_is_consistent() -> None:
    artifact = _json(ARTIFACT_PATH)
    payload = artifact["compatibility_payload"]

    assert payload["payload_status"] == "BOUNDED_LOW_Z_KINEMATIC_ALIGNMENT_PINNED_NONCLAIM"
    assert payload["route"] == "LOW_Z_REDSHIFT_TO_SR_BETA_LINEARIZATION_BRIDGE"
    assert payload["scope"] == "LOW_Z_WINDOW_ONLY_NONCLAIM"

    z_min = Fraction(payload["z_window"]["z_min"])
    z_max = Fraction(payload["z_window"]["z_max"])
    eps = Fraction(payload["epsilon_abs"])
    assert z_min <= z_max

    for sample in payload["samples"]:
        z = Fraction(sample["z"])
        beta_sr = Fraction(sample["beta_sr_linear"])
        beta_cosmo = Fraction(sample["beta_cosmo_linear"])
        abs_delta = Fraction(sample["abs_delta"])

        assert z_min <= z <= z_max
        assert beta_sr == z
        assert beta_cosmo == z
        assert abs(beta_sr - beta_cosmo) == abs_delta
        assert abs_delta <= eps


def test_cosmo_sr_cycle01_high_z_exclusion_and_nonclaim_boundary() -> None:
    artifact = _json(ARTIFACT_PATH)
    exclusion = artifact["bounded_incompatibility_exclusion"]

    z = Fraction(exclusion["z"])
    beta_sr_linear = Fraction(exclusion["beta_sr_linear"])
    beta_sr_exact = Fraction(exclusion["beta_sr_exact"])
    abs_delta = Fraction(exclusion["abs_delta"])

    # Relativistic Doppler map for recession-like kinematics: beta=( (1+z)^2 - 1 ) / ( (1+z)^2 + 1 )
    one_plus_z_sq = (Fraction(1, 1) + z) * (Fraction(1, 1) + z)
    beta_exact_recomputed = (one_plus_z_sq - 1) / (one_plus_z_sq + 1)

    assert beta_sr_linear == z
    assert beta_sr_exact == beta_exact_recomputed
    assert abs(beta_sr_linear - beta_sr_exact) == abs_delta
    assert exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    bounded = artifact["bounded_scope"]
    assert bounded["class_flip_claimed"] is False
    assert bounded["full_theorem_discharge_claimed"] is False
    assert bounded["global_cosmology_completion_claimed"] is False
    assert bounded["external_truth_claimed"] is False

    adjudication = artifact["adjudication"]
    assert adjudication["token"] == "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"
