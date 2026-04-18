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
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_v0.md"
)
CYCLE01_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0.md"
)
CYCLE01_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle01_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_sr_cycle01_synthesis_artifacts_exist() -> None:
    assert SYNTH_DOC_PATH.exists(), "Missing COSMO-SR synthesis doc."
    assert CYCLE01_DOC_PATH.exists(), "Missing COSMO-SR Cycle01 doc."
    assert CYCLE01_ARTIFACT_PATH.exists(), "Missing COSMO-SR Cycle01 artifact."


def test_cosmo_sr_cycle01_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-SYNTHESIS-v0",
        "COSMO_SR_CYCLE01_CONTRIBUTION_v0: BOUNDED_LOW_Z_KINEMATIC_ALIGNMENT_WITNESS_PINNED",
        "COSMO_SR_LOW_Z_COVERAGE_STATE_v0: LINEAR_ALIGNMENT_ONLY_ON_BOUNDED_LOW_Z_WINDOW",
        "COSMO_SR_HIGH_Z_EXCLUSION_STATE_v0: LINEARIZATION_DRIFT_EXCLUDED_AS_NONCOMPATIBLE",
        "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: THEOREM_LINKED_DISCHARGE_AND_CLASS_FLIP_NOT_READY",
        "COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE02_ELSE_RETURN_QM_STAT_CYCLE03",
        "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR synthesis doc missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle01_synthesis_matches_cycle01_payload() -> None:
    artifact = _json(CYCLE01_ARTIFACT_PATH)

    assert artifact["status"] == "WITNESS_AND_BOUNDED_PAYLOAD_PINNED_NONCLAIM"

    payload = artifact["compatibility_payload"]
    assert payload["payload_status"] == "BOUNDED_LOW_Z_KINEMATIC_ALIGNMENT_PINNED_NONCLAIM"
    assert payload["route"] == "LOW_Z_REDSHIFT_TO_SR_BETA_LINEARIZATION_BRIDGE"
    assert payload["scope"] == "LOW_Z_WINDOW_ONLY_NONCLAIM"

    z_min = Fraction(payload["z_window"]["z_min"])
    z_max = Fraction(payload["z_window"]["z_max"])
    eps = Fraction(payload["epsilon_abs"])

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

    exclusion = artifact["bounded_incompatibility_exclusion"]
    z = Fraction(exclusion["z"])
    beta_sr_linear = Fraction(exclusion["beta_sr_linear"])
    beta_sr_exact = Fraction(exclusion["beta_sr_exact"])
    abs_delta = Fraction(exclusion["abs_delta"])

    one_plus_z_sq = (Fraction(1, 1) + z) * (Fraction(1, 1) + z)
    beta_exact_recomputed = (one_plus_z_sq - 1) / (one_plus_z_sq + 1)

    assert beta_sr_linear == z
    assert beta_sr_exact == beta_exact_recomputed
    assert abs(beta_sr_linear - beta_sr_exact) == abs_delta
    assert exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"


def test_cosmo_sr_cycle01_synthesis_nonclaim_boundary() -> None:
    bounded = _json(CYCLE01_ARTIFACT_PATH)["bounded_scope"]

    assert bounded["class_flip_claimed"] is False
    assert bounded["full_theorem_discharge_claimed"] is False
    assert bounded["global_cosmology_completion_claimed"] is False
    assert bounded["external_truth_claimed"] is False
