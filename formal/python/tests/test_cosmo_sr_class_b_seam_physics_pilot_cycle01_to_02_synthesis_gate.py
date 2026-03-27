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
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_v0.md"
)
CYCLE01_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0.md"
)
CYCLE02_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE02_v0.md"
)
CYCLE01_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle01_v0.json"
CYCLE02_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle02_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _sr_beta_exact(z: Fraction) -> Fraction:
    one_plus_z_sq = (Fraction(1, 1) + z) * (Fraction(1, 1) + z)
    return (one_plus_z_sq - 1) / (one_plus_z_sq + 1)


def test_cosmo_sr_cycle01_to_02_synthesis_artifacts_exist() -> None:
    for path in (SYNTH_DOC_PATH, CYCLE01_DOC_PATH, CYCLE02_DOC_PATH, CYCLE01_ARTIFACT_PATH, CYCLE02_ARTIFACT_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_cosmo_sr_cycle01_to_02_synthesis_doc_tokens() -> None:
    text = _read(SYNTH_DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_v0",
        "TARGET-COSMO-SR-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-TO-02-SYNTHESIS-v0",
        "COSMO_SR_CYCLE01_BASELINE_v0: LOW_Z_LINEAR_ALIGNMENT_WITNESS_PINNED",
        "COSMO_SR_CYCLE02_ADDITIVE_DELTA_v0: LOW_Z_SECOND_ORDER_MATCH_IMPROVEMENT_AND_EXCLUSION_PINNED",
        "COSMO_SR_LOW_Z_COMPATIBILITY_IMPACT_v0: SECOND_ORDER_SURROGATE_REDUCES_EXACT_MAP_RESIDUALS_ON_BOUNDED_WINDOW",
        "COSMO_SR_SECOND_ORDER_EXCLUSION_MEANING_v0: HIGH_Z_SERIES_DRIFT_EXCLUDED_AS_NONCOMPATIBLE",
        "COSMO_SR_PROMOTION_BLOCKER_STATE_v0: CLASS_FLIP_AND_FULL_THEOREM_DISCHARGE_NOT_READY",
        "COSMO_SR_NONCLAIM_BOUNDARY_STATE_v0: CLASS_FLIP_AND_FULL_DISCHARGE_NOT_CLAIMED",
        "COSMO_SR_NEXT_DECISION_RULE_v0: IF_ONE_BOUNDED_ADDITIVE_COSMO_SR_PAYLOAD_IS_READY_THEN_CYCLE03_ELSE_RETURN_QM_STAT_CYCLE04",
        "COSMO_SR_DECISION_BOUNDARY_STATUS_v0: SYNTHESIS_CHECKPOINT_READY",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_STATUS_v0: CHECKPOINT_PINNED_NONCLAIM",
        "COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_TO_02_SYNTHESIS_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle01_to_02_synthesis_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "COSMO-SR Cycle01-to-02 synthesis doc missing required token(s): " + ", ".join(missing)


def test_cosmo_sr_cycle01_to_02_additive_delta_is_material() -> None:
    cycle01 = _json(CYCLE01_ARTIFACT_PATH)
    cycle02 = _json(CYCLE02_ARTIFACT_PATH)

    c1_payload = cycle01["compatibility_payload"]
    assert c1_payload["payload_status"] == "BOUNDED_LOW_Z_KINEMATIC_ALIGNMENT_PINNED_NONCLAIM"

    c2_criteria = cycle02["blocker_discharge_criteria"]
    assert c2_criteria["token"] == "EXACT_SR_DOPPLER_MATCH_IMPROVEMENT_REQUIRED"

    for sample in c2_criteria["samples"]:
        z = Fraction(sample["z"])
        beta_exact = Fraction(sample["beta_exact"])
        beta_linear = Fraction(sample["beta_linear"])
        beta_series2 = Fraction(sample["beta_series2"])
        abs_delta_linear = Fraction(sample["abs_delta_linear"])
        abs_delta_series2 = Fraction(sample["abs_delta_series2"])

        assert beta_exact == _sr_beta_exact(z)
        assert beta_linear == z
        assert beta_series2 == z - (z * z) / 2

        assert abs(beta_exact - beta_linear) == abs_delta_linear
        assert abs(beta_exact - beta_series2) == abs_delta_series2
        assert abs_delta_series2 <= abs_delta_linear


def test_cosmo_sr_cycle01_to_02_second_order_exclusion_and_blockers() -> None:
    cycle01 = _json(CYCLE01_ARTIFACT_PATH)
    cycle02 = _json(CYCLE02_ARTIFACT_PATH)

    c1_exclusion = cycle01["bounded_incompatibility_exclusion"]
    c2_exclusion = cycle02["bounded_incompatibility_exclusion"]

    assert c1_exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"
    assert c2_exclusion["classification"] == "NONCOMPATIBLE_EXCLUDED_v0"

    z = Fraction(c2_exclusion["z"])
    beta_exact = Fraction(c2_exclusion["beta_exact"])
    beta_series2 = Fraction(c2_exclusion["beta_series2"])
    abs_delta = Fraction(c2_exclusion["abs_delta"])

    assert beta_exact == _sr_beta_exact(z)
    assert beta_series2 == z - (z * z) / 2
    assert abs(beta_exact - beta_series2) == abs_delta

    assert cycle01["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert cycle02["adjudication"]["value"] == "NOT_YET_DISCHARGED"


def test_cosmo_sr_cycle01_to_02_nonclaim_boundary_preserved() -> None:
    for artifact in (_json(CYCLE01_ARTIFACT_PATH), _json(CYCLE02_ARTIFACT_PATH)):
        bounded = artifact["bounded_scope"]
        assert bounded["class_flip_claimed"] is False
        assert bounded["full_theorem_discharge_claimed"] is False
        assert bounded["global_cosmology_completion_claimed"] is False
        assert bounded["external_truth_claimed"] is False
