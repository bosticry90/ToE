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
DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle01_v0.json"
QM_M4_PATH = REPO_ROOT / "formal" / "output" / "qm_m4_seam_closure_promotion_cycle01_v0.json"
STAT_M4_PATH = REPO_ROOT / "formal" / "output" / "stat_m4_seam_closure_promotion_cycle01_v0.json"
WITNESS_PACKAGE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Constraints" / "SeamWitnessPackages.lean"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qm_stat_pilot_artifacts_exist() -> None:
    for path in (DOC_PATH, ARTIFACT_PATH, QM_M4_PATH, STAT_M4_PATH, WITNESS_PACKAGE_PATH, INVENTORY_PATH, REGISTRY_PATH):
        assert path.exists(), f"Missing required file: {path}"


def test_qm_stat_pilot_doc_contains_required_tokens() -> None:
    text = _read(DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_v0",
        "TARGET-QM-STAT-CLASS-B-SEAM-PHYSICS-PILOT-CYCLE01-v0",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_SEAM_v0: SEAM-QM-STAT",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CLASS_v0: TOE_CK_CLASS_COMPATIBILITY_v0",
        "QM_STAT_COMPATIBILITY_PAYLOAD_STATUS_v0: BOUNDED_MOMENT_TRANSPORT_CONSISTENCY_PINNED_NONCLAIM",
        "QM_STAT_COMPATIBILITY_ROUTE_v0: PROBABILITY_MASS_TO_MOMENT_SURFACE_ALIGNMENT",
        "QM_STAT_COMPATIBILITY_WITNESS_v0: DISCRETE_SPECTRAL_MASS_TO_STAT_MOMENT_MATCH",
        "QM_STAT_COMPATIBILITY_SCOPE_v0: FINITE_STATE_DISCRETE_ONLY_NONCLAIM",
        "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_STATUS_v0: WITNESS_AND_BOUNDED_PAYLOAD_PINNED_NONCLAIM",
        "formal/output/qm_stat_class_b_seam_physics_pilot_cycle01_v0.json",
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle01_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "QM-STAT seam pilot doc is missing required token(s): " + ", ".join(missing)


def test_qm_stat_pilot_artifact_schema_and_tieback() -> None:
    artifact = _json(ARTIFACT_PATH)
    assert artifact["artifact_id"] == "qm_stat_class_b_seam_physics_pilot_cycle01_v0"
    assert artifact["seam_id"] == "SEAM-QM-STAT"
    assert artifact["class_token"] == "TOE_CK_CLASS_COMPATIBILITY_v0"
    assert artifact["status"] == "WITNESS_AND_BOUNDED_PAYLOAD_PINNED_NONCLAIM"
    assert artifact["witness_package_pointer"] == "formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean"

    assert "formal/output/qm_m4_seam_closure_promotion_cycle01_v0.json" in artifact["source_artifacts"]
    assert "formal/output/stat_m4_seam_closure_promotion_cycle01_v0.json" in artifact["source_artifacts"]


def test_qm_stat_bounded_physics_payload_is_moment_consistent() -> None:
    artifact = _json(ARTIFACT_PATH)
    payload = artifact["compatibility_payload"]

    assert payload["payload_status"] == "BOUNDED_MOMENT_TRANSPORT_CONSISTENCY_PINNED_NONCLAIM"
    assert payload["route"] == "PROBABILITY_MASS_TO_MOMENT_SURFACE_ALIGNMENT"
    assert payload["scope"] == "FINITE_STATE_DISCRETE_ONLY_NONCLAIM"

    state_support = payload["state_support"]
    qm_p = [Fraction(x) for x in payload["qm_probability_mass"]]
    stat_p = [Fraction(x) for x in payload["stat_probability_mass"]]
    xs = [Fraction(x) for x in state_support]

    assert sum(qm_p) == 1
    assert sum(stat_p) == 1

    qm_mu = sum(p * x for p, x in zip(qm_p, xs))
    stat_mu = sum(p * x for p, x in zip(stat_p, xs))
    assert qm_mu == Fraction(payload["first_moment"]["qm_mu"])
    assert stat_mu == Fraction(payload["first_moment"]["stat_mu"])

    qm_var = sum(p * (x - qm_mu) * (x - qm_mu) for p, x in zip(qm_p, xs))
    stat_var = sum(p * (x - stat_mu) * (x - stat_mu) for p, x in zip(stat_p, xs))
    assert qm_var == Fraction(payload["second_central_moment"]["qm_var"])
    assert stat_var == Fraction(payload["second_central_moment"]["stat_var"])


def test_qm_stat_pilot_nonclaim_boundary_and_registry_presence() -> None:
    artifact = _json(ARTIFACT_PATH)
    bounded = artifact["bounded_scope"]
    assert bounded["class_flip_claimed"] is False
    assert bounded["full_theorem_discharge_claimed"] is False
    assert bounded["continuum_statistical_closure_claimed"] is False
    assert bounded["external_truth_claimed"] is False

    adjudication = artifact["adjudication"]
    assert adjudication["token"] == "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE01_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"

    inventory_text = _read(INVENTORY_PATH)
    registry_text = _read(REGISTRY_PATH)
    assert "SEAM-QM-STAT" in inventory_text
    assert "SEAM_QM_STAT_STATUS_READ_v0: CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE" in registry_text
