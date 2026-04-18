from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
TARGET_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_INTEGRATION_v0.md"
)
ARTIFACT = (
    REPO_ROOT / "formal" / "output" / "information_constraint_operational_position_integration_v0.json"
)
MASTER_ACTION = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"
SEAM_REGISTRY = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
COMPENDIUM = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_information_constraint_target_and_artifact_exist() -> None:
    assert TARGET_DOC.exists(), "Missing information-constraint target document."
    assert ARTIFACT.exists(), "Missing information-constraint checkpoint artifact."


def test_information_constraint_target_tokens_present() -> None:
    text = _read(TARGET_DOC)
    required = [
        "DERIVATION_TARGET_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_INTEGRATION_v0",
        "TARGET-INFORMATION-CONSTRAINT-OPERATIONAL-POSITION-INTEGRATION-v0",
        "INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_ADJUDICATION_v0: NOT_YET_DISCHARGED",
        "POSITION_OPERATIONAL_SURFACE_v0: POSITION_AS_TIMING_AND_CORRELATION_CONSTRAINT_SATISFIABILITY",
        "INFORMATION_CONSISTENCY_FUNCTIONAL_SURFACE_v0: I_PHI_TIMING_PLUS_CORRELATION_PLUS_CAUSAL_ADMISSIBILITY",
        "RESONANCE_CLOSURE_QUANTIZATION_SURFACE_v0: PHASE_CLOSURE_2PI_N_STATEMENT_LOCK",
        "HIERARCHICAL_CHIRALITY_COUPLING_SURFACE_v0: CHIRALITY_AS_MULTISCALE_CONSTRAINT_FUNCTIONAL",
        "DRESSED_STATE_EMERGENCE_SURFACE_v0: OBSERVED_OBJECT_AS_EXCITATION_PLUS_BACKREACTION_PATTERN",
        "INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_STATUS_v0: FOUNDATION_PINNED_NONCLAIM",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing target token(s): " + ", ".join(missing)


def test_information_constraint_artifact_schema_and_bounds() -> None:
    artifact = _json(ARTIFACT)
    assert artifact["artifact_id"] == "information_constraint_operational_position_integration_v0"
    assert artifact["target_id"] == "TARGET-INFORMATION-CONSTRAINT-OPERATIONAL-POSITION-INTEGRATION-v0"
    assert artifact["status"] == "FOUNDATION_PINNED_NONCLAIM"

    expected_tokens = {
        "TOE_CK_CLASS_COMPATIBILITY_v0",
        "TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0",
        "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0",
        "TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0",
    }
    observed_tokens = {row["token"] for row in artifact["seam_class_bindings"]}
    assert observed_tokens == expected_tokens

    bounded = artifact["bounded_scope"]
    assert bounded["class_flip_claimed"] is False
    assert bounded["seam_physics_complete_claimed"] is False
    assert bounded["canonical_action_promotion_claimed"] is False
    assert bounded["external_truth_claimed"] is False
    assert bounded["release_gate_policy_changed"] is False
    assert bounded["packet_hold_posture_changed"] is False


def test_information_constraint_cross_surface_tokens_present() -> None:
    master_action_text = _read(MASTER_ACTION)
    seam_registry_text = _read(SEAM_REGISTRY)
    compendium_text = _read(COMPENDIUM)

    assert "INFO_CONSTRAINT_LAYER_STATUS_v0: FOUNDATION_PINNED_NONCLAIM" in master_action_text
    assert "POSITION_OPERATIONAL_MAP_STATUS_v0: FOUNDATION_PINNED_NONCLAIM" in master_action_text

    assert "INFORMATION_CONSTRAINT_CLASS_BINDING_STATUS_v0: FOUNDATION_PINNED_NONCLAIM" in seam_registry_text
    assert "TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0 -> timing-window + causal-order admissibility" in seam_registry_text

    assert "EQ-INFO-OPERATIONAL-POSITION-CONSTRAINT-v0" in compendium_text
    assert "WORK-PHYS-INFO-CONSTRAINT-INTEGRATION-v0" in compendium_text
