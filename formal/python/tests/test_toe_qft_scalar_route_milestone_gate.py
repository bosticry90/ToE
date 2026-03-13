from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
SUMMARY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_MILESTONE_SUMMARY_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_milestone_checkpoint_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_route_milestone_summary_has_required_structure() -> None:
    text = _read(SUMMARY_PATH)
    required_strings = [
        "Pinned derivation ladder (current milestone)",
        "bounded free-scalar QFT-to-QM bridge track",
        "Open items (bounded backlog)",
        "Non-claim boundary:",
        "does not claim interacting-field completion",
        "Reproducibility pointers:",
    ]
    for marker in required_strings:
        assert marker in text, f"Milestone summary missing marker: {marker}"


def test_toe_qft_scalar_route_milestone_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_milestone_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_MILESTONE_CONSOLIDATION"
    assert artifact.get("route_scope") == "bounded_free_scalar_qft_to_qm_bridge"

    ladder = artifact.get("ladder_checkpoint", {})
    assert ladder.get("charter_criteria_pinned") is True
    assert ladder.get("field_and_covariance_pinned") is True
    assert ladder.get("quantization_hamiltonian_pinned") is True
    assert ladder.get("operator_mode_pinned") is True
    assert ladder.get("normalization_one_particle_pinned") is True
    assert ladder.get("nonrelativistic_schrodinger_bridge_pinned") is True
    assert ladder.get("propagator_two_point_pinned") is True
    assert ladder.get("review_readiness_package_pinned") is True

    open_items = artifact.get("open_items", [])
    assert "interacting_field_depth_tranche_deferred" in open_items
    assert "gauge_adjacent_lane_deferred" in open_items

    non_claims = artifact.get("non_claim_boundaries", [])
    assert "no_interacting_field_completion_claim" in non_claims
    assert "no_gauge_sector_completion_claim" in non_claims

    assert artifact.get("status") == "MILESTONE_PINNED_BOUNDED_FREE_SCALAR_QFT_TO_QM_BRIDGE_PROPAGATOR_AND_REVIEW_READY"
