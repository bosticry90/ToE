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
PACKAGE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_REVIEW_READINESS_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_review_readiness_checkpoint_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_route_review_readiness_package_has_required_structure() -> None:
    text = _read(PACKAGE_PATH)
    required_strings = [
        "Derived physics bundle (bounded):",
        "bounded propagator/two-point-function route",
        "Reconstructed-vs-novel split:",
        "Open physics items:",
        "BOUNDED_DERIVATION_ACHIEVED_v0: TRUE",
        "BROAD_PHYSICS_CLAIM_JUSTIFIED_v0: NOT_YET",
        "REVIEW_READINESS_STATUS_v0: READY_FOR_BOUNDED_FREE_SCALAR_REVIEW",
    ]
    for marker in required_strings:
        assert marker in text, f"Review-readiness package missing marker: {marker}"


def test_toe_qft_scalar_route_review_readiness_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_review_readiness_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_REVIEW_READINESS"

    bundle = artifact.get("derived_bundle", {})
    assert bundle.get("field_equation") is True
    assert bundle.get("covariance_stress_energy") is True
    assert bundle.get("canonical_quantization") is True
    assert bundle.get("operator_mode_normalization") is True
    assert bundle.get("nonrelativistic_limit") is True
    assert bundle.get("propagator_two_point") is True

    interp = artifact.get("interpretation", {})
    assert interp.get("broad_physics_claim_justified") is False

    open_items = artifact.get("open_items", [])
    assert "interacting_field_completion" in open_items
    assert "gauge_sector_completion" in open_items

    assert artifact.get("status") == "READY_FOR_BOUNDED_FREE_SCALAR_REVIEW"
