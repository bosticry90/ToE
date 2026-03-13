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
GR_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0.md"
SR_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0.md"
GR_ARTIFACT = REPO_ROOT / "formal" / "output" / "gr_empirical_comparison_packet_05_v0.json"
SR_ARTIFACT = REPO_ROOT / "formal" / "output" / "sr_empirical_comparison_packet_05_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_empirical_packet05_falsification_surfaces_are_explicit() -> None:
    gr_text = _read(GR_DOC)
    sr_text = _read(SR_DOC)
    gr_payload = _read_json(GR_ARTIFACT)["payload"]
    sr_payload = _read_json(SR_ARTIFACT)["payload"]

    assert "GR_EMPIRICAL_PACKET_05_INVALIDATION_HOOK_v0: WEAK_FIELD_POISSON_RESIDUAL_SIGN_OR_SCALE_FAILURE" in gr_text
    assert "SR_EMPIRICAL_PACKET_05_INVALIDATION_HOOK_v0: COVARIANCE_DISCRIMINATOR_DRIFT_EXCEEDS_BOUNDED_TOLERANCE" in sr_text
    assert gr_payload["falsification_surface_pointer"] == "formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0.md"
    assert sr_payload["falsification_surface_pointer"] == "formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0.md"

    for text in (_read(ROADMAP_PATH), _read(STATE_PATH)):
        assert "formal/python/tests/test_empirical_packet05_falsification_surface_gate.py" in text