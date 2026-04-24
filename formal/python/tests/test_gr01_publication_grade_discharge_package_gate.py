from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PACKAGE_DOC = REPO_ROOT / "formal" / "docs" / "release" / "GR01_PUBLICATION_GRADE_DISCHARGE_PACKAGE_v0.md"
PACKAGE_ARTIFACT = REPO_ROOT / "formal" / "output" / "gr01_publication_grade_discharge_package_v0.json"
GR_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"
COMPLETENESS_GATE = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_COMPLETENESS_GATE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_gr01_publication_grade_package_is_cross_pinned() -> None:
    package_text = _read(PACKAGE_DOC)
    gr_text = _read(GR_DOC)
    gate_text = _read(COMPLETENESS_GATE)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    artifact = _read_json(PACKAGE_ARTIFACT)

    for token in (
        "GR01_PUBLICATION_GRADE_DISCHARGE_PACKAGE_v0",
        "GR01_PUBLICATION_GRADE_DISCHARGE_PACKAGE_STATUS_v0: PACKAGE_COMPLETE_v0_DISCRETE_SCOPE_NONCLAIM",
        "GR01_PUBLICATION_GRADE_DISCHARGE_SCOPE_v0: DISCRETE_WEAK_FIELD_ONLY",
        "GR01_PUBLICATION_GRADE_DISCHARGE_GATE_v0: CROSS_SURFACE_PACKAGE_PARITY_REQUIRED",
    ):
        assert token in package_text
        assert token in gr_text

    assert "formal/docs/release/GR01_PUBLICATION_GRADE_DISCHARGE_PACKAGE_v0.md" in gate_text
    for text in (state_text, roadmap_text):
        assert "formal/docs/release/GR01_PUBLICATION_GRADE_DISCHARGE_PACKAGE_v0.md" in text
        assert "formal/output/gr01_publication_grade_discharge_package_v0.json" in text
        assert "formal/python/tests/test_gr01_publication_grade_discharge_package_gate.py" in text

    assert artifact["artifact_id"] == "gr01_publication_grade_discharge_package_v0"
    assert artifact["status"] == "PACKAGE_COMPLETE_v0_DISCRETE_SCOPE_NONCLAIM"
    assert artifact["scope"] == "DISCRETE_WEAK_FIELD_ONLY"
    assert artifact["interpretation"]["publication_package_complete"] is True
    assert artifact["interpretation"]["continuum_limit_claimed"] is False