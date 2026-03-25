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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SCORED_AUDIT_MATRIX_v1.json"
GUIDE_PATH = REPO_ROOT / "formal" / "markdown" / "SCORED_AUDIT_MATRIX_READER_GUIDE_v1.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

REQUIRED_DOMAINS = (
    "ARCHITECTURE_GOVERNANCE",
    "DERIVATION_CHAIN_COMPLETENESS",
    "SEAM_PHYSICS_CLOSURE",
    "EVIDENCE_TIER_PROGRESSION",
    "MATHEMATICAL_FORMALIZATION",
    "MAINTENANCE_HEALTH",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_matrix_has_required_top_level_schema() -> None:
    data = _read_json(MATRIX_PATH)

    assert data["matrix_id"] == "SCORED_AUDIT_MATRIX_v1"
    assert data["matrix_version"] == 1
    assert "non_claim_boundary" in data
    assert "audit_rows" in data and isinstance(data["audit_rows"], list) and data["audit_rows"]

    domains = tuple(data["score_domains"])
    assert domains == REQUIRED_DOMAINS


def test_each_row_has_required_domains_and_bounded_safeguard() -> None:
    data = _read_json(MATRIX_PATH)

    for row in data["audit_rows"]:
        scores = row["scores"]
        for domain in REQUIRED_DOMAINS:
            assert domain in scores
            assert "score" in scores[domain]
            assert 0 <= int(scores[domain]["score"]) <= 10
        assert row.get("non_overread_safeguard")


def test_low_seam_score_requires_open_debt() -> None:
    data = _read_json(MATRIX_PATH)

    for row in data["audit_rows"]:
        seam = row["scores"]["SEAM_PHYSICS_CLOSURE"]
        if int(seam["score"]) < 5:
            assert "open_debt" in seam and seam["open_debt"]


def test_summary_preserves_global_noncompletion_posture() -> None:
    data = _read_json(MATRIX_PATH)
    summary = data["summary_scores"]

    assert summary["OVERALL_PHYSICS"] == "DISCRIMINATIVE_MIXED_PROGRESS"
    assert summary["OVERALL_SEAM_PHYSICS_COMPLETE_GLOBAL"] == "NO"


def test_reader_guide_has_nonclaim_framing_and_pointer() -> None:
    guide = _read(GUIDE_PATH)
    assert "This matrix does not claim a physics-complete ToE." in guide
    assert "formal/docs/release/SCORED_AUDIT_MATRIX_v1.json" in guide


def test_state_surface_points_to_scored_matrix_artifact() -> None:
    state = _read(STATE_PATH)
    assert "formal/docs/release/SCORED_AUDIT_MATRIX_v1.json" in state
