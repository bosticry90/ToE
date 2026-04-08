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
DOC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle12_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_cycle12_candidate_doc_and_artifact_contract() -> None:
    doc_text = _read(DOC_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))

    assert "WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM" in doc_text
    assert "WS10_T20_QM_STAT_CYCLE12_LANE_v0: QM_STAT" in doc_text
    assert "WS10_T20_QM_STAT_CYCLE12_TARGET_v0: CYCLE12" in doc_text
    assert "formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json" in doc_text

    assert artifact["artifact_id"] == "qm_stat_class_b_seam_physics_pilot_cycle12_v0"
    assert artifact["status"] == "DECLARED_BOUNDED_NONCLAIM"
    assert artifact["lane"] == "QM_STAT"
    assert artifact["cycle_target"] == "CYCLE12"
    assert artifact["payload"]["non_claim_invariance"] is True
