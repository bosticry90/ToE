from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_STAGE_1_OPEN_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_STAGE_1_OPEN_AUTHORITY_REVIEW_v0.json"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_canonical_stage_one() -> None:
    authority = read(AUTHORITY)
    stage = read(MANIFEST)["stages"][0]
    assert authority["authorized_stage"]["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert authority["authorized_stage"]["canonical_target"] == stage["canonical_target"]
    assert authority["canonical_terminal_outcomes"] == stage["mandatory_terminal_outcomes"]


def test_director_wording_normalizes_to_immutable_manifest() -> None:
    authority = read(AUTHORITY)
    assert authority["director_wording_normalization"] == {
        "RETAIN_TWO_SEPARATE_CANDIDATES_AND_BLOCK_SINGLE_MODEL_PROGRAM":
        "RETAIN_TWO_SEPARATE_CONSTRUCTION_CANDIDATES"
    }
    assert set(authority["blocking_outcomes"]) == {
        "RETAIN_TWO_SEPARATE_CONSTRUCTION_CANDIDATES",
        "NO_BRANCH_READY_WITHOUT_FOUNDATIONAL_POSTULATE",
    }


def test_authority_creates_no_scientific_result() -> None:
    authority = read(AUTHORITY)
    output = authority["scientific_output_at_authority"]
    assert output == {
        "branch_selected": "NONE",
        "model": "NONE",
        "new_postulates": 0,
        "primary_theorem": "NONE",
        "scientific_attempts": 0,
    }
    assert not any(
        authority["scientific_limits"][key]
        for key in (
            "equation_selection_or_repair_authorized",
            "new_postulate_authorized",
            "model_freeze_authorized",
            "theorem_packet_or_execution_authorized",
            "stage_2_authorized",
        )
    )


def test_evidence_hashes_and_review_reproduce() -> None:
    authority = read(AUTHORITY)
    assert all(sha(ROOT / row["path"]) == row["sha256"] for row in authority["evidence_bindings"])
    review = read(REVIEW)
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["stage_2_authorized"] is False
