from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_STAGE_2_OPEN_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_STAGE_2_OPEN_AUTHORITY_REVIEW_v0.json"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_manifest_stage_two() -> None:
    authority = read(AUTHORITY)
    stage = read(MANIFEST)["stages"][1]
    assert authority["authorized_stage"]["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert authority["authorized_stage"]["canonical_target"] == stage["canonical_target"]
    assert authority["canonical_terminal_outcomes"] == stage["mandatory_terminal_outcomes"]


def test_cp_nlse_route_is_selected_but_equation_is_not() -> None:
    authority = read(AUTHORITY)
    assert authority["selected_stage_1_route"]["branch"] == "CP_NLSE"
    assert authority["selected_stage_1_route"]["governing_equation_selected"] is False
    assert authority["scientific_output_at_authority"]["governing_equation"] == "UNSELECTED"
    assert authority["scientific_output_at_authority"]["new_postulates"] == 0
    assert authority["scientific_output_at_authority"]["ccft_v0_model"] == "NONE"


def test_new_postulates_are_bounded_and_require_provenance() -> None:
    authority = read(AUTHORITY)
    assert authority["scientific_limits"]["maximum_new_ccft_postulates"] == 8
    assert authority["scientific_limits"]["maximum_frozen_models"] == 1
    assert authority["provenance_vocabulary"] == [
        "SOURCE_RECOVERED",
        "KNOWN_PHYSICS_BASELINE",
        "NEW_CCFT_POSTULATE",
        "NUMERICAL_CONVENTION",
        "MATHEMATICAL_CONTROL",
    ]
    assert authority["scientific_limits"]["unlabeled_assumption_insertion_authorized"] is False


def test_director_outcomes_normalize_deterministically() -> None:
    normalization = read(AUTHORITY)["director_wording_normalization"]
    assert normalization["CCFT_V0_MODEL_CONTRACT_FROZEN_WITH_NEW_POSTULATES"]["canonical_outcome"] == "CCFT_V0_MODEL_CONTRACT_FROZEN"
    assert normalization["BLOCKED_BY_GOVERNING_EQUATION_CONFLICT"]["canonical_outcome"] == "SELECTED_ROUTE_CONTRADICTORY_OR_UNDERDEFINED"
    assert len(normalization["BLOCKED_BY_INCOMPLETE_MODEL_CONTRACT"]["canonical_precedence"]) == 3


def test_evidence_and_review_reproduce() -> None:
    authority = read(AUTHORITY)
    assert all(sha(ROOT / row["path"]) == row["sha256"] for row in authority["evidence_bindings"])
    review = read(REVIEW)
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["stage_3_authorized"] is False
