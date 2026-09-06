import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal" / "docs" / "release"
AUTHORITY = RELEASE / (
    "TOE_GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION_"
    "STAGE_3_OPEN_AUTHORITY_v0.json"
)
REVIEW = RELEASE / (
    "TOE_GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION_"
    "STAGE_3_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_authority_binds_exact_stage_three_scope_and_rows() -> None:
    authority = _read(AUTHORITY)
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "af28fab6b424603cccbc2e7ef8663d8f8a1e88212285c1767a59f0cfccef9ebb"
        ),
        "canonical_target": (
            "reconstruct_toe_gravitational_requirement_and_action_family_lineages_v0"
        ),
        "semantic_stage_id": (
            "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION"
        ),
        "stage_number": 3,
    }
    assert len(authority["family_ids"]) == 7
    assert len(set(authority["family_ids"])) == 7
    assert len(authority["requirement_ids"]) == 10
    assert len(set(authority["requirement_ids"])) == 10


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY)
    for row in authority["evidence_bindings"]:
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row[
            "sha256"
        ]


def test_authority_preserves_lineage_only_boundary() -> None:
    authority = _read(AUTHORITY)
    permitted = "\n".join(authority["permitted_work"])
    prohibited = "\n".join(authority["prohibited_work"])
    assert "exact preserved sources" in permitted
    assert "documentary finding without promotion" in permitted
    assert "invent an action" in prohibited
    assert "judge compatibility" in prohibited
    assert "open Stage 4 automatically" in prohibited


def test_independent_review_accepts_authority_without_science() -> None:
    review = _read(REVIEW)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["stage_3_scientific_result_created"] is False
    assert review["stage_4_authorized"] is False
