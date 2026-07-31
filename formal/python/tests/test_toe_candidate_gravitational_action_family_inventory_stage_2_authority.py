import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal" / "docs" / "release"
AUTHORITY = RELEASE / (
    "TOE_CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY_"
    "STAGE_2_OPEN_AUTHORITY_v0.json"
)
REVIEW = RELEASE / (
    "TOE_CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY_"
    "STAGE_2_OPEN_AUTHORITY_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_authority_binds_exact_stage_two_scope_and_families() -> None:
    authority = _read(AUTHORITY)
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": (
            "8dc24a87cd882d67123278bc2da416a4efffe29866f96bbecc4dd7af7a7942ea"
        ),
        "canonical_target": "inventory_toe_candidate_gravitational_action_families_v0",
        "semantic_stage_id": "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY",
        "stage_number": 2,
    }
    assert authority["family_ids"] == [
        "F_EH",
        "F_FR",
        "F_QUADRATIC",
        "F_EXTRA_FIELD",
        "F_NONLOCAL",
        "F_CONNECTION_TORSION",
        "F_EQUIVALENCE_PROBE",
    ]


def test_authority_source_hashes_reproduce() -> None:
    authority = _read(AUTHORITY)
    for row in authority["evidence_bindings"]:
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]


def test_authority_prohibits_selection_calculation_and_stage_three() -> None:
    authority = _read(AUTHORITY)
    prohibited = "\n".join(authority["prohibited_work"])
    assert "select a winning" in prohibited
    assert "compatibility" in prohibited
    assert "new hyperbolicity" in prohibited
    assert "open Stage 3 automatically" in prohibited


def test_independent_review_accepts_authority_without_science() -> None:
    review = _read(REVIEW)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["stage_2_scientific_result_created"] is False
    assert review["stage_3_authorized"] is False
