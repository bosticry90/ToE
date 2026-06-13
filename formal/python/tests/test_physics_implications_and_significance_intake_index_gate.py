from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.physics_implications_and_significance_intake_index_report import (
    CATEGORIES,
CURRENT_LIVE_NEXT_TARGET,
    DEFAULT_INDEX_PATH,
    DEFAULT_OUT,
    INDEX_ID,
    LEDGER_TARGET,
    NONCLAIM_FLAGS,
    OUTCOME_ID,
    ROWS,
    SCHEMA_ID,
    SOURCE_ATTACHMENT,
    build_physics_implications_and_significance_intake_index_packet,
)

POST_MR_LIVE_TARGET = (
    "execute_qft_gr_minimal_working_model_refinement_attempt_after_post_retest_refinement_conservation_retest"
)


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

REQUIRED_CEILING_KEYS = {
    "validates_toe",
    "closes_seams",
    "promotes_master_action",
    "authorizes_release_assembly",
    "authorizes_public_submission",
    "discharges_theorems",
    "claims_empirical_validation",
    "mutates_live_target",
}

REQUIRED_ROW_TOKENS = [
    "NONCLAIM",
    "NO_THEOREM_DISCHARGE",
    "NO_SEAM_CLOSURE",
    "NO_EMPIRICAL_VALIDATION",
    "NO_MASTER_ACTION_PROMOTION",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _git_cached_names(path: str) -> list[str]:
    completed = subprocess.run(
        ["git", "diff", "--cached", "--name-only", "--", path],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    return [line for line in completed.stdout.splitlines() if line]


def test_physics_implications_intake_index_files_exist() -> None:
    assert DEFAULT_INDEX_PATH.exists()
    assert DEFAULT_OUT.exists()


def test_physics_implications_intake_packet_schema_and_identity() -> None:
    payload = _json(DEFAULT_OUT)
    assert payload["schema_id"] == SCHEMA_ID
    assert payload["index_id"] == INDEX_ID
    assert payload["source_attachment"] == SOURCE_ATTACHMENT
    assert payload["claim_status"] == "NONCLAIM"
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["prepared_target"] == (
        "prepare_physics_implications_and_significance_intake_index_packet"
    )
    assert payload["not_a_source_verification_ledger"] is True
    assert payload["source_verification_deferred_to"] == LEDGER_TARGET


def test_physics_implications_intake_categories_and_rows_are_nonclaim() -> None:
    payload = _json(DEFAULT_OUT)
    markdown = _read(DEFAULT_INDEX_PATH)
    expected_ids = [row["intake_id"] for row in ROWS]

    assert payload["categories"] == CATEGORIES
    assert payload["intake_row_count"] == len(ROWS)
    assert payload["intake_ids"] == expected_ids
    assert set(payload["nonclaim_flags"]) == set(NONCLAIM_FLAGS)

    for category in CATEGORIES:
        assert category in markdown

    for row in payload["intake_rows"]:
        assert row["intake_id"] in markdown
        assert row["claim_status"] == "NONCLAIM"
        assert row["source_verification_status"] == (
            "UNLEDGERED_INTAKE_PENDING_SOURCE_VERIFICATION_LEDGER"
        )
        for token in REQUIRED_ROW_TOKENS:
            assert token in markdown
        assert set(row["not_authorized"]) == {
            "NO_THEOREM_DISCHARGE",
            "NO_SEAM_CLOSURE",
            "NO_EMPIRICAL_VALIDATION",
            "NO_MASTER_ACTION_PROMOTION",
        }


def test_physics_implications_intake_ceiling_and_live_target_controls() -> None:
    payload = _json(DEFAULT_OUT)
    registry = _json(REGISTRY_PATH)
    markdown = _read(DEFAULT_INDEX_PATH)

    assert payload["live_target_mutation_allowed"] is False
    assert payload["not_live_target_mutation"] is True
    assert payload["current_live_next_target_before_intake"] == CURRENT_LIVE_NEXT_TARGET
    assert payload["current_live_next_target_after_intake"] == CURRENT_LIVE_NEXT_TARGET
    assert (
        payload["current_live_next_target_unchanged_assertion"]
        == "CURRENT_LIVE_NEXT_TARGET_v0 remains unchanged by this supplemental intake packet."
    )
    assert registry["current_target_state"]["live_next_target"] in {
        CURRENT_LIVE_NEXT_TARGET,
        POST_MR_LIVE_TARGET,
    }
    assert f"CURRENT_LIVE_NEXT_TARGET_v0: {CURRENT_LIVE_NEXT_TARGET}" in markdown
    assert "live_target_mutation_allowed = false" in markdown

    ceilings = payload["ceiling_statements"]
    assert set(ceilings) == REQUIRED_CEILING_KEYS
    for flag_value in ceilings.values():
        assert flag_value is False


def test_physics_implications_intake_does_not_mutate_authoritative_live_surfaces() -> None:
    expected = f"CURRENT_LIVE_NEXT_TARGET_v0: {CURRENT_LIVE_NEXT_TARGET}"
    post_mr_expected = f"CURRENT_LIVE_NEXT_TARGET_v0: {POST_MR_LIVE_TARGET}"
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, SURFACES_PATH]:
        text = _read(path)
        assert expected in text or post_mr_expected in text


def test_physics_implications_intake_packet_is_deterministic() -> None:
    payload = _json(DEFAULT_OUT)
    generated = build_physics_implications_and_significance_intake_index_packet(
        current_live_next_target=CURRENT_LIVE_NEXT_TARGET
    )
    assert payload == generated
    for key, value in payload["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_physics_implications_raw_attachment_is_not_staged() -> None:
    assert _git_cached_names(SOURCE_ATTACHMENT) == []
