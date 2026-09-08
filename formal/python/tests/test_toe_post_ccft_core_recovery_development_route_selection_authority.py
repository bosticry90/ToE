from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_POST_CCFT_CORE_RECOVERY_DEVELOPMENT_ROUTE_SELECTION_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_POST_CCFT_CORE_RECOVERY_DEVELOPMENT_ROUTE_SELECTION_AUTHORITY_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
TARGET = "select_post_ccft_core_recovery_development_route_v0"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_is_bound_to_terminal_ccft_closeout() -> None:
    value = read(AUTHORITY)
    assert value["parent_head"] == "40a7d472029fb556ac80eee74d9bde13afb23692"
    assert value["consumed_target"].startswith("close_toe_ccft_native_mathematical_core")
    assert value["authorized_target"] == TARGET
    assert value["authorization_status"] == "AUTHORIZED_NOT_EXECUTED"


def test_exactly_three_nonexecuting_routes_are_frozen() -> None:
    value = read(AUTHORITY)
    assert value["authorized_routes"] == [
        "SELECT_ONE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY",
        "SELECT_BOUNDED_CCFT_V0_THEORY_CONSTRUCTION",
        "DEFER_CCFT_DEVELOPMENT",
    ]
    assert value["frozen_route_requirements"]["targeted_recovery"]["one_pass_only"] is True
    assert value["frozen_route_requirements"]["targeted_recovery"]["automatic_second_search_prohibited"] is True


def test_authority_does_not_prepare_or_execute_science() -> None:
    prohibited = set(read(AUTHORITY)["prohibited_actions"])
    assert "TRAVERSE_OR_PARSE_UNREVIEWED_ARCHIVE_CONTENT" in prohibited
    assert "INSERT_A_NEW_CCFT_POSTULATE" in prohibited
    assert "CONSTRUCT_OR_EXECUTE_A_CCFT_MODEL" in prohibited
    assert "PREPARE_INSTALL_OR_OPEN_A_TARGETED_RECOVERY_OR_CCFT_V0_PROGRAM" in prohibited


def test_independent_review_accepts_every_check() -> None:
    review = read(REVIEW)
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True
    assert review["failed_checks"] == []
    assert all(review["checks"].values())


def test_registry_preserves_completed_route_selection_authority() -> None:
    registry = read(REGISTRY)
    rows = [row for row in registry["workstreams"] if row.get("workstream_id") == TARGET]
    assert len(rows) == 1
    assert rows[0]["status"] == "completed"
    assert registry["bounded_programs_v1"]["TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0"]["mandatory_exit_completed"] is True
