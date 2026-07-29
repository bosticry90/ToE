from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from formal.python.tools.bounded_program_governance import (
    BoundedProgramError,
    ORDERED_ARRAY_FIELDS,
    QUADRATIC_MANDATORY_EXIT,
    QUADRATIC_PROGRAM_ID,
    QUADRATIC_STAGE_DEFINITIONS,
    REGISTRY_EXTENSION_KEY,
    SET_LIKE_ARRAY_FIELDS,
    close_attempt,
    governance_contract,
    install_registry_extension,
    jcs_bytes,
    normalize_scope,
    open_attempt,
    scope_hash,
    sha256_bytes,
    strict_json_loads,
    validate_event_chain,
    validate_registry_extension,
    write_event,
)

REPO_ROOT = Path(__file__).resolve().parents[3]


def _base_registry() -> dict[str, object]:
    return {
        "schema_id": "LOOP_CONTROL_REGISTRY_v0",
        "schema_version": 0,
        "current_target": (
            "prepare_qft_gr_quadratic_generic_background_linearization_"
            "gauge_and_jet_contract_v0"
        ),
    }


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def test_strict_json_rejects_duplicate_properties_and_nonfinite_numbers() -> None:
    with pytest.raises(BoundedProgramError, match="duplicate JSON property"):
        strict_json_loads('{"same":1,"same":2}')
    with pytest.raises(BoundedProgramError, match="non-I-JSON"):
        strict_json_loads('{"value":NaN}')


def test_jcs_preserves_array_order_and_sorts_object_keys_by_utf16() -> None:
    payload = {"😀": 3, "€": 2, "\r": 1, "ordered": ["b", "a"]}
    encoded = jcs_bytes(payload)
    assert encoded == (
        '{"\\r":1,"ordered":["b","a"],"€":2,"😀":3}'.encode("utf-8")
    )


def test_jcs_rejects_floats_unsafe_integers_and_lone_surrogates() -> None:
    with pytest.raises(BoundedProgramError, match="floating JSON numbers"):
        jcs_bytes({"value": 1.25})
    with pytest.raises(BoundedProgramError, match="exactly representable"):
        jcs_bytes({"value": 1 << 60})
    with pytest.raises(BoundedProgramError, match="invalid Unicode"):
        jcs_bytes({"value": "\ud800"})


def test_scope_preprocessing_sorts_only_declared_semantic_sets() -> None:
    stage = dict(QUADRATIC_STAGE_DEFINITIONS[0])
    scope = {
        key: stage[key]
        for key in (
            "semantic_stage_id",
            "normalized_scientific_question",
            *SET_LIKE_ARRAY_FIELDS,
        )
    }
    reversed_scope = json.loads(json.dumps(scope))
    for key in SET_LIKE_ARRAY_FIELDS:
        reversed_scope[key] = list(reversed(reversed_scope[key]))
    assert normalize_scope(scope) == normalize_scope(reversed_scope)
    assert scope_hash(scope) == scope_hash(reversed_scope)
    assert ORDERED_ARRAY_FIELDS == (
        "rewrite_precedence",
        "substitution_order",
        "variable_ordering",
        "dependency_execution_sequence",
        "Jordan_chain_member_order",
    )


def test_scope_preprocessing_rejects_semantic_duplicates() -> None:
    stage = dict(QUADRATIC_STAGE_DEFINITIONS[0])
    scope = {
        key: json.loads(json.dumps(stage[key]))
        for key in (
            "semantic_stage_id",
            "normalized_scientific_question",
            *SET_LIKE_ARRAY_FIELDS,
        )
    }
    scope["authorized_inputs"].append(scope["authorized_inputs"][0])
    with pytest.raises(BoundedProgramError, match="duplicate semantic"):
        normalize_scope(scope)


def test_installation_preserves_target_and_installs_unopened_quadratic_program() -> None:
    original = _base_registry()
    migrated = install_registry_extension(original)
    assert migrated["current_target"] == original["current_target"]
    assert migrated["schema_version"] == 1
    assert migrated[REGISTRY_EXTENSION_KEY] == governance_contract()
    program = migrated["bounded_programs_v1"][QUADRATIC_PROGRAM_ID]
    assert program["authorized_stage_count"] == 5
    assert program["attempted_stage_ids"] == []
    assert program["repair_attempt_count"] == 0
    assert program["mandatory_exit_target"] == QUADRATIC_MANDATORY_EXIT
    assert program["state"] == "UNOPENED"
    validate_registry_extension(migrated)


def test_open_close_chain_is_immutable_and_contiguous(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import formal.python.tools.bounded_program_governance as governance

    monkeypatch.setattr(governance, "REPO_ROOT", tmp_path)
    registry = install_registry_extension(_base_registry())
    registry_bytes = json.dumps(registry, sort_keys=True).encode()
    parent = "a" * 40
    stage = QUADRATIC_STAGE_DEFINITIONS[0]
    opened, open_path, open_event = open_attempt(
        registry,
        registry_bytes=registry_bytes,
        program_id=QUADRATIC_PROGRAM_ID,
        semantic_stage_id=stage["semantic_stage_id"],
        target=stage["target"],
        opened_from_commit=parent,
    )
    write_event(tmp_path / open_path, open_event)

    result_path = "formal/docs/release/result.json"
    review_path = "formal/docs/release/review.json"
    _write_json(tmp_path / result_path, {"result": "complete"})
    _write_json(tmp_path / review_path, {"review": "accepted"})
    closed, close_path, close_event = close_attempt(
        opened,
        program_id=QUADRATIC_PROGRAM_ID,
        result_artifact_path=result_path,
        review_artifact_path=review_path,
        terminal_result="PASSED",
        closed_from_commit="b" * 40,
    )
    write_event(tmp_path / close_path, close_event)
    validate_event_chain(closed, repo_root=tmp_path)

    program = closed["bounded_programs_v1"][QUADRATIC_PROGRAM_ID]
    assert program["state"] == "CLOSED"
    assert program["last_closed_attempt_number"] == 1
    assert [row["event_type"] for row in program["events"]] == [
        "ATTEMPT_OPEN",
        "ATTEMPT_CLOSE",
    ]
    assert close_event["previous_event_hash"] == open_event["event_hash"]
    assert close_event["open_event_hash"] == open_event["event_hash"]

    with pytest.raises(BoundedProgramError, match="immutable event already exists"):
        write_event(tmp_path / open_path, open_event)


def test_blocked_stage_cannot_be_reopened(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import formal.python.tools.bounded_program_governance as governance

    monkeypatch.setattr(governance, "REPO_ROOT", tmp_path)
    registry = install_registry_extension(_base_registry())
    stage = QUADRATIC_STAGE_DEFINITIONS[0]
    opened, open_path, open_event = open_attempt(
        registry,
        registry_bytes=b"registry",
        program_id=QUADRATIC_PROGRAM_ID,
        semantic_stage_id=stage["semantic_stage_id"],
        target=stage["target"],
        opened_from_commit="a" * 40,
    )
    write_event(tmp_path / open_path, open_event)
    result_path = "formal/docs/release/result.json"
    review_path = "formal/docs/release/review.json"
    _write_json(tmp_path / result_path, {"result": "blocked"})
    _write_json(tmp_path / review_path, {"review": "accepted blocked result"})
    closed, close_path, close_event = close_attempt(
        opened,
        program_id=QUADRATIC_PROGRAM_ID,
        result_artifact_path=result_path,
        review_artifact_path=review_path,
        terminal_result="BLOCKED",
        closed_from_commit="b" * 40,
    )
    write_event(tmp_path / close_path, close_event)
    with pytest.raises(BoundedProgramError, match="mandatory exit"):
        open_attempt(
            closed,
            registry_bytes=b"registry",
            program_id=QUADRATIC_PROGRAM_ID,
            semantic_stage_id=stage["semantic_stage_id"],
            target=stage["target"],
            opened_from_commit="c" * 40,
        )


def test_fixed_scope_hash_is_stable() -> None:
    stage = QUADRATIC_STAGE_DEFINITIONS[0]
    scope = {
        key: stage[key]
        for key in (
            "semantic_stage_id",
            "normalized_scientific_question",
            *SET_LIKE_ARRAY_FIELDS,
        )
    }
    digest = scope_hash(scope)
    assert digest == hashlib.sha256(jcs_bytes(normalize_scope(scope))).hexdigest()
    assert len(digest) == 64


def test_installed_governance_artifacts_preserve_scientific_authority() -> None:
    installation = strict_json_loads(
        (
            REPO_ROOT
            / "formal"
            / "docs"
            / "release"
            / "BOUNDED_PROGRAM_GOVERNANCE_CONTROL_INSTALLATION_20260729_v0.json"
        ).read_text(encoding="utf-8")
    )
    review = strict_json_loads(
        (
            REPO_ROOT
            / "formal"
            / "docs"
            / "release"
            / "BOUNDED_PROGRAM_GOVERNANCE_CONTROL_INSTALLATION_RESULT_REVIEW_20260729_v0.json"
        ).read_text(encoding="utf-8")
    )
    target = (
        "prepare_qft_gr_quadratic_generic_background_linearization_"
        "gauge_and_jet_contract_v0"
    )
    assert installation["current_scientific_target_preserved"] == target
    assert review["next_scientific_target"] == target
    assert review["findings"]["scientific_stage_attempted"] is False
    assert review["findings"]["native_program_authorized"] is False
