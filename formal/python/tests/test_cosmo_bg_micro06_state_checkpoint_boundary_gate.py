from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
)
COSMO_MICRO06_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_06_STATE_CHECKPOINT_BOUNDARY_v0.md"
)
COSMO_MICRO06_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _cosmo_rollup_checkpoint_section(text: str) -> str:
    start_marker = "COSMO rollup checkpoint (2026-03-01):"
    end_marker = "COSMO_ROLLUP_STATE_CHECKPOINT_END_v0"

    start = text.find(start_marker)
    assert start >= 0, "Missing COSMO rollup checkpoint section marker in state."

    end = text.find(end_marker, start)
    assert end >= 0, "Missing COSMO rollup state-checkpoint end marker in state."

    return text[start : end + len(end_marker)]


def test_cosmo_micro06_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
    assert COSMO_MICRO06_PATH.exists(), "Missing COSMO background Cycle-006 micro document."
    assert COSMO_MICRO06_ARTIFACT_PATH.exists(), "Missing COSMO background Cycle-006 artifact payload."


def test_cosmo_target_references_micro06_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "TARGET-COSMO-BG-MICRO-06-STATE-CHECKPOINT-BOUNDARY-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_06_STATE_CHECKPOINT_BOUNDARY_v0.md",
        "formal/output/cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro06_state_checkpoint_boundary_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target is missing required micro-06 token(s): " + ", ".join(missing)


def test_cosmo_micro06_doc_contains_required_tokens() -> None:
    text = _read(COSMO_MICRO06_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_06_STATE_CHECKPOINT_BOUNDARY_v0",
        "TARGET-COSMO-BG-MICRO-06-STATE-CHECKPOINT-BOUNDARY-v0",
        "COSMO_BG_MICRO06_STATE_CHECKPOINT_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO06_SCOPE_BOUNDARY_v0: COSMO_ROLLUP_STATE_CHECKPOINT_SECTION_ONLY_NONCLAIM",
        "COSMO_BG_MICRO06_PROGRESS_v0: STATE_CHECKPOINT_BOUNDARY_TOKEN_PINNED",
        "COSMO_BG_MICRO06_STATE_CHECKPOINT_ARTIFACT_v0: cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0",
        "COSMO_ROLLUP_STATE_CHECKPOINT_BOUNDARY_v0: SECTION_ISOLATED",
        "COSMO_ROLLUP_STATE_CHECKPOINT_END_v0",
        "formal/output/cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0.json",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO micro-06 document is missing required token(s): " + ", ".join(missing)


def test_cosmo_rollup_state_checkpoint_section_is_isolated() -> None:
    state_text = _read(STATE_PATH)
    section = _cosmo_rollup_checkpoint_section(state_text)

    required_section_tokens = [
        "formal/docs/paper/TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md",
        "formal/markdown/locks/policy/COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md",
        "COSMO_BACKGROUND_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "COSMO_BACKGROUND_PILLAR_PACKAGE_PROGRESS_v0: REQUIRED_CONTENTS_PINNED",
        "COSMO_BACKGROUND_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "REOPEN_TRIGGER_COSMO_SURFACE_DRIFT_v0",
        "REOPEN_TRIGGER_COSMO_SCOPE_BOUNDARY_REGRESSION_v0",
        "REOPEN_TRIGGER_COSMO_PACKAGE_CONTENT_MISMATCH_v0",
        "formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py",
        "formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py",
        "COSMO_ROLLUP_STATE_CHECKPOINT_BOUNDARY_v0: SECTION_ISOLATED",
        "COSMO_ROLLUP_STATE_CHECKPOINT_END_v0",
    ]
    missing = [token for token in required_section_tokens if token not in section]
    assert not missing, "COSMO state checkpoint section missing required token(s): " + ", ".join(missing)

    forbidden_prefixes = ["QFT_", "GR01_", "SR_FULL_DERIVATION_ENFORCEMENT_ADJUDICATION"]
    leaked = [prefix for prefix in forbidden_prefixes if prefix in section]
    assert not leaked, "COSMO state checkpoint section contains out-of-scope token prefix(es): " + ", ".join(leaked)


def test_cosmo_micro06_artifact_schema_and_token_alignment() -> None:
    payload = _read_json(COSMO_MICRO06_ARTIFACT_PATH)

    assert payload.get("artifact_id") == "cosmo_bg_micro06_state_checkpoint_boundary_cycle01_v0"
    assert payload.get("artifact_version") == "v0"
    assert payload.get("placeholder_template") is True

    body = payload.get("payload")
    assert isinstance(body, dict), "Artifact payload block must be an object."
    assert body.get("checkpoint") == "cosmo_bg_micro06_state_checkpoint_boundary_cycle01"
    assert body.get("status") == "placeholder_non_promotional"
    assert body.get("scope") == "cosmo_rollup_state_checkpoint_section_only_nonclaim_v0"

    boundary_tokens = body.get("boundary_tokens")
    assert isinstance(boundary_tokens, list) and len(boundary_tokens) == 2, (
        "COSMO micro-06 artifact must include exactly two boundary_tokens rows."
    )
    for token in [
        "COSMO_ROLLUP_STATE_CHECKPOINT_BOUNDARY_v0: SECTION_ISOLATED",
        "COSMO_ROLLUP_STATE_CHECKPOINT_END_v0",
    ]:
        assert token in boundary_tokens

    required_contents = body.get("required_cosmo_checkpoint_contents")
    assert isinstance(required_contents, list) and len(required_contents) == 7, (
        "COSMO micro-06 artifact must include exactly seven required_cosmo_checkpoint_contents rows."
    )
