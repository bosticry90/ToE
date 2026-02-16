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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
SR_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md"
)
SR_CYCLE1_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_object_scaffold_cycle1_v0.json"
)
SR_CYCLE2_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_contract_surface_cycle2_v0.json"
)
SR_CYCLE3_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "sr_covariance_lorentz_interval_placeholder_cycle3_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sr_cycle1_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-01-OBJECT-SCAFFOLD-v0",
        "SR_COVARIANCE_PROGRESS_v0: CYCLE1_OBJECT_SCAFFOLD_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE1_ARTIFACT_v0: sr_covariance_object_scaffold_cycle1_v0",
        "formal/output/sr_covariance_object_scaffold_cycle1_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR kickoff token in target: {token}"
        assert token in state_text, f"Missing SR kickoff token in state: {token}"


def test_sr_cycle2_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-02-CONTRACT-SURFACE-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE2_v0: CONTRACT_SURFACE_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE2_ARTIFACT_v0: sr_covariance_contract_surface_cycle2_v0",
        "formal/output/sr_covariance_contract_surface_cycle2_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-2 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-2 token in state: {token}"


def test_sr_cycle3_kickoff_tokens_are_pinned_in_target_and_state() -> None:
    target_text = _read(SR_TARGET_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        "TARGET-SR-COV-MICRO-03-LORENTZ-INTERVAL-PLACEHOLDER-v0",
        "SR_COVARIANCE_PROGRESS_CYCLE3_v0: LORENTZ_INTERVAL_PLACEHOLDER_TOKEN_PINNED",
        "SR_COVARIANCE_CYCLE3_ARTIFACT_v0: sr_covariance_lorentz_interval_placeholder_cycle3_v0",
        "formal/output/sr_covariance_lorentz_interval_placeholder_cycle3_v0.json",
    ]

    for token in required_tokens:
        assert token in target_text, f"Missing SR cycle-3 token in target: {token}"
        assert token in state_text, f"Missing SR cycle-3 token in state: {token}"


def test_sr_cycle1_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE1_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_object_scaffold_cycle1_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-001"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-01-OBJECT-SCAFFOLD-v0"
    assert payload.get("status") == "LOCKED_OBJECT_SCAFFOLD_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-1 artifact."
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_object_scaffold_cycle1_v0"


def test_sr_cycle2_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE2_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_contract_surface_cycle2_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-002"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-02-CONTRACT-SURFACE-v0"
    assert payload.get("status") == "LOCKED_CONTRACT_SURFACE_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-2 artifact."
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert determinism.get("content_fingerprint") == "sr_covariance_contract_surface_cycle2_v0"


def test_sr_cycle3_artifact_schema_and_scope_are_locked() -> None:
    payload = json.loads(_read(SR_CYCLE3_ARTIFACT_PATH))

    assert payload.get("artifact_id") == "sr_covariance_lorentz_interval_placeholder_cycle3_v0"
    assert payload.get("target_id") == "TARGET-SR-COV-PLAN"
    assert payload.get("pillar") == "PILLAR-SR"
    assert payload.get("cycle") == "CYCLE-003"
    assert payload.get("micro_target") == "TARGET-SR-COV-MICRO-03-LORENTZ-INTERVAL-PLACEHOLDER-v0"
    assert payload.get("status") == "LOCKED_LORENTZ_INTERVAL_PLACEHOLDER_PINNED"
    assert payload.get("scope") == "planning_only_non_claim_v0"

    witness_tokens = payload.get("witness_tokens")
    assert isinstance(witness_tokens, list) and witness_tokens, (
        "witness_tokens must be a non-empty list in SR cycle-3 artifact."
    )

    determinism = payload.get("determinism")
    assert isinstance(determinism, dict), "determinism block is required."
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"
    assert (
        determinism.get("content_fingerprint")
        == "sr_covariance_lorentz_interval_placeholder_cycle3_v0"
    )
