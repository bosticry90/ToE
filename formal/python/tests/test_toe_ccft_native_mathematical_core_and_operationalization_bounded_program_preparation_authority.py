from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY = RELEASE / "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
TARGET = "prepare_toe_ccft_native_mathematical_core_and_operationalization_bounded_program_v0"


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_is_exactly_proposal_preparation() -> None:
    value = _load(AUTHORITY)
    assert value["authority_decision"] == "AUTHORIZE_PROPOSAL_PREPARATION_ONLY"
    assert value["authorized_target"] == TARGET
    assert value["status"] == "PROGRAM_PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED"
    assert value["zero_scientific_execution"] is True


def test_frontier_selection_bindings_reproduce() -> None:
    checkpoint = _load(AUTHORITY)["consumed_frontier_checkpoint"]
    assert _sha256(REPO_ROOT / checkpoint["selection_result_path"]) == (
        checkpoint["selection_result_sha256"]
    )
    assert _sha256(REPO_ROOT / checkpoint["selection_review_path"]) == (
        checkpoint["selection_review_sha256"]
    )
    assert checkpoint["selected_frontier_readiness"] == "AFTER_ONE_PREREQUISITE"


def test_authority_prohibits_model_and_scientific_execution() -> None:
    prohibited = _load(AUTHORITY)["prohibited_work"]
    required = {
        "install the proposed CCFT program",
        "open any scientific stage",
        "recover or adjudicate CCFT mathematics",
        "select a coherence representation or field",
        "construct a CCFT action or evolution law",
        "couple CCFT to matter or gravity",
        "define a CCFT observable or discriminator",
        "promote archived or noncanonical evidence",
    }
    assert required <= set(prohibited)


def test_independent_review_accepts_only_preparation() -> None:
    value = _load(REVIEW)
    assert value["accepted"] is True
    assert value["scientific_execution_authorized"] is False
    assert value["failed_checks"] == []
    assert all(value["checks"].values())


def test_registry_retains_the_preparation_workstream() -> None:
    registry = _load(REGISTRY)
    rows = [row for row in registry["workstreams"] if row.get("workstream_id") == TARGET]
    assert len(rows) == 1
