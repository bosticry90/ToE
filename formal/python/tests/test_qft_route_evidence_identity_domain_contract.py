from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from formal.python.tools import qft_route_evidence_identity as subject
from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection as route_v0,
)


EM_PATH = "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
SCALAR_REVIEW_PATH = (
    "formal/docs/release/"
    "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_"
    "RESULT_REVIEW_20260618_v0.json"
)


def _write_contract(path: Path, contract: dict) -> None:
    path.write_bytes(subject.canonical_json_bytes(contract))


def test_contract_declares_exactly_nine_typed_current_identities() -> None:
    contract = subject.load_contract()
    identities = contract["identities"]
    assert [entry["path"] for entry in identities] == [
        artifact["path"] for artifact in route_v0.ROUTE_EVIDENCE_ARTIFACTS
    ]
    domains = [entry["current_identity"]["domain"] for entry in identities]
    assert domains.count(subject.FROZEN_GIT_BLOB_SHA256) == 8
    assert domains.count(subject.CANONICAL_ARTIFACT_SHA256) == 1
    assert contract["scientific_posture"] == "B-BLOCKED"
    assert contract["scientific_content_changed"] is False
    assert contract["registry_rotated"] is False
    assert contract["v2_enrollment_authorized"] is False


def test_historical_v0_v1_pins_remain_exactly_preserved() -> None:
    contract = subject.load_contract()
    historical_by_path = {
        entry["path"]: entry["historical_identity"]["sha256"]
        for entry in contract["identities"]
    }
    assert historical_by_path == route_v0.ROUTE_EVIDENCE_SHA_BY_PATH


def test_all_current_identities_resolve_in_their_declared_domains() -> None:
    resolved = subject.verify_route_evidence(
        [artifact["path"] for artifact in route_v0.ROUTE_EVIDENCE_ARTIFACTS]
    )
    assert len(resolved) == 9
    assert {entry["domain"] for entry in resolved} == {
        subject.FROZEN_GIT_BLOB_SHA256,
        subject.CANONICAL_ARTIFACT_SHA256,
    }


def test_em_rebinding_uses_the_provenance_verified_frozen_blob() -> None:
    contract = subject.load_contract()
    em = next(entry for entry in contract["identities"] if entry["path"] == EM_PATH)
    assert em["historical_identity"]["sha256"] == (
        "7b1c0bdd683e5d5891a77cf27772df239967ca210b3a7c9fd88ba75f7a1e85e9"
    )
    assert em["current_identity"] == {
        "domain": subject.FROZEN_GIT_BLOB_SHA256,
        "git_blob_oid": "c255a820200746ea428e1db8f91f7e5e059ff1e7",
        "sha256": "0a977bd478e39141cc7d198b706bad46f9e468305fa7586c2ea410b3c742d63c",
    }


def test_scalar_review_uses_canonical_artifact_identity() -> None:
    contract = subject.load_contract()
    scalar = next(
        entry
        for entry in contract["identities"]
        if entry["path"] == SCALAR_REVIEW_PATH
    )
    assert scalar["current_identity"]["domain"] == (
        subject.CANONICAL_ARTIFACT_SHA256
    )
    raw = (subject.REPO_ROOT / SCALAR_REVIEW_PATH).read_bytes()
    assert raw == subject.canonical_json_bytes(json.loads(raw))
    assert subject.sha256_bytes(raw) == scalar["current_identity"]["sha256"]


def test_contract_rejects_a_rebound_historical_pin(
    tmp_path: Path,
) -> None:
    contract = copy.deepcopy(subject.load_contract())
    contract["identities"][0]["historical_identity"]["sha256"] = "0" * 64
    contract_path = tmp_path / "contract.json"
    _write_contract(contract_path, contract)
    with pytest.raises(
        subject.IdentityContractError,
        match="does not preserve.*historical pins",
    ):
        subject.verify_route_evidence(
            [artifact["path"] for artifact in route_v0.ROUTE_EVIDENCE_ARTIFACTS],
            expected_historical_sha_by_path=route_v0.ROUTE_EVIDENCE_SHA_BY_PATH,
            contract_path=contract_path,
        )


def test_contract_rejects_an_unknown_identity_domain(tmp_path: Path) -> None:
    contract = copy.deepcopy(subject.load_contract())
    contract["identities"][0]["current_identity"]["domain"] = "CHECKOUT_BYTES"
    contract_path = tmp_path / "contract.json"
    _write_contract(contract_path, contract)
    with pytest.raises(subject.IdentityContractError, match="identity domain"):
        subject.load_contract(contract_path)


def test_consumer_path_set_is_fail_closed() -> None:
    paths = [artifact["path"] for artifact in route_v0.ROUTE_EVIDENCE_ARTIFACTS]
    with pytest.raises(
        subject.IdentityContractError,
        match="consumer route-evidence paths",
    ):
        subject.verify_route_evidence(paths[:-1])
