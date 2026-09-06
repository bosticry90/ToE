from __future__ import annotations

import copy
import json
import subprocess
from collections import Counter
from pathlib import Path

import pytest

from formal.python.tools import historical_artifact_currency_identity as identity


def test_all_seventeen_bindings_are_explicitly_role_typed() -> None:
    contract = identity.load_contract()
    bindings = contract["bindings"]
    assert len(bindings) == contract["binding_count"] == 17
    assert [row["binding_id"] for row in bindings] == [
        f"PAC-{index:03d}" for index in range(1, 18)
    ]
    assert Counter(row["role"] for row in bindings) == {
        identity.HISTORICAL_SOURCE_BLOB: 1,
        identity.HISTORICAL_GENERATOR_PIN: 15,
        identity.REVIEW_TIME_AUTHORITY: 1,
    }
    assert Counter(row["current_successor_role"] for row in bindings) == {
        identity.CURRENT_CANONICAL_IDENTITY: 16,
        identity.CURRENT_LIVE_AUTHORITY: 1,
    }


def test_historical_registry_and_generator_resolve_from_frozen_git_blobs() -> None:
    registry = identity.verify_binding("PAC-001")
    generator = identity.verify_binding("PAC-002")
    assert registry["role"] == identity.HISTORICAL_SOURCE_BLOB
    assert registry["git_blob_oid"] == "e6c5b3773dccd92fde9c0a8d486a56f993d6b235"
    assert registry["sha256"] == (
        "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
    )
    assert generator["role"] == identity.HISTORICAL_GENERATOR_PIN
    assert generator["git_blob_oid"] == "2edf61181178c8629980e51b52f61aaaef628b1a"
    assert generator["sha256"] == (
        "27ad363691f34279e5a9e0d0ffc916096af0f21ca189c284ff7ad005927c730c"
    )


def test_historical_compendium_pin_and_current_identity_are_separate() -> None:
    resolved = identity.verify_binding("PAC-007")
    assert resolved["role"] == identity.HISTORICAL_GENERATOR_PIN
    assert resolved["sha256"] == (
        "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e"
    )
    current = resolved["current_canonical_identity"]
    assert current["domain"] == "FROZEN_GIT_BLOB_SHA256"
    assert current["git_blob_oid"] == "ccd41b23e28ee01cc23c41821d0f4dde5ccb13fb"
    assert current["sha256"] == (
        "3e4f82424d294289a44fa400b82e31654c9e3614d5551a5c5a0c72526352a9ae"
    )


def test_lf_and_crlf_compendium_copies_resolve_to_the_historical_pin(
    tmp_path: Path,
) -> None:
    relative = (
        "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
    )
    canonical = subprocess.run(
        ["git", "show", f"HEAD:{relative}"],
        cwd=identity.REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout
    expected = "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e"
    lf_path = tmp_path / "lf.md"
    crlf_path = tmp_path / "crlf.md"
    lf_path.write_bytes(canonical)
    crlf_path.write_bytes(canonical.replace(b"\n", b"\r\n"))
    assert (
        identity.historical_compendium_sha256_for_path(
            lf_path, expected_historical_sha256=expected
        )
        == expected
    )
    assert (
        identity.historical_compendium_sha256_for_path(
            crlf_path, expected_historical_sha256=expected
        )
        == expected
    )
    crlf_path.write_bytes(crlf_path.read_bytes() + b"tamper")
    assert (
        identity.historical_compendium_sha256_for_path(
            crlf_path, expected_historical_sha256=expected
        )
        != expected
    )


def test_review_time_authority_is_verified_without_live_equality() -> None:
    resolved = identity.verify_binding("PAC-017")
    assert resolved["role"] == identity.REVIEW_TIME_AUTHORITY
    assert resolved["current_successor_role"] == identity.CURRENT_LIVE_AUTHORITY
    assert resolved["equality_with_current_live_authority_required"] is False
    assert resolved["sha256"] == (
        "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b"
    )
    assert resolved["current_live_authority_sha256"] != resolved["sha256"]


def test_contract_identity_tamper_fails_closed(tmp_path: Path) -> None:
    contract = copy.deepcopy(identity.load_contract())
    contract["identities"]["registry_post_repair"]["sha256"] = "0" * 64
    path = tmp_path / "tampered-contract.json"
    path.write_bytes(identity.canonical_json_bytes(contract))
    with pytest.raises(
        identity.HistoricalArtifactIdentityError,
        match="frozen Git blob SHA-256 mismatch",
    ):
        identity.verify_binding("PAC-001", contract_path=path)


def test_contract_is_canonical_and_preserves_nonclaim_boundaries() -> None:
    raw = identity.CONTRACT_PATH.read_bytes()
    payload = json.loads(raw)
    assert raw == identity.canonical_json_bytes(payload)
    assert payload["registry_rotated"] is False
    assert payload["scientific_content_changed"] is False
    assert payload["scientific_posture"] == "B-BLOCKED"
    assert payload["v2_enrollment_authorized"] is False
