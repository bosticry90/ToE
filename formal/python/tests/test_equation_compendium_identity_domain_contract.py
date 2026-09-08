from __future__ import annotations

import copy
from pathlib import Path

import pytest

from formal.python.tools import equation_compendium_identity as subject
from formal.python.tools import pillar_seam_unit_mapping_ledger_reports as pillar
from formal.python.tools import scalar_multi_background_robustness_reports as scalar


COMPENDIUM_PATH = (
    "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
)
HISTORICAL_SHA256 = (
    "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e"
)
CURRENT_SHA256 = (
    "3e4f82424d294289a44fa400b82e31654c9e3614d5551a5c5a0c72526352a9ae"
)


def _write_contract(path: Path, contract: dict) -> None:
    path.write_bytes(subject.canonical_json_bytes(contract))


def test_contract_separates_historical_and_current_identity_domains() -> None:
    contract = subject.load_contract()
    identity = contract["identity"]
    assert contract["identity_count"] == 1
    assert identity["path"] == COMPENDIUM_PATH
    assert identity["historical_identity"] == {
        "bytes": 13743,
        "carriage_returns": 85,
        "domain": subject.HISTORICAL_MIXED_EOL_WORKING_TREE_SHA256,
        "line_feeds": 113,
        "sha256": HISTORICAL_SHA256,
    }
    assert identity["current_identity"] == {
        "bytes": 13658,
        "domain": subject.FROZEN_GIT_BLOB_SHA256,
        "git_blob_oid": "ccd41b23e28ee01cc23c41821d0f4dde5ccb13fb",
        "sha256": CURRENT_SHA256,
    }
    assert contract["scientific_posture"] == "B-BLOCKED"
    assert contract["scientific_content_changed"] is False
    assert contract["registry_rotated"] is False
    assert contract["v2_enrollment_authorized"] is False


def test_current_identity_resolves_from_the_frozen_git_blob() -> None:
    resolved = subject.verify_equation_compendium(
        expected_path=COMPENDIUM_PATH,
        expected_historical_sha256=HISTORICAL_SHA256,
    )
    assert resolved["domain"] == subject.FROZEN_GIT_BLOB_SHA256
    assert resolved["git_blob_oid"] == "ccd41b23e28ee01cc23c41821d0f4dde5ccb13fb"
    assert resolved["sha256"] == CURRENT_SHA256
    assert resolved["bytes"] == 13658


def test_both_current_consumers_preserve_the_historical_generator_pin() -> None:
    assert scalar.COMPENDIUM_RELATIVE_PATH == COMPENDIUM_PATH
    assert scalar.COMPENDIUM_SHA256 == HISTORICAL_SHA256
    assert pillar.COMPENDIUM_PATH.relative_to(pillar.REPO_ROOT).as_posix() == (
        COMPENDIUM_PATH
    )
    assert pillar.EXPECTED_COMPENDIUM_SHA256 == HISTORICAL_SHA256


def test_contract_rejects_a_rebound_historical_pin(tmp_path: Path) -> None:
    contract = copy.deepcopy(subject.load_contract())
    contract["identity"]["historical_identity"]["sha256"] = "0" * 64
    contract_path = tmp_path / "contract.json"
    _write_contract(contract_path, contract)
    with pytest.raises(
        subject.IdentityContractError,
        match="preserve the consumer's historical pin",
    ):
        subject.verify_equation_compendium(
            expected_historical_sha256=HISTORICAL_SHA256,
            contract_path=contract_path,
        )


def test_contract_rejects_a_different_frozen_blob_oid(tmp_path: Path) -> None:
    contract = copy.deepcopy(subject.load_contract())
    contract["identity"]["current_identity"]["git_blob_oid"] = "0" * 40
    contract_path = tmp_path / "contract.json"
    _write_contract(contract_path, contract)
    with pytest.raises(
        subject.IdentityContractError,
        match="Git blob OID mismatch",
    ):
        subject.verify_equation_compendium(contract_path=contract_path)


def test_contract_rejects_noncanonical_serialization(tmp_path: Path) -> None:
    contract_path = tmp_path / "contract.json"
    contract_path.write_text('{"schema_id": "wrong"}\n', encoding="utf-8")
    with pytest.raises(
        subject.IdentityContractError,
        match="not canonical JSON",
    ):
        subject.load_contract(contract_path)
