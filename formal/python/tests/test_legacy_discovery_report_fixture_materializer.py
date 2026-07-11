from __future__ import annotations

import hashlib
from pathlib import Path
from types import SimpleNamespace

import pytest

from formal.python.tests import legacy_discovery_report_fixture_materializer as fixture
from formal.python.tools.legacy_discovery_report_fixture_packet import ROOT_FIXTURES


def test_contract_has_exact_unique_bounded_scope() -> None:
    fixture.validate_contract()
    assert len(fixture.AFFECTED_TEST_PATHS) == 20
    assert sum(map(len, fixture.DERIVED_DEPENDENCIES.values())) == 35


def test_contract_rejects_duplicate_output_and_order_violation() -> None:
    duplicate = list(fixture.DERIVED_REPORT_CHAIN)
    duplicate[-1] = duplicate[0]
    with pytest.raises(fixture.FixtureMaterializationError, match="duplicate runtime output"):
        fixture.validate_contract(duplicate)
    reversed_chain = list(reversed(fixture.DERIVED_REPORT_CHAIN))
    with pytest.raises(
        fixture.FixtureMaterializationError, match="order violation or dependency cycle"
    ):
        fixture.validate_contract(reversed_chain)


def test_activation_is_exact_and_collection_scoped() -> None:
    affected = next(iter(fixture.AFFECTED_TEST_PATHS))
    assert fixture.should_activate([SimpleNamespace(nodeid=f"{affected}::test_x")])
    assert not fixture.should_activate(
        [SimpleNamespace(nodeid="formal/python/tests/test_unrelated.py::test_x")]
    )


def test_three_tracked_root_fixtures_match_frozen_bytes() -> None:
    for row in ROOT_FIXTURES:
        raw = (fixture.REPO_ROOT / row["planned_fixture_path"]).read_bytes()
        fixture._validate_root_fixture(raw, row)
        assert len(raw) == row["size_bytes"]
        assert hashlib.sha256(raw).hexdigest() == row["sha256"]


def test_root_fixture_negative_controls_reject_size_and_hash_drift() -> None:
    row = ROOT_FIXTURES[0]
    raw = (fixture.REPO_ROOT / row["planned_fixture_path"]).read_bytes()
    with pytest.raises(fixture.FixtureMaterializationError, match="size mismatch"):
        fixture._validate_root_fixture(raw[:-1], row)
    changed = bytes([raw[0] ^ 1]) + raw[1:]
    with pytest.raises(fixture.FixtureMaterializationError, match="hash mismatch"):
        fixture._validate_root_fixture(changed, row)


def test_install_and_cleanup_custody_helpers_preserve_preexisting(tmp_path: Path) -> None:
    created: list[Path] = []
    created_expected: dict[Path, str] = {}
    preserved: list[Path] = []
    new_path = tmp_path / "new.json"
    old_path = tmp_path / "old.json"
    old_path.write_bytes(b"{}\n")
    fixture._install_exact_or_preserve(
        new_path,
        b"{}\n",
        created=created,
        created_expected=created_expected,
        preserved=preserved,
    )
    fixture._install_exact_or_preserve(
        old_path,
        b"{}\n",
        created=created,
        created_expected=created_expected,
        preserved=preserved,
    )
    assert created == [new_path]
    assert preserved == [old_path]
    for path in reversed(created):
        path.unlink()
    assert not new_path.exists()
    assert old_path.read_bytes() == b"{}\n"


def test_two_materializations_produce_same_canonical_map_and_preserve_workspace() -> None:
    tracked_paths = [fixture.REPO_ROOT / row["historical_runtime_path"] for row in ROOT_FIXTURES]
    tracked_paths.extend(
        fixture.REPO_ROOT / "formal/output/reports" / output
        for _, _, output, _ in fixture.DERIVED_REPORT_CHAIN
    )
    before = {path: path.read_bytes() if path.exists() else None for path in tracked_paths}
    with fixture.materialized_legacy_discovery_reports() as first:
        first_map = first.canonical_sha256_by_path
        assert len(first_map) == 21
    with fixture.materialized_legacy_discovery_reports() as second:
        second_map = second.canonical_sha256_by_path
    assert first_map == second_map
    after = {path: path.read_bytes() if path.exists() else None for path in tracked_paths}
    assert after == before
