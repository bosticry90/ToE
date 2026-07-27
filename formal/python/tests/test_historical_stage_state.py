from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests.historical_stage_state import (
    HistoricalStageRoot,
    historical_path_presence_overlay,
)


def test_router_redirects_only_declared_successor_paths(tmp_path: Path) -> None:
    real_root = tmp_path / "real"
    stage_root = tmp_path / "stage"
    real_root.mkdir()
    (real_root / "predecessor.json").write_text("preserved\n", encoding="utf-8")
    successor = real_root / "release" / "successor.json"
    successor.parent.mkdir()
    successor.write_text("later\n", encoding="utf-8")

    view = HistoricalStageRoot(
        real_root,
        stage_root,
        ["release/successor.json"],
    )

    assert view.path("predecessor.json") == real_root / "predecessor.json"
    assert view.path("release/successor.json") == (
        stage_root / "release" / "successor.json"
    )
    assert not view.routes_to_stage(real_root / "predecessor.json")
    assert view.routes_to_stage(successor)


def test_presence_overlay_hides_successor_without_changing_archive(
    tmp_path: Path,
) -> None:
    real_root = tmp_path / "real"
    stage_root = tmp_path / "stage"
    real_root.mkdir()
    predecessor = real_root / "predecessor.json"
    predecessor.write_text("preserved\n", encoding="utf-8")
    successor = real_root / "release" / "successor.json"
    successor.parent.mkdir()
    successor.write_text("later\n", encoding="utf-8")

    with historical_path_presence_overlay(
        real_root=real_root,
        stage_root=stage_root,
        absent_relative_paths=["release/successor.json"],
        profile="UNIT_TEST_STAGE",
    ):
        assert predecessor.read_text(encoding="utf-8") == "preserved\n"
        assert not successor.exists()

    assert successor.read_text(encoding="utf-8") == "later\n"
    manifest = json.loads(
        (stage_root / "stage_state_manifest.json").read_text(encoding="utf-8")
    )
    assert manifest["profile"] == "UNIT_TEST_STAGE"
    assert manifest["absent_successor_paths"] == ["release/successor.json"]
    assert (
        manifest["predecessor_byte_policy"]
        == "READ_COMMITTED_PATHS_WITH_EXISTING_ARTIFACT_HASH_GATES"
    )
