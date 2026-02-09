from __future__ import annotations

from pathlib import Path

import pytest

from formal.python.tools import repo_hygiene_snapshot as hygiene


def test_fixture_allowlist_covers_known_archive_reference() -> None:
    # This path is loaded directly by tests via importlib.util.spec_from_file_location.
    assert hygiene.is_fixture_path(
        "archive/fundamental_theory/crft/diagnostics/acoustic_metric.py"
    )


def test_default_ignore_treats_archive_as_noncanonical_except_fixtures() -> None:
    assert hygiene.is_ignored_by_default("archive/area_law_scan.py")
    assert not hygiene.is_ignored_by_default(
        "archive/fundamental_theory/crft/diagnostics/acoustic_metric.py"
    )


def test_fast_snapshot_and_fast_diff_quiet(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    snaps = tmp_path / "snaps"
    root.mkdir(parents=True, exist_ok=True)
    snaps.mkdir(parents=True, exist_ok=True)

    (root / "a.txt").write_text("hello", encoding="utf-8")
    (root / "b.txt").write_text("world", encoding="utf-8")

    baseline_path = snaps / "baseline_fast.jsonl"
    current_path = snaps / "current_fast.jsonl"

    hygiene.write_snapshot_atomic(
        root=root,
        out_path=baseline_path,
        ignore_globs=(),
        include_hash=False,
        mode="fast",
    )
    hygiene.write_snapshot_atomic(
        root=root,
        out_path=current_path,
        ignore_globs=(),
        include_hash=False,
        mode="fast",
    )

    baseline = hygiene.read_snapshot(baseline_path)
    current = hygiene.read_snapshot(current_path)
    new, modified, missing = hygiene.diff_snapshots(baseline, current)
    assert new == []
    assert modified == []
    assert missing == []


def test_full_vs_fast_diff_quiet_on_unchanged_repo(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    snaps = tmp_path / "snaps"
    root.mkdir(parents=True, exist_ok=True)
    snaps.mkdir(parents=True, exist_ok=True)

    (root / "a.txt").write_text("hello", encoding="utf-8")
    (root / "b.txt").write_text("world", encoding="utf-8")

    baseline_path = snaps / "baseline_full.jsonl"
    current_path = snaps / "current_fast.jsonl"

    hygiene.write_snapshot_atomic(
        root=root,
        out_path=baseline_path,
        ignore_globs=(),
        include_hash=True,
        mode="full",
    )
    hygiene.write_snapshot_atomic(
        root=root,
        out_path=current_path,
        ignore_globs=(),
        include_hash=False,
        mode="fast",
    )

    baseline = hygiene.read_snapshot(baseline_path)
    current = hygiene.read_snapshot(current_path)
    new, modified, missing = hygiene.diff_snapshots(baseline, current)
    assert new == []
    assert modified == []
    assert missing == []


def test_snapshot_write_is_atomic_and_cleans_tmp_on_failure(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    root = tmp_path / "repo"
    snaps = tmp_path / "snaps"
    root.mkdir(parents=True, exist_ok=True)
    snaps.mkdir(parents=True, exist_ok=True)

    (root / "a.txt").write_text("hello", encoding="utf-8")

    out_path = snaps / "snap.jsonl"
    tmp_path_expected = out_path.with_suffix(out_path.suffix + ".tmp")

    def _boom(_src: Path, _dst: Path) -> None:
        raise RuntimeError("rename failed")

    monkeypatch.setattr(hygiene, "_atomic_replace", _boom)

    with pytest.raises(RuntimeError):
        hygiene.write_snapshot_atomic(
            root=root,
            out_path=out_path,
            ignore_globs=(),
            include_hash=False,
            mode="fast",
        )

    assert not out_path.exists()
    assert not tmp_path_expected.exists()


def test_repo_hygiene_snapshot_fast_mode_is_non_authoritative_but_deterministic(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    snaps = tmp_path / "snaps"
    root.mkdir(parents=True, exist_ok=True)
    snaps.mkdir(parents=True, exist_ok=True)

    # FAST mode is non-authoritative (no content hashes), but it should still be
    # deterministic for an unchanged tree.
    (root / "a.txt").write_text("hello", encoding="utf-8")
    (root / "b.txt").write_text("world", encoding="utf-8")

    s1 = snaps / "fast1.jsonl"
    s2 = snaps / "fast2.jsonl"

    hygiene.write_snapshot_atomic(
        root=root,
        out_path=s1,
        ignore_globs=(),
        include_hash=False,
        mode="fast",
    )
    hygiene.write_snapshot_atomic(
        root=root,
        out_path=s2,
        ignore_globs=(),
        include_hash=False,
        mode="fast",
    )

    assert s1.read_text(encoding="utf-8") == s2.read_text(encoding="utf-8")
