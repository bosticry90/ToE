from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _run_regen(args: list[str]) -> subprocess.CompletedProcess[str]:
    cmd = [sys.executable, "-m", "formal.python.tools.regen_canonical_locks", *args]
    return subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
    )


def _has_flag(flag: str) -> bool:
    proc = _run_regen(["--help"])
    assert proc.returncode == 0
    help_text = (proc.stdout or "") + (proc.stderr or "")
    return flag in help_text


def test_regen_rejects_bragg_only_plus_snd_only() -> None:
    proc = _run_regen(["--bragg-only", "--snd-only"])
    assert proc.returncode != 0

    err = (proc.stderr or "").lower()
    assert "not allowed with argument" in err
    assert "--bragg-only" in err
    assert "--snd-only" in err


def test_regen_rejects_sw_only_plus_snd_only() -> None:
    proc = _run_regen(["--sw-only", "--snd-only"])
    assert proc.returncode != 0

    err = (proc.stderr or "").lower()
    assert "not allowed with argument" in err
    assert "--sw-only" in err
    assert "--snd-only" in err


def test_regen_rejects_sw_only_plus_bragg_only() -> None:
    proc = _run_regen(["--sw-only", "--bragg-only"])
    assert proc.returncode != 0

    err = (proc.stderr or "").lower()
    assert "not allowed with argument" in err
    assert "--sw-only" in err
    assert "--bragg-only" in err


def test_regen_rejects_sw_only_plus_include_snd() -> None:
    proc = _run_regen(["--sw-only", "--include-snd"])
    assert proc.returncode != 0

    err = (proc.stderr or "").lower()
    assert "--sw-only cannot be combined with --include-snd" in err


def test_regen_rejects_bragg_only_plus_snd_digitization_only_if_present() -> None:
    if not _has_flag("--snd-digitization-only"):
        pytest.skip("--snd-digitization-only not present in regen CLI")

    proc = _run_regen(["--bragg-only", "--snd-digitization-only"])
    assert proc.returncode != 0

    err = (proc.stderr or "").lower()
    assert "not allowed with argument" in err
    assert "--bragg-only" in err
    assert "--snd-digitization-only" in err
