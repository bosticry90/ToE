from __future__ import annotations

import subprocess
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
TOE_FORMAL_DIR = REPO_ROOT / "formal" / "toe_formal"


def test_qft_gauge_object_scaffold_module_builds() -> None:
    result = subprocess.run(
        ["lake", "build", "ToeFormal.QFT.Gauge.ObjectScaffold"],
        cwd=TOE_FORMAL_DIR,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        out = result.stdout[-4000:]
        err = result.stderr[-4000:]
        raise AssertionError(
            "Lean module build failed for ToeFormal.QFT.Gauge.ObjectScaffold.\n"
            f"stdout (tail):\n{out}\n\nstderr (tail):\n{err}"
        )
