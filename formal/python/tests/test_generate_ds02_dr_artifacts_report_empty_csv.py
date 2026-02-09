from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def test_generate_ds02_dr_artifacts_report_empty_csv_is_non_throwing_and_exits_zero():
    # This test pins the "armed but safe" behavior: report mode should not
    # throw whether DS-02 is still scaffold-only or has been populated.
    cmd = [
        sys.executable,
        "-m",
        "formal.python.tools.generate_ds02_dr_artifacts",
        "--report",
    ]

    proc = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0

    out = proc.stdout or ""
    if "DS-02 report: no rows found" in out:
        # Scaffold-only mode.
        assert "Populate omega_k_data.csv" in out
    else:
        # Populated mode: should print row count + window policy summary.
        assert "DS-02 rows:" in out
        assert "DR01(overlap)" in out
