from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TOE_FORMAL_ROOT = REPO_ROOT / "formal" / "toe_formal"
BUILD_SCRIPT = TOE_FORMAL_ROOT / "build.ps1"

FN01_REP32_MODULES = [
    "ToeFormal.Variational.ActionRep32CubicLane",
    "ToeFormal.Variational.DischargeELMatchesFN01Rep32Pcubic",
]


def test_fn01_rep32_discharge_modules_build():
    assert BUILD_SCRIPT.exists(), f"Missing Lean build wrapper: {BUILD_SCRIPT}"
    shell = shutil.which("pwsh") or shutil.which("powershell") or shutil.which("powershell.exe")
    assert shell is not None, "Expected pwsh/powershell on PATH for Lean build guard."

    cmd = [
        shell,
        "-NoProfile",
        "-ExecutionPolicy",
        "Bypass",
        "-File",
        str(BUILD_SCRIPT),
        *FN01_REP32_MODULES,
    ]
    proc = subprocess.run(
        cmd,
        cwd=TOE_FORMAL_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, (
        "Lean build guard failed for FN/Rep32 discharge modules.\n"
        f"Command: {' '.join(cmd)}\n"
        f"stdout:\n{proc.stdout}\n"
        f"stderr:\n{proc.stderr}"
    )
