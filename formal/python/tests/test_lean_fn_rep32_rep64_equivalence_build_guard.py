from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TOE_FORMAL_ROOT = REPO_ROOT / "formal" / "toe_formal"
BUILD_SCRIPT = TOE_FORMAL_ROOT / "build.ps1"

FN_REP32_REP64_EQ_MODULES = [
    "ToeFormal.Variational.DischargeELMatchesFN01Rep32Pcubic",
    "ToeFormal.Variational.DischargeELMatchesFN01Rep64Pcubic",
    "ToeFormal.Variational.FNRepresentationEquivalencePolicy",
    "ToeFormal.Variational.FNRep32Rep64Equivalence",
]


def test_fn_rep32_rep64_equivalence_modules_build():
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
        *FN_REP32_REP64_EQ_MODULES,
    ]
    proc = subprocess.run(
        cmd,
        cwd=TOE_FORMAL_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, (
        "Lean build guard failed for FN Rep32<->Rep64 equivalence modules.\n"
        f"Command: {' '.join(cmd)}\n"
        f"stdout:\n{proc.stdout}\n"
        f"stderr:\n{proc.stderr}"
    )
