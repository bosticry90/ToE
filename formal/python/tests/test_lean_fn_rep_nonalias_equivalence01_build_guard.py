from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TOE_FORMAL_ROOT = REPO_ROOT / "formal" / "toe_formal"
BUILD_SCRIPT = TOE_FORMAL_ROOT / "build.ps1"

FN_REP_NONALIAS_EQ_MODULES = [
    "ToeFormal.Variational.FieldRepresentation",
    "ToeFormal.Variational.FieldRepresentationRep32",
    "ToeFormal.Variational.FNRepNonAliasEquivalence01",
]


def test_fn_rep_nonalias_equivalence01_modules_build() -> None:
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
        *FN_REP_NONALIAS_EQ_MODULES,
    ]
    proc = subprocess.run(
        cmd,
        cwd=TOE_FORMAL_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, (
        "Lean build guard failed for non-alias equivalence target modules.\n"
        f"Command: {' '.join(cmd)}\n"
        f"stdout:\n{proc.stdout}\n"
        f"stderr:\n{proc.stderr}"
    )
