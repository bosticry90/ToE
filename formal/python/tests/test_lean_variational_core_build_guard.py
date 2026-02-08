from __future__ import annotations

import subprocess
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TOE_FORMAL_ROOT = REPO_ROOT / "formal" / "toe_formal"
BUILD_SCRIPT = TOE_FORMAL_ROOT / "build.ps1"

CORE_VARIATIONAL_MODULES = [
    "ToeFormal.Variational.EvolutionGeneratorLaw",
    "ToeFormal.Variational.SemigroupWithGenerator",
    "ToeFormal.Variational.DeclaredAction",
    "ToeFormal.Variational.EvolutionDeclared",
    "ToeFormal.Variational.DeclaredDynamics",
]


def test_variational_evolution_linkage_modules_build():
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
        *CORE_VARIATIONAL_MODULES,
    ]
    proc = subprocess.run(
        cmd,
        cwd=TOE_FORMAL_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, (
        "Lean build guard failed for variational evolution-linkage modules.\n"
        f"Command: {' '.join(cmd)}\n"
        f"stdout:\n{proc.stdout}\n"
        f"stderr:\n{proc.stderr}"
    )
