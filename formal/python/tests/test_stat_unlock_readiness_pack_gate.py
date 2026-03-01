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
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STAT_UNLOCK_READINESS_AUDIT_v0.md"
MATRIX_PREP_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STAT_MATRIX_PREP_CHECKLIST_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

# Do not include this aggregation gate itself to avoid recursive re-entry.
STAT_READINESS_PACK_GATES = [
    "formal/python/tests/test_stat_unlock_prerequisite_integrity_gate.py",
    "formal/python/tests/test_stat_no_circular_dependency_with_closed_pillars.py",
    "formal/python/tests/test_stat_readiness_placeholder_structure_gate.py",
    "formal/python/tests/test_stat_authority_token_preset_lock_gate.py",
    "formal/python/tests/test_stat_activation_changeset_template_structure_gate.py",
    "formal/python/tests/test_pillar_status_matrix_consistency_gate.py",
    "formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py",
    "formal/python/tests/test_authority_token_single_definition_gate.py",
    "formal/python/tests/test_results_table_integrity.py",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_stat_unlock_readiness_pack_gate() -> None:
    audit_text = _read(AUDIT_PATH)
    matrix_prep_text = _read(MATRIX_PREP_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    stat_locked = "| `PILLAR-STAT` | `LOCKED` |" in roadmap_text
    if not stat_locked:
        assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text or "| `PILLAR-STAT` | `CLOSED` |" in roadmap_text, (
            "STAT readiness aggregation gate expects LOCKED, ACTIVE, or CLOSED posture."
        )

    for gate_rel in STAT_READINESS_PACK_GATES:
        gate_path = REPO_ROOT / gate_rel
        assert gate_path.exists(), f"Missing STAT readiness gate file `{gate_rel}`."
        assert gate_rel in audit_text, f"STAT readiness audit must pin `{gate_rel}`."
        assert gate_rel in matrix_prep_text, f"STAT matrix prep checklist must pin `{gate_rel}`."

    if not stat_locked:
        return

    cmd = [sys.executable, "-m", "pytest", *STAT_READINESS_PACK_GATES]
    result = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert result.returncode == 0, (
        "STAT readiness pack is not green.\n"
        f"Command: {' '.join(cmd)}\n"
        f"stdout:\n{result.stdout}\n"
        f"stderr:\n{result.stderr}"
    )
