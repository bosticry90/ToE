from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
TEMPLATE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_CLOSURE_CHANGESET_TEMPLATE_v0.md"
CHECKLIST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_CLOSURE_PREP_CHECKLIST_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
UNLOCK_CHECKLIST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_stat_closure_changeset_template_structure_gate() -> None:
    template_text = _read(TEMPLATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)
    state_text = _read(STATE_PATH)
    unlock_text = _read(UNLOCK_CHECKLIST_PATH)

    assert "Spec ID:" in template_text and "`PILLAR_STAT_CLOSURE_CHANGESET_TEMPLATE_v0`" in template_text
    assert "Classification:" in template_text and "`P-POLICY`" in template_text
    assert "## Preconditions" in template_text
    assert "## Mandatory Files To Touch" in template_text
    assert "## Exact Validation Commands" in template_text

    for required_path in (
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json",
        "formal/docs/paper/RESULTS_TABLE_v0.md",
        "formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json",
        "State_of_the_Theory.md",
        "formal/docs/release/PILLAR_STAT_CLOSURE_PREP_CHECKLIST_v0.md",
    ):
        assert f"`{required_path}`" in template_text, f"Closure template must pin `{required_path}`."

    for required_gate in (
        "formal/python/tests/test_stat_dual_closure_posture_gate.py",
        "formal/python/tests/test_stat_closure_changeset_template_structure_gate.py",
        "formal/python/tests/test_pillar_dual_layer_gate_template.py",
        "formal/python/tests/test_pillar_status_matrix_consistency_gate.py",
        "formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py",
        "formal/python/tests/test_authority_token_single_definition_gate.py",
        "formal/python/tests/test_results_table_integrity.py",
        "formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py",
        "formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py",
        "formal/python/tests/test_pillar_full_discharge_completion_mechanics.py",
    ):
        assert required_gate in template_text, f"Closure template must pin `{required_gate}`."

    assert "ACTIVE -> CLOSED" in template_text
    assert "`TOE-STAT-DER-01` and `TOE-STAT-DER-02` are no longer `P-POLICY` placeholders" in template_text
    assert "Current closure-prep posture is `OPEN/BLOCKED`" in template_text
    assert "Closure patch must transition these tokens to `CLOSED/ALLOWED`" in template_text

    code_blocks = re.findall(r"```powershell\n(.*?)\n```", template_text, flags=re.DOTALL)
    assert len(code_blocks) >= 2, "Closure template must contain explicit PowerShell command blocks."
    joined_blocks = "\n".join(code_blocks)
    assert "test_stat_dual_closure_posture_gate.py" in joined_blocks
    assert "test_pillar_full_discharge_completion_mechanics.py" in joined_blocks

    template_rel = "formal/docs/release/PILLAR_STAT_CLOSURE_CHANGESET_TEMPLATE_v0.md"
    checklist_rel = "formal/docs/release/PILLAR_STAT_CLOSURE_PREP_CHECKLIST_v0.md"
    assert template_rel in checklist_text, "Closure prep checklist must reference the closure changeset template."
    assert checklist_rel in state_text, "State checkpoint must reference the closure prep checklist."
    assert template_rel in state_text, "State checkpoint must reference the closure changeset template."
    assert checklist_rel in unlock_text, "Unlock checklist handoff must reference the closure prep checklist."
    assert template_rel in unlock_text, "Unlock checklist handoff must reference the closure changeset template."
