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
TEMPLATE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md"
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STAT_UNLOCK_READINESS_AUDIT_v0.md"
MATRIX_PREP_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STAT_MATRIX_PREP_CHECKLIST_v0.md"
UNLOCK_CHECKLIST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_stat_activation_changeset_template_structure_gate() -> None:
    template_text = _read(TEMPLATE_PATH)
    audit_text = _read(AUDIT_PATH)
    matrix_prep_text = _read(MATRIX_PREP_PATH)
    unlock_checklist_text = _read(UNLOCK_CHECKLIST_PATH)

    assert "Spec ID:" in template_text and "`PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0`" in template_text
    assert "Classification:" in template_text and "`P-POLICY`" in template_text
    assert "Non-claim boundary:" in template_text
    assert "## Mandatory Files To Touch" in template_text
    assert "## Exact Validation Commands" in template_text

    for required_path in (
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json",
        "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
        "State_of_the_Theory.md",
        "formal/docs/release/PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0.md",
    ):
        assert f"`{required_path}`" in template_text, f"Template must pin `{required_path}`."

    for required_gate in (
        "formal/python/tests/test_stat_unlock_readiness_pack_gate.py",
        "formal/python/tests/test_stat_authority_token_preset_lock_gate.py",
        "formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py",
        "formal/python/tests/test_authority_token_single_definition_gate.py",
        "formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py",
        "formal/python/tests/test_pillar_adjudication_legacy_retirement_gate.py",
        "formal/python/tests/test_results_table_integrity.py",
    ):
        assert required_gate in template_text, f"Template must pin `{required_gate}`."

    assert "LOCKED posture" in template_text
    assert "ACTIVE posture" in template_text
    assert "expected to fail after a successful activation flip" in template_text
    assert "intentionally excludes lock-scoped STAT readiness-pack gates" in template_text
    assert "Pinned token names:" in template_text
    assert "`PILLAR_STAT_FULL_DERIVATION_DISCHARGE_ADJUDICATION`" in template_text
    assert "`PILLAR_STAT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION`" in template_text
    assert "`NOT_YET_DISCHARGED`" in template_text

    # Ensure the lock-scoped preflight command and post-activation command are both explicitly present.
    code_blocks = re.findall(r"```powershell\n(.*?)\n```", template_text, flags=re.DOTALL)
    assert len(code_blocks) >= 2, "Template must contain explicit PowerShell command blocks."
    joined_blocks = "\n".join(code_blocks)
    assert "python -m pytest formal/python/tests/test_stat_unlock_readiness_pack_gate.py" in joined_blocks
    assert "test_pillar_adjudication_cross_surface_consistency_gate.py" in joined_blocks
    assert "test_pillar_adjudication_legacy_retirement_gate.py" in joined_blocks

    # Post-activation command block must not include the lock-scoped readiness-pack gate.
    post_block_candidates = [b for b in code_blocks if "test_pillar_matrix_roadmap_coverage_gate.py" in b]
    assert post_block_candidates, "Template must include a post-activation validation command block."
    for block in post_block_candidates:
        assert "test_stat_unlock_readiness_pack_gate.py" not in block, (
            "Post-activation validation command must exclude lock-scoped readiness-pack gate."
        )

    assert "legacy forbidden prefix `NOT_YET_`" in template_text
    assert "LOCKED -> ACTIVE" in template_text

    # Readiness docs must reference this template once it becomes part of the pre-activation control lane.
    template_rel = "formal/docs/release/PILLAR_STAT_ACTIVATION_CHANGESET_TEMPLATE_v0.md"
    for doc_text, doc_label in (
        (audit_text, "STAT unlock readiness audit"),
        (matrix_prep_text, "STAT matrix prep checklist"),
        (unlock_checklist_text, "PILLAR-STAT unlock readiness checklist"),
    ):
        assert template_rel in doc_text, f"{doc_label} must reference the STAT activation changeset template."
