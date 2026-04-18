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
SR_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
EM_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_MATURITY_AUDIT_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_entry_blocks(text: str, entry_prefix: str) -> list[str]:
    pattern = re.compile(
        rf"- `{entry_prefix}_ADEQUACY_ENTRY_\d{{2}}_v0`\n(?P<body>(?:  - .*\n)+)",
        re.MULTILINE,
    )
    return [m.group("body") for m in pattern.finditer(text)]


def _assert_entry_block_shape(block: str, label: str) -> None:
    assert "artifact hash token:" in block, f"{label} is missing artifact hash token reference."
    assert "coupling gate path:" in block, f"{label} is missing coupling gate path reference."
    assert "pass criterion:" in block, f"{label} is missing pass criterion field."
    assert re.search(r"pass criterion:.*(Boolean|<=|>=|[0-9])", block) is not None, (
        f"{label} pass criterion must include explicit numeric or Boolean condition."
    )
    assert "failure" in block.lower(), f"{label} is missing failure taxonomy/mode field."


def test_sr_em_adequacy_justification_structure_gate() -> None:
    sr_text = _read(SR_DOC_PATH)
    em_text = _read(EM_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    audit_text = _read(AUDIT_PATH)

    assert _extract_token(sr_text, "EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_v0") == "PRESENT"
    assert _extract_token(em_text, "EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_v0") == "PRESENT"
    assert _extract_token(state_text, "EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_v0") == "PRESENT"
    assert _extract_token(state_text, "EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_v0") == "PRESENT"
    assert _extract_token(roadmap_text, "EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_v0") == "PRESENT"
    assert _extract_token(roadmap_text, "EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_v0") == "PRESENT"

    assert _extract_token(sr_text, "EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0") == "MIN_5_ENTRIES_REQUIRED"
    assert _extract_token(em_text, "EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0") == "MIN_5_ENTRIES_REQUIRED"
    assert _extract_token(state_text, "EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0") == "MIN_5_ENTRIES_REQUIRED"
    assert _extract_token(state_text, "EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0") == "MIN_5_ENTRIES_REQUIRED"
    assert _extract_token(roadmap_text, "EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0") == "MIN_5_ENTRIES_REQUIRED"
    assert _extract_token(roadmap_text, "EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0") == "MIN_5_ENTRIES_REQUIRED"

    assert _extract_token(audit_text, "EVIDENCE_ADEQUACY_SR_5X5_JUSTIFICATION_v0") == "PRESENT"
    assert _extract_token(audit_text, "EVIDENCE_ADEQUACY_EM_5X5_JUSTIFICATION_v0") == "PRESENT"
    assert _extract_token(audit_text, "EVIDENCE_ADEQUACY_5X5_GATE") == "NOT_SATISFIED_v0"

    sr_blocks = _extract_entry_blocks(sr_text, "SR")
    em_blocks = _extract_entry_blocks(em_text, "EM")

    assert len(sr_blocks) >= 5, "SR adequacy justification must include at least 5 entries."
    assert len(em_blocks) >= 5, "EM adequacy justification must include at least 5 entries."

    for idx, block in enumerate(sr_blocks[:5], start=1):
        _assert_entry_block_shape(block, f"SR adequacy entry {idx}")

    for idx, block in enumerate(em_blocks[:5], start=1):
        _assert_entry_block_shape(block, f"EM adequacy entry {idx}")
