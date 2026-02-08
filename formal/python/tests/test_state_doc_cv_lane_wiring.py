from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _extract_block(text: str, *, block_id: str) -> str:
    marker_re = re.compile(rf"^ID:\s*{re.escape(block_id)}\s*$", flags=re.MULTILINE)
    m = marker_re.search(text)
    if m is None:
        raise AssertionError(f"Could not find exact block marker for ID: {block_id!r}")
    start = m.start()

    next_idx = text.find("\n\n\nID:", start + 1)
    if next_idx < 0:
        return text[start:]
    return text[start:next_idx]


def _extract_gap_block(text: str, *, gap_id: str) -> str:
    marker_re = re.compile(rf"^GapID:\s*{re.escape(gap_id)}\s*$", flags=re.MULTILINE)
    m = marker_re.search(text)
    if m is None:
        raise AssertionError(f"Could not find exact gap marker for GapID: {gap_id!r}")
    start = m.start()

    nxt = re.search(r"^GapID:\s*\S+\s*$", text[m.end() :], flags=re.MULTILINE)
    if nxt is None:
        return text[start:]
    return text[start : m.end() + nxt.start()]


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def _field_count(block: str, field: str) -> int:
    prefix = f"{field}:"
    return sum(1 for line in block.splitlines() if line.startswith(prefix))


def test_state_doc_has_cv_and_domain_blocks_with_evidence():
    text = STATE_PATH.read_text(encoding="utf-8")

    required_ids = ["OV-CV-01", "OV-CV-BR-01", "DRBR-DOMAIN-02", "OV-CV-02"]
    for block_id in required_ids:
        block = _extract_block(text, block_id=block_id)
        evidence = _first_field(block, "Evidence") or ""
        assert evidence, f"Expected non-empty Evidence field in {block_id}"
        assert "formal/" in evidence.replace("\\", "/"), f"Expected path-like evidence pointer in {block_id}"
        assert _field_count(block, "Dependencies") == 1, f"Expected exactly one Dependencies line in {block_id}"

    bridge_block = _extract_block(text, block_id="OV-CV-BR-01")
    bridge_evidence = _first_field(bridge_block, "Evidence") or ""
    assert "OV-CV-BR-01_cv01_v1_pruning_bridge.md" in bridge_evidence
    assert "OV-CV-BR-01_cv01_v1_pruning_bridge_NEG_CONTROL.md" in bridge_evidence

    cv02_block = _extract_block(text, block_id="OV-CV-02")
    cv02_deps = _first_field(cv02_block, "Dependencies") or ""
    assert "DRBR-DOMAIN-02" in cv02_deps


def test_comp_pred_fals_evidence_mentions_cv_bridge_and_domain02_lanes():
    text = STATE_PATH.read_text(encoding="utf-8")
    block = _extract_gap_block(text, gap_id="COMP-PRED-FALS")
    assert _field_count(block, "Evidence path") == 1, "Expected exactly one Evidence path line in COMP-PRED-FALS"

    evidence = _first_field(block, "Evidence path") or ""
    required_tokens = [
        "formal/python/toe/comparators/cv01_bec_bragg_v1.py",
        "formal/python/toe/observables/ovcvbr01_cv01_v1_pruning_bridge_record.py",
        "formal/markdown/locks/observables/OV-CV-BR-01_cv01_v1_pruning_bridge.md",
        "formal/python/toe/comparators/cv02_bec_bragg_b1_v0.py",
        "formal/docs/second_empirical_comparator_domain_bec_bragg_b1.md",
    ]
    for token in required_tokens:
        assert token in evidence, f"Missing COMP-PRED-FALS evidence token: {token}"
