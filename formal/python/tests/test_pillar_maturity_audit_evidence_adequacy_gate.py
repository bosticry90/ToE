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
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_MATURITY_AUDIT_v0.md"

PILLARS = ("QFT", "QM", "GR", "EM", "SR")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_gate_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing required gate token `{token_name}` in maturity audit."
    return m.group(1)


def _extract_results_rows(text: str) -> dict[str, tuple[float, float, float]]:
    pattern = re.compile(
        r"(?m)^\|\s*(QFT|QM|GR|EM|SR)\s*\|\s*([0-5]\.\d)\s*\|\s*([0-5]\.\d)\s*\|\s*([0-5]\.\d)\s*\|"
    )
    rows: dict[str, tuple[float, float, float]] = {}
    for m in pattern.finditer(text):
        pillar = m.group(1)
        rows[pillar] = (float(m.group(2)), float(m.group(3)), float(m.group(4)))
    assert set(rows.keys()) == set(PILLARS), "Results table must include QFT/QM/GR/EM/SR rows."
    return rows


def test_pillar_maturity_audit_evidence_adequacy_gate() -> None:
    text = _read(AUDIT_PATH)
    rows = _extract_results_rows(text)

    custody_gate = _extract_gate_token(text, "EVIDENCE_CUSTODY_5X5_GATE")
    adequacy_gate = _extract_gate_token(text, "EVIDENCE_ADEQUACY_5X5_GATE")

    evidence_is_5 = {pillar: (vals[1] == 5.0) for pillar, vals in rows.items()}
    any_evidence_5 = any(evidence_is_5.values())

    all_dimensions_5 = all(closure == 5.0 and evidence == 5.0 and drift == 5.0 for closure, evidence, drift in rows.values())

    if any_evidence_5:
        assert adequacy_gate == "SATISFIED_v0", (
            "Evidence Completeness cannot be 5.0 for any pillar unless EVIDENCE_ADEQUACY_5X5_GATE is SATISFIED_v0."
        )
        for pillar, is_5 in evidence_is_5.items():
            if is_5:
                token = f"EVIDENCE_ADEQUACY_{pillar}_5X5_JUSTIFICATION_v0"
                value = _extract_gate_token(text, token)
                assert value == "PRESENT", (
                    f"{token} must be PRESENT when {pillar} Evidence Completeness is scored 5.0."
                )

    if all_dimensions_5:
        assert custody_gate == "SATISFIED_v0", "All-5 assignment requires EVIDENCE_CUSTODY_5X5_GATE = SATISFIED_v0."
        assert adequacy_gate == "SATISFIED_v0", "All-5 assignment requires EVIDENCE_ADEQUACY_5X5_GATE = SATISFIED_v0."

    if adequacy_gate != "SATISFIED_v0":
        assert not any_evidence_5, (
            "If EVIDENCE_ADEQUACY_5X5_GATE is not SATISFIED_v0, no pillar may have Evidence Completeness = 5.0."
        )
