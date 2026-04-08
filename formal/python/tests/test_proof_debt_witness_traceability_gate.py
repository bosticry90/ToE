from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
TRACE_DOC = REPO_ROOT / "formal" / "docs" / "release" / "TOE_PROOF_DEBT_WITNESS_TRACEABILITY_v0.md"
LEAN_REGISTRY = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "ProofDebtRegistry.lean"
PACKET_DOC = REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_proof_debt_traceability_surfaces_exist_and_pin_tokens() -> None:
    trace_text = _read(TRACE_DOC)
    lean_text = _read(LEAN_REGISTRY)
    _read(PACKET_DOC)

    assert "TOE_PROOF_DEBT_TRACEABILITY_STATUS_v0: ACTIVE_BOUNDED_NONCLAIM" in trace_text
    assert "TOE_PROOF_DEBT_TRACEABILITY_GAPID_CLASS_v0: OPEN_PROOF_DEBT" in trace_text
    assert "formal/toe_formal/ToeFormal/ProofDebtRegistry.lean" in trace_text

    assert "structure ProofDebtRow" in lean_text
    assert "def boundedProofDebtRowSurface" in lean_text
    assert "theorem proof_debt_traceability_pointer" in lean_text
