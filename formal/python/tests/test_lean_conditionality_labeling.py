# C:\Users\psboy\Documents\ToE\formal\python\tests\test_lean_conditionality_labeling.py
from __future__ import annotations

import re
from pathlib import Path
from typing import List, Tuple


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
TOEFORMAL_ROOT = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal"

# Trigger: direct import of the axiom quarantine module
IMPORT_AXIOMS_RE = re.compile(r"^\s*import\s+.*PlaneWaveOperatorAxioms\s*$", re.MULTILINE)

# Detect theorem/lemma declarations (Lean4)
DECL_RE = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z0-9_']+)\b", re.MULTILINE)

# Heuristic: within the declaration header (until ':=' or 'where'/'by'), look for explicit axiom dependence
AXIOM_MARKERS = ("Dt_planeWave", "Delta_planeWave", "PlaneWaveOperatorAxioms")


def lean_files_under(root: Path) -> List[Path]:
    if not root.exists():
        return []
    return list(root.rglob("*.lean"))


def extract_decl_header(text: str, start_idx: int) -> str:
    """
    Extract a conservative header chunk starting at the theorem/lemma line,
    stopping at ':=' or 'where' or 'by' that typically ends the statement header.
    """
    tail = text[start_idx : start_idx + 4000]  # bounded
    stop_tokens = [":=", "\nwhere", "\nby"]
    stop = len(tail)
    for tok in stop_tokens:
        j = tail.find(tok)
        if j != -1:
            stop = min(stop, j)
    return tail[:stop]


def test_axiom_import_requires_conditional_label_or_explicit_axiom_hypothesis():
    offenders: List[Tuple[str, str]] = []

    for p in lean_files_under(TOEFORMAL_ROOT):
        text = p.read_text(encoding="utf-8", errors="replace")

        if not IMPORT_AXIOMS_RE.search(text):
            continue

        for m in DECL_RE.finditer(text):
            kind, name = m.group(1), m.group(2)
            if "conditional" in name.lower():
                continue

            header = extract_decl_header(text, m.start())
            if any(marker in header for marker in AXIOM_MARKERS):
                continue

            offenders.append((str(p.relative_to(REPO_ROOT)).replace("\\", "/"), name))

    assert not offenders, (
        "Conditionality labeling enforcement failed.\n\n"
        "Files that import PlaneWaveOperatorAxioms must EITHER:\n"
        "  (A) name each theorem/lemma with 'conditional' (e.g., foo_conditional), OR\n"
        "  (B) include explicit axiom hypotheses/markers in the declaration header (Dt_planeWave/Delta_planeWave).\n\n"
        "Offenders:\n"
        + "\n".join([f"  {fp} :: {nm}" for fp, nm in offenders])
    )
