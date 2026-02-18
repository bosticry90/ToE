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
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"

BANNED_UNBOUNDED_PHRASES = [
    "continuum complete",
    "external truth",
    "unbounded inevitability",
    "infinite domain",
    "global uniqueness",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _upgrade_files() -> list[Path]:
    files = set(REPO_ROOT.glob("**/*POLICY_UPGRADE*.md"))
    files.update(REPO_ROOT.glob("**/*GOVERNANCE_UPGRADE*.md"))
    return sorted(files)


def _is_negated_line(line_lower: str, phrase: str) -> bool:
    escaped = re.escape(phrase)
    negation_patterns = [
        rf"\bno\b[^\n]*\b{escaped}\b",
        rf"\bnot\b[^\n]*\b{escaped}\b",
        rf"\bwithout\b[^\n]*\b{escaped}\b",
        rf"\bdoes\s+not\b[^\n]*\b{escaped}\b",
        rf"\bdo\s+not\b[^\n]*\b{escaped}\b",
        rf"\bdoesn't\b[^\n]*\b{escaped}\b",
        rf"\bdon't\b[^\n]*\b{escaped}\b",
    ]
    return any(re.search(pattern, line_lower) for pattern in negation_patterns)


def test_unbounded_claim_phrases_require_explicit_policy_upgrade_file() -> None:
    tracked_docs = [STATE_PATH] + sorted(PAPER_DIR.glob("*.md"))
    phrase_hits: dict[str, list[str]] = {}

    for path in tracked_docs:
        text = _read(path)
        for idx, line in enumerate(text.splitlines(), start=1):
            line_lower = line.lower()
            for phrase in BANNED_UNBOUNDED_PHRASES:
                if phrase in line_lower and not _is_negated_line(line_lower, phrase):
                    phrase_hits.setdefault(phrase, []).append(f"{path.relative_to(REPO_ROOT)}:{idx}")

    if not phrase_hits:
        return

    upgrades = _upgrade_files()
    upgrade_texts = {path: _read(path).lower() for path in upgrades}

    violations: list[str] = []
    for phrase, locations in sorted(phrase_hits.items()):
        approved = any(phrase in text for text in upgrade_texts.values())
        if not approved:
            locations_str = ", ".join(locations)
            violations.append(f"'{phrase}' found at {locations_str} without policy-upgrade authorization file.")

    assert not violations, "Unbounded claim posture violation:\n- " + "\n- ".join(violations)
