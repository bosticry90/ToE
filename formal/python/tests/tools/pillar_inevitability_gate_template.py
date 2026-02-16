from __future__ import annotations

import re
from pathlib import Path
from typing import Iterable


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def read_text(path: Path) -> str:
    if not path.exists():
        raise AssertionError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def theorem_block(text: str, theorem_name: str) -> str:
    start_match = re.search(rf"\\btheorem\\s+{re.escape(theorem_name)}\\b", text)
    if start_match is None:
        raise AssertionError(f"Missing theorem token: {theorem_name}")
    start = start_match.start()
    next_match = re.search(r"\\n(?:theorem|def|abbrev|structure)\\s+", text[start_match.end() :])
    if next_match is None:
        return text[start:]
    end = start_match.end() + next_match.start()
    return text[start:end]


def assert_tokens_present(text: str, tokens: Iterable[str], label: str) -> None:
    missing = [tok for tok in tokens if tok not in text]
    if missing:
        raise AssertionError(f"Missing {label} token(s): " + ", ".join(missing))


def assert_forbidden_tokens_absent(text: str, tokens: Iterable[str], label: str) -> None:
    present = [tok for tok in tokens if tok in text]
    if present:
        raise AssertionError(f"Forbidden {label} token(s) present: " + ", ".join(present))


def assert_canonical_route_contract(
    module_text: str,
    canonical_theorem: str,
    constructor_token: str,
    forbidden_shortcuts: Iterable[str],
    required_nontrivial: Iterable[str],
) -> None:
    block = theorem_block(module_text, canonical_theorem)
    if constructor_token not in block:
        raise AssertionError(
            f"Canonical theorem {canonical_theorem} must invoke constructor token {constructor_token}."
        )
    assert_forbidden_tokens_absent(block, forbidden_shortcuts, "shortcut")
    assert_tokens_present(block, required_nontrivial, "nontriviality")


def assert_compatibility_lane_contract(
    module_text: str,
    compatibility_theorem: str,
    required_compatibility_tokens: Iterable[str],
    forbidden_canonical_tokens: Iterable[str],
) -> None:
    block = theorem_block(module_text, compatibility_theorem)
    assert_tokens_present(block, required_compatibility_tokens, "compatibility-lane")
    assert_forbidden_tokens_absent(block, forbidden_canonical_tokens, "canonical-lane leakage")


# Usage guidance (copy into per-pillar gate tests):
# 1) Define core discharge-critical token list and compatibility token list.
# 2) Use theorem_block(...) to inspect canonical and constructor theorem bodies.
# 3) Enforce anti-circularity (forbidden bridge/policy tokens).
# 4) Enforce nontriviality (forbid trivial shortcuts + require explicit obligations).
# 5) Enforce compatibility-lane integrity (required compatibility markers +
#    forbidden canonical-marker leakage).
# 6) Gate adjudication flips on canonical route tokens only.
