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


def _split_blocks(text: str) -> list[str]:
    # Blocks are canonically separated by blank lines and the next "ID:" marker.
    blocks: list[str] = []
    start = text.find("ID: ")
    while start >= 0:
        next_idx = text.find("\n\n\nID:", start + 1)
        if next_idx < 0:
            blocks.append(text[start:])
            break
        blocks.append(text[start:next_idx])
        start = next_idx + 3  # skip the leading \n\n\n
    return blocks


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def test_state_doc_mainline_nodes_do_not_claim_beta_nonzero():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    # Forbidden phrasing: assertions that beta is nonzero / detected curvature.
    forbidden = re.compile(
        r"(\bβ\s*(?:!=|≠)\s*0\b|\bbeta\s*(?:!=|≠)\s*0\b|\bβ\s+non\s*-?zero\b|\bbeta\s+non\s*-?zero\b|\bnon\s*-?zero\s+β\b|\bnon\s*-?zero\s+beta\b|\bdetected\s+curvature\b|\bcurvature\s+detected\b)",
        flags=re.IGNORECASE,
    )

    # Allow speculation only in explicitly non-mainline statuses.
    allowed_statuses = {"Hypothesis", "Spec-backed"}

    offenders: list[str] = []

    for block in _split_blocks(doc):
        block_id = _first_field(block, "ID") or "<unknown>"
        status = _first_field(block, "Status") or "<missing>"

        # Mainline = not Deprecated (and not explicitly speculative).
        if status == "Deprecated":
            continue

        m = forbidden.search(block)
        if m is None:
            continue

        if status in allowed_statuses:
            continue

        offenders.append(f"{block_id} (Status: {status}) matched: {m.group(0)!r}")

    assert not offenders, (
        "Mainline inventory blocks must not assert beta is nonzero / curvature detected.\n"
        "If such a claim is desired, it must be explicitly labeled Hypothesis or Spec-backed and gated by future evidence.\n"
        + "\n".join(["  - " + o for o in offenders])
    )
