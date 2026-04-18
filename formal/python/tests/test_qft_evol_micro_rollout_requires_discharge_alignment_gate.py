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
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
PACK_PATH = PAPER_DIR / "QFT_DISCHARGE_READINESS_PACK_v0.md"

MICRO_PATH_PATTERN = re.compile(r"DERIVATION_TARGET_QFT_EVOL_MICRO_(\d+)_")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_micro_rollout_beyond_52_requires_discharge_alignment_or_expansion_tag() -> None:
    pack_text = _read(PACK_PATH)
    assert "QFT_EVOL_MICRO_EXPANSION_ALIGNMENT_v0" in pack_text

    evol_micro_docs = sorted(PAPER_DIR.glob("DERIVATION_TARGET_QFT_EVOL_MICRO_*.md"))
    violations: list[str] = []

    for path in evol_micro_docs:
        m = MICRO_PATH_PATTERN.search(path.name)
        assert m is not None, f"Unable to parse EVOL micro index from `{path.name}`."
        cycle_number = int(m.group(1))
        if cycle_number <= 52:
            continue

        text = _read(path)
        tagged_expansion = "EXPANSION_NONCLOSURE" in text
        linked_in_pack = path.name in pack_text

        if not (tagged_expansion or linked_in_pack):
            violations.append(
                f"{path.name}: EVOL micro >52 must either include EXPANSION_NONCLOSURE tag or be explicitly listed in QFT_DISCHARGE_READINESS_PACK_v0.md."
            )

    assert not violations, "QFT EVOL rollout/discharge alignment violations:\n- " + "\n- ".join(violations)
