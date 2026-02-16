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
TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"
)
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _state_full_row(text: str) -> str:
    m = re.search(r"TOE-GR-FULL-01:\s*(T-PROVED|B-BLOCKED)", text)
    assert m is not None, "Missing TOE-GR-FULL-01 token in State_of_the_Theory.md"
    return m.group(1)


def _state_adjudication(text: str) -> str:
    m = re.search(
        r"FULL_DERIVATION_ADJUDICATION:\s*"
        r"(DISCHARGED_v0_DISCRETE|NOT_YET_DISCHARGED_v0)",
        text,
    )
    assert m is not None, "Missing FULL_DERIVATION_ADJUDICATION token in State_of_the_Theory.md"
    return m.group(1)


def _target_classification(text: str) -> str:
    m = re.search(r"Classification:\s*\n-\s*`([^`]+)`", text)
    assert m is not None, "Missing Classification token in derivation target doc"
    return m.group(1)


def _target_adjudication(text: str) -> str:
    m = re.search(
        r"FULL_DERIVATION_ADJUDICATION:\s*"
        r"(DISCHARGED_v0_DISCRETE|NOT_YET_DISCHARGED_v0)",
        text,
    )
    assert m is not None, "Missing FULL_DERIVATION_ADJUDICATION token in derivation target doc"
    return m.group(1)


def _results_status(text: str) -> str:
    m = re.search(r"^\| TOE-GR-FULL-01 \| `([^`]+)` \|", text, flags=re.MULTILINE)
    assert m is not None, "Missing TOE-GR-FULL-01 row in results table"
    return m.group(1)


def test_gr01_full_derivation_status_surfaces_are_atomic_and_in_sync() -> None:
    state_text = _read(STATE_PATH)
    target_text = _read(TARGET_PATH)
    results_text = _read(RESULTS_PATH)

    state_row = _state_full_row(state_text)
    state_adj = _state_adjudication(state_text)
    target_cls = _target_classification(target_text)
    target_adj = _target_adjudication(target_text)
    results_status = _results_status(results_text)

    allowed_state_pairs = {
        ("T-PROVED", "DISCHARGED_v0_DISCRETE"),
        ("B-BLOCKED", "NOT_YET_DISCHARGED_v0"),
    }
    assert (state_row, state_adj) in allowed_state_pairs, (
        "State_of_the_Theory has inconsistent TOE-GR-FULL-01/adjudication pair: "
        f"({state_row}, {state_adj})"
    )

    if state_row == "T-PROVED":
        assert target_cls == "T-PROVED", (
            "State says TOE-GR-FULL-01 is T-PROVED but derivation target classification is not T-PROVED."
        )
        assert target_adj == "DISCHARGED_v0_DISCRETE", (
            "State says TOE-GR-FULL-01 is T-PROVED but derivation target adjudication is not DISCHARGED_v0_DISCRETE."
        )
        assert results_status == "T-PROVED", (
            "State says TOE-GR-FULL-01 is T-PROVED but results row is not T-PROVED."
        )
    else:
        assert target_cls == "B-BLOCKED", (
            "State says TOE-GR-FULL-01 is B-BLOCKED but derivation target classification is not B-BLOCKED."
        )
        assert target_adj == "NOT_YET_DISCHARGED_v0", (
            "State says TOE-GR-FULL-01 is B-BLOCKED but derivation target adjudication is not NOT_YET_DISCHARGED_v0."
        )
        assert results_status.startswith("B-"), (
            "State says TOE-GR-FULL-01 is B-BLOCKED but results row is not blocked."
        )
