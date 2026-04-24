from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SLICE_C_GR01_THEOREM_COMPRESSION_EXECUTION_PACKET_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _assert_tokens_present(text: str, *, tokens: list[str], label: str) -> None:
    missing = [tok for tok in tokens if tok not in text]
    assert not missing, f"Missing {label} token(s): " + ", ".join(missing)


def test_gr01_packet_entry_phase_tokens_present() -> None:
    text = _read(PACKET_PATH)
    required_tokens = [
        "# Slice C GR01 Theorem Compression Execution Packet v0",
        "Non-claim boundary:",
        "## 1) Boundary Anchor",
        "## 2) Objective and Bottleneck",
        "## 3) Representation-First Triage",
        "## 4) Search Outputs (Route Discovery)",
        "Declared file envelope:",
    ]
    _assert_tokens_present(text, tokens=required_tokens, label="entry phase")


def test_gr01_packet_content_phase_tokens_present() -> None:
    text = _read(PACKET_PATH)
    required_tokens = [
        "## 5) Referee Objections",
        "## 6) Repair Plan (Bounded Correction)",
        "## 7) Validation Ladder (Fixed)",
        "## 8) Stop Conditions",
        "## 9) Acceptance Criteria",
        "Acceptance measurement rule:",
    ]
    _assert_tokens_present(text, tokens=required_tokens, label="content phase")


def test_gr01_packet_exit_phase_tokens_present() -> None:
    text = _read(PACKET_PATH)
    required_tokens = [
        "## 10) Outcome Memo Block (Cycle01 Snapshot)",
        "## 11) Next-Lane Decision Gate",
        "## 12) Traceability",
        "Outcome A:",
        "Outcome B:",
        "Exact validations run:",
    ]
    _assert_tokens_present(text, tokens=required_tokens, label="exit phase")
