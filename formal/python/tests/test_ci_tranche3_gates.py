from __future__ import annotations

import re
from pathlib import Path


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = _find_repo_root(Path(__file__))
CI_PATH = REPO_ROOT / ".github" / "workflows" / "ci.yml"


def test_rust_trust_core_lane_is_blocking() -> None:
    text = CI_PATH.read_text(encoding="utf-8")
    marker = "  rust-trust-core:\n"
    assert marker in text, "Missing rust-trust-core CI job."
    start = text.index(marker)
    tail = text[start:]

    next_job = re.search(r"\n  [a-zA-Z0-9_-]+:\n", tail[len(marker) :])
    if next_job is None:
        block_text = tail
    else:
        end = len(marker) + next_job.start()
        block_text = tail[:end]

    assert "continue-on-error: true" not in block_text, "rust-trust-core must remain blocking."
    assert "cargo build --manifest-path formal/rust/toe_trust_core/Cargo.toml" in block_text
    assert "cargo run --manifest-path formal/rust/toe_trust_core/Cargo.toml" in block_text


def test_sql_integrity_lane_fails_on_issues() -> None:
    text = CI_PATH.read_text(encoding="utf-8")
    assert "sql-integrity-smoke:" in text, "Missing sql-integrity-smoke CI job."
    assert "formal.python.tools.sql_integrity_snapshot" in text
    assert "--fail-on-issues" in text, "SQL integrity smoke must fail on reported issues."
