from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read_suite() -> str:
    assert SUITE_PATH.exists(), "Missing governance suite script."
    return SUITE_PATH.read_text(encoding="utf-8")


def _index_or_fail(content: str, needle: str) -> int:
    idx = content.find(needle)
    assert idx >= 0, f"Expected governance divergence policy text not found: {needle}"
    return idx


def test_governance_divergence_guardrail_staged_policy_contract() -> None:
    content = _read_suite()

    param_idx = _index_or_fail(content, "param(")
    override_idx = _index_or_fail(content, "[switch]$AllowDivergenceOverride")
    warn_idx = _index_or_fail(content, "$warnLimit = 10")
    hard_idx = _index_or_fail(content, "$hardLimit = 20")
    override_limit_idx = _index_or_fail(content, "$overrideLimit = 30")

    strict_fail_idx = _index_or_fail(content, "Divergence guardrail failed: local branch is ahead by $aheadCount commits (hard limit $hardLimit).")
    override_msg_idx = _index_or_fail(content, "TOE_ALLOW_DIVERGENCE_OVERRIDE=1")
    absolute_fail_idx = _index_or_fail(content, "Divergence guardrail failed: local branch is ahead by $aheadCount commits (override limit $overrideLimit).")

    assert param_idx < override_idx < warn_idx < hard_idx < override_limit_idx
    assert strict_fail_idx < override_msg_idx < absolute_fail_idx
