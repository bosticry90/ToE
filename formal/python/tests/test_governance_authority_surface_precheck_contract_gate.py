from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read_suite() -> str:
    assert SUITE_PATH.exists(), "Missing governance suite script."
    return SUITE_PATH.read_text(encoding="utf-8")


def _index_or_fail(content: str, needle: str) -> int:
    idx = content.find(needle)
    assert idx >= 0, f"Expected governance precheck contract text not found: {needle}"
    return idx


def test_governance_authority_surface_parity_precheck_contract() -> None:
    content = _read_suite()

    preflight_idx = _index_or_fail(content, "Running local stack preflight")
    tooling_idx = _index_or_fail(content, "Running tooling validation checks (no writes)")
    parity_idx = _index_or_fail(content, "Running authority-surface parity precheck")
    parity_cmd_idx = _index_or_fail(content, "./py.ps1 -m formal.python.tools.authority_surface_parity_check")
    parity_fail_idx = _index_or_fail(content, "Authority-surface parity precheck failed.")
    divergence_idx = _index_or_fail(content, "Running local divergence guardrail")

    assert preflight_idx < tooling_idx < parity_idx < parity_cmd_idx < parity_fail_idx < divergence_idx
