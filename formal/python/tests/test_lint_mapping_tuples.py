from __future__ import annotations

from formal.python.tools.lint_mapping_tuples import lint_mapping_tuples


def test_mapping_tuples_lint_is_clean() -> None:
    res = lint_mapping_tuples(date="2026-01-24", fail_fast=False)
    assert res.errors == []
