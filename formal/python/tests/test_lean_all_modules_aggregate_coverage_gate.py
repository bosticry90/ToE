from __future__ import annotations

from formal.python.tools.generate_lean_all_modules_aggregate import (
    OUTPUT_PATH,
    render_aggregate,
    tracked_module_names,
)


def test_all_tracked_lean_modules_are_in_the_validation_aggregate() -> None:
    modules = tracked_module_names()
    assert modules
    assert len(modules) == len(set(modules))
    assert OUTPUT_PATH.read_bytes() == render_aggregate()

    aggregate = OUTPUT_PATH.read_text(encoding="utf-8")
    for module in modules:
        assert f"import {module}\n" in aggregate


def test_validation_aggregate_is_explicitly_nonpromotional() -> None:
    aggregate = OUTPUT_PATH.read_text(encoding="utf-8")
    assert "does not" in aggregate
    assert "promote any theorem" in aggregate
    assert "discharge any axiom" in aggregate


def test_exhaustive_root_is_registered_as_a_nondefault_lake_target() -> None:
    lakefile = (OUTPUT_PATH.parent / "lakefile.toml").read_text(encoding="utf-8")
    assert 'defaultTargets = ["ToeFormal"]' in lakefile
    assert 'name = "ToeFormalAll"' in lakefile
