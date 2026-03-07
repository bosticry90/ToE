from __future__ import annotations

import sys

import formal.python.tools.dev_stack_preflight as preflight


def test_evaluate_environment_reports_python() -> None:
    status = preflight.evaluate_environment()
    assert status.python_ok is True
    assert status.python_executable == sys.executable


def test_main_warns_without_rust_when_optional(monkeypatch) -> None:
    monkeypatch.setattr(preflight.shutil, "which", lambda _name: None)
    rc = preflight.main([])
    assert rc == 0


def test_main_fails_without_rust_when_required(monkeypatch) -> None:
    monkeypatch.setattr(preflight.shutil, "which", lambda _name: None)
    rc = preflight.main(["--require-rust"])
    assert rc == 2
