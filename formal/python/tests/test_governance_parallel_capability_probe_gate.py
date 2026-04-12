from __future__ import annotations

from formal.python.tools import governance_parallel_capability_probe as probe


def test_parallel_probe_reports_available_when_help_and_collect_succeed(monkeypatch) -> None:
    calls: list[list[str]] = []

    def fake_run(args: list[str]) -> tuple[int, str]:
        calls.append(args)
        if args == ["-m", "pytest", "--help"]:
            return 0, "...\n  -n NUM\n..."
        return 0, "ok"

    monkeypatch.setattr(probe, "_run_pyps1", fake_run)
    payload = probe.build_probe(workers="auto", captured_at_utc="2026-04-11T00:00:00Z")

    assert payload["capability_available"] is True
    assert payload["parallel_activated"] is True
    assert payload["probe_details"]["help_has_n_flag"] is True
    assert len(calls) == 2


def test_parallel_probe_reports_unavailable_when_n_flag_missing(monkeypatch) -> None:
    def fake_run(args: list[str]) -> tuple[int, str]:
        if args == ["-m", "pytest", "--help"]:
            return 0, "help-without-parallel"
        return 0, "unused"

    monkeypatch.setattr(probe, "_run_pyps1", fake_run)
    payload = probe.build_probe(workers="2", captured_at_utc=None)

    assert payload["capability_available"] is False
    assert payload["parallel_activated"] is False
    assert payload["probe_details"]["collect_probe_exit_code"] == 1
