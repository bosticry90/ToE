from __future__ import annotations

from pathlib import Path

from formal.python.tools.physics_math_throughput_rolling_window_metrics import compute_metrics


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_program_token_for_rolling_window_gate_present() -> None:
    text = _read(PROGRAM_PATH)
    token = (
        "PHYS_MATH_THROUGHPUT_PROGRAM_ROLLING_WINDOW_GATE_v0: "
        "formal/python/tests/test_physics_math_throughput_rolling_window_improvement_gate.py"
    )
    assert token in text


def test_rolling_window_science_signal_positive() -> None:
    metrics = compute_metrics()
    assert metrics["science_signal_rolling_mean"] > 0.0


def test_rolling_window_controls_signal_nonzero() -> None:
    metrics = compute_metrics()
    assert metrics["controls_signal_rolling_mean"] > 0.0


def test_science_signal_last_window_not_regressing_to_zero() -> None:
    metrics = compute_metrics()
    series = metrics["science_signal_series"]
    assert len(series) == metrics["window_size"]
    assert series[-1] > 0.0
