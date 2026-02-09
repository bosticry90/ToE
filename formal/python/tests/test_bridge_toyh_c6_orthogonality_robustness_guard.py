from __future__ import annotations

from pathlib import Path

import numpy as np

from formal.python.tools.bridge_toyh_c6_orthogonality_report_generate import (
    build_bridge_toyh_c6_orthogonality_report,
)


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _assert_nonredundant_with_mismatch(report: dict) -> None:
    summary = dict(report.get("summary", {}))
    counts = dict(summary.get("counts", {}))
    assert summary.get("nonredundant") is True
    assert int(counts.get("pass_fail", 0)) >= 1
    assert int(counts.get("fail_pass", 0)) >= 1


def test_bridge_toyh_c6_orthogonality_nonredundancy_robustness_guard() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    base_thetas = [0.0, float(np.pi / 6.0), float(np.pi / 3.0), float(np.pi / 2.0)]
    expanded_thetas = [
        0.0,
        float(np.pi / 8.0),
        float(np.pi / 6.0),
        float(np.pi / 3.0),
        float(np.pi / 2.0),
        float(2.0 * np.pi / 3.0),
    ]

    variants = [
        {"phase_thetas": base_thetas, "grid_sizes": [7, 9, 11], "tol": 1e-10},
        {"phase_thetas": base_thetas, "grid_sizes": [9, 11, 13], "tol": 1e-10},
        {"phase_thetas": expanded_thetas, "grid_sizes": [7, 9, 11], "tol": 1e-10},
        {"phase_thetas": base_thetas, "grid_sizes": [7, 9, 11], "tol": 1e-12},
    ]

    for cfg in variants:
        report = build_bridge_toyh_c6_orthogonality_report(
            repo_root=repo_root,
            phase_thetas=list(cfg["phase_thetas"]),
            grid_sizes=list(cfg["grid_sizes"]),
            tol=float(cfg["tol"]),
        )
        _assert_nonredundant_with_mismatch(report)

