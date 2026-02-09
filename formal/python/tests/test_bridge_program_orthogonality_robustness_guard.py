from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_program_orthogonality_report_generate import (
    build_bridge_program_orthogonality_report,
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


def test_bridge_program_orthogonality_nonredundancy_robustness_guard() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    variants = [
        {"grid_sizes": [7, 9, 11], "toyh_tol": 1e-10, "toyg_tol_winding": 0.05},
        {"grid_sizes": [9, 11, 13], "toyh_tol": 1e-10, "toyg_tol_winding": 0.05},
        {"grid_sizes": [7, 9, 11], "toyh_tol": 1e-12, "toyg_tol_winding": 0.05},
        {"grid_sizes": [7, 9, 11], "toyh_tol": 1e-10, "toyg_tol_winding": 0.04},
    ]

    for cfg in variants:
        report = build_bridge_program_orthogonality_report(
            repo_root=repo_root,
            grid_sizes=list(cfg["grid_sizes"]),
            toyh_tol=float(cfg["toyh_tol"]),
            toyg_tol_winding=float(cfg["toyg_tol_winding"]),
        )
        summary = dict(report.get("summary", {}))
        pairwise = dict(summary.get("pairwise_disagreement_counts", {}))
        assert summary.get("nonredundant") is True
        assert int(pairwise.get("phase_vs_toyg_bridge", 0)) >= 1
        assert int(pairwise.get("current_vs_toyg_bridge", 0)) >= 1
