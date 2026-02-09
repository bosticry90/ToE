from __future__ import annotations

from pathlib import Path

from formal.python.tools.regen_canonical_locks import main as regen_main


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def test_regen_bragg_only_is_content_stable() -> None:
    lock_paths = [
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-03_bragg_dispersion_k_omega_digitized.md",
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-04A_bragg_lowk_slope_conditionA.md",
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-04B_bragg_lowk_slope_conditionB.md",
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-05_bragg_lowk_slope_summary.md",
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-DR-BR-00_br01_prediction_declarations.md",
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-DR-BR-01_candidate_pruning_table.md",
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-SEL-BR-01_bragg_lowk_slope_audit.md",
    ]

    before = [p.read_text(encoding="utf-8") for p in lock_paths]

    # Should run without requiring any sound-lane artifacts.
    rc = regen_main(["--bragg-only"])
    assert rc == 0

    after = [p.read_text(encoding="utf-8") for p in lock_paths]
    assert after == before
