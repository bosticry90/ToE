from __future__ import annotations

from pathlib import Path

from formal.python.tools.regen_canonical_locks import main as regen_main
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))


def test_regen_sw_only_is_content_stable() -> None:
    lock_paths = [
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-SW-01_shallow_water_lowk_slope.md",
        # Guardrail: sw-only must not touch other canonical locks.
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-02_regime_bridge_record.md",
    ]

    before = [p.read_text(encoding="utf-8") for p in lock_paths]

    rc = regen_main(["--sw-only", "--validate-only"])
    assert rc == 0

    after = [p.read_text(encoding="utf-8") for p in lock_paths]
    assert after == before
