from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_ROOT = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal"


def test_ad01_caus_time_order_gate_is_nlse_first_order_and_checked():
    canonicals = (LEAN_ROOT / "Constraints" / "AD01_Canonicals.lean").read_text(
        encoding="utf-8", errors="replace"
    )
    instances = (LEAN_ROOT / "Constraints" / "AD01_Instances.lean").read_text(
        encoding="utf-8", errors="replace"
    )
    time_order_tests = (LEAN_ROOT / "Constraints" / "AD01_TimeOrderTests.lean").read_text(
        encoding="utf-8", errors="replace"
    )

    # NLSE-style commitment: the canonical suite uses first-order-in-time packaging.
    assert "EvolForm.firstOrderTime" in canonicals

    # AD01 CAUS wiring must include the non-circular operator-level metadata sanity check.
    assert "TimeOrderSaneOp" in instances

    # Consequence check module: proves (structurally) that second-order metadata cannot
    # satisfy a first-order suite form.
    assert "ad01_caus_rejects_second_order_time" in time_order_tests
    assert "EvolForm.secondOrderTime" in time_order_tests
