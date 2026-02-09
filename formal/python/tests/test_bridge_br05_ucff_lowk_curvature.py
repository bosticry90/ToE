"""Bridge attempt: BR low-k window ↔ UCFF omega^2 curvature/convexity (bounded).

Ticket: formal/quarantine/bridge_tickets/BRIDGE_TICKET_0004_br05_ucff_lowk_curvature.md

This is a deterministic, structural compatibility constraint only.
It does not claim physical truth or unit identification.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.toe.ucff.core_front_door import UcffCoreParams, ucff_dispersion_omega2_numeric


def _find_repo_root(start: Path) -> Path:
    for parent in (start.resolve(), *start.resolve().parents):
        if (parent / "formal").exists():
            return parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory)")


def _load_first_json_block_from_markdown(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    parts = text.split("```json")
    if len(parts) < 2:
        raise AssertionError(f"No ```json block found in {path}")
    rest = parts[1]
    end = rest.find("```")
    if end < 0:
        raise AssertionError(f"Unterminated ```json block in {path}")
    blob = rest[:end].strip()
    return json.loads(blob)


def _uniform_grid(*, k_max: float, n: int) -> np.ndarray:
    if n < 3:
        raise ValueError("n must be >= 3")
    if k_max <= 0:
        raise ValueError("k_max must be > 0")
    return np.linspace(0.0, float(k_max), int(n), dtype=float)


def test_bridge_br_lowk_window_ucff_omega2_is_convex_on_pinned_grid() -> None:
    repo_root = _find_repo_root(Path(__file__))

    # Source the low-k window definition from the Bragg lane selection rule.
    ovbr04a_rel = Path("formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md")
    ovbr04a = _load_first_json_block_from_markdown(repo_root / ovbr04a_rel)
    assert ovbr04a["observable_id"] == "OV-BR-04A"
    assert ovbr04a["status"]["blocked"] is False

    sel = dict(ovbr04a.get("selection", {}))
    params = dict(sel.get("parameters", {}))
    k_max = float(params["k_um_inv_max"])

    # Deterministic UCFF parameters (fixed; no tuning).
    # Use simple exact floats (powers of two / quarters) to keep the computation stable.
    ucff_params = UcffCoreParams(rho0=1.0, g=2.0, lam=0.25, beta=0.125)

    # Deterministic low-k grid over the Bragg window.
    k = _uniform_grid(k_max=k_max, n=9)

    omega2 = ucff_dispersion_omega2_numeric(k=k, params=ucff_params)
    assert omega2.shape == k.shape

    # Discrete second differences for uniform grid: proportional to second derivative.
    diff2 = omega2[2:] - 2.0 * omega2[1:-1] + omega2[:-2]

    # Convexity compatibility constraint.
    eps = 1e-12
    assert float(np.min(diff2)) >= -eps


def test_bridge_br_lowk_window_ucff_omega2_convexity_negative_control_operator_sanity() -> None:
    """Negative control: prove the convexity detector can fail.

    Keep everything fixed (Bragg window, UCFF params, grid). Only apply a
    deterministic adversarial transformation to the finite-difference operator.
    """

    repo_root = _find_repo_root(Path(__file__))

    ovbr04a_rel = Path("formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md")
    ovbr04a = _load_first_json_block_from_markdown(repo_root / ovbr04a_rel)
    assert ovbr04a["observable_id"] == "OV-BR-04A"
    assert ovbr04a["status"]["blocked"] is False

    sel = dict(ovbr04a.get("selection", {}))
    params = dict(sel.get("parameters", {}))
    k_max = float(params["k_um_inv_max"])

    ucff_params = UcffCoreParams(rho0=1.0, g=2.0, lam=0.25, beta=0.125)
    k = _uniform_grid(k_max=k_max, n=9)
    omega2 = ucff_dispersion_omega2_numeric(k=k, params=ucff_params)

    # Correct second difference (should be convex / non-negative).
    diff2 = omega2[2:] - 2.0 * omega2[1:-1] + omega2[:-2]
    assert float(np.min(diff2)) >= -1e-12

    # Wrong operator: deterministic sign flip. This must violate the convexity inequality
    # unless diff2 is numerically ~0 everywhere (which would make the constraint uninformative).
    diff2_wrong = -diff2

    # Negative-control success condition: the wrong operator produces a clear violation.
    # (Fixed threshold; no tuning.)
    assert float(np.min(diff2_wrong)) < -1e-8
