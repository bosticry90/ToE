"""Boundary mapping: BRIDGE_TICKET_0004 curvature/convexity grid-density scan.

Deliverable class: boundary mapping only.
Ticket anchor: formal/quarantine/bridge_tickets/BRIDGE_TICKET_0004_br05_ucff_lowk_curvature.md
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
    return np.linspace(0.0, float(k_max), int(n), dtype=float)


def test_bridge_br05_ucff_lowk_curvature_grid_density_scan() -> None:
    repo_root = _find_repo_root(Path(__file__))

    ovbr04a_rel = Path("formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md")
    ovbr04a = _load_first_json_block_from_markdown(repo_root / ovbr04a_rel)
    assert ovbr04a["observable_id"] == "OV-BR-04A"
    assert ovbr04a["status"]["blocked"] is False

    sel = dict(ovbr04a.get("selection", {}))
    params = dict(sel.get("parameters", {}))
    k_max = float(params["k_um_inv_max"])

    ucff_params = UcffCoreParams(rho0=1.0, g=2.0, lam=0.25, beta=0.125)
    eps = 1e-12
    negctl_threshold = 1e-8

    for n in [5, 7, 9]:
        k = _uniform_grid(k_max=k_max, n=n)
        omega2 = ucff_dispersion_omega2_numeric(k=k, params=ucff_params)
        diff2 = omega2[2:] - 2.0 * omega2[1:-1] + omega2[:-2]

        assert float(np.min(diff2)) >= -eps

        # Negative control must continue to fail under the same grids.
        diff2_wrong = -diff2
        assert float(np.min(diff2_wrong)) < -negctl_threshold
