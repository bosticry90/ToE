"""Guard bridge: robustness + falsification behavior for BRIDGE_TICKET_0002.

Ticket: formal/quarantine/bridge_tickets/BRIDGE_TICKET_0003_br05_ucff_lowk_slope_robustness.md

This is deterministic and bounded. It does not claim physical truth.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.toe.ucff.core_front_door import UcffCoreParams, ucff_dispersion_omega2_numeric


def _find_repo_root(start: Path) -> Path:
    for parent in (start.resolve(), *start.resolve().parents):
        if (parent / "README.md").exists():
            return parent
    raise RuntimeError("Could not locate repo root (expected README.md)")


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


def _fit_slope_through_origin(*, x: np.ndarray, y: np.ndarray) -> float:
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    assert x.shape == y.shape
    if x.ndim != 1:
        raise AssertionError("Expected 1D arrays")

    denom = float(np.dot(x, x))
    if denom == 0.0:
        raise AssertionError("Cannot fit slope with all-zero x")
    return float(np.dot(x, y) / denom)


def _ucff_lowk_slope_from_c(*, c: float) -> float:
    params = UcffCoreParams(rho0=1.0, g=float(c**2), lam=0.0, beta=0.0)
    k = np.array([0.0, 0.001, 0.002, 0.005, 0.01], dtype=float)
    omega2 = ucff_dispersion_omega2_numeric(k=k, params=params)
    omega = np.sqrt(omega2)
    return _fit_slope_through_origin(x=k[1:], y=omega[1:])


def test_bridge_br05_ucff_lowk_slope_robustness_and_falsification() -> None:
    repo_root = _find_repo_root(Path(__file__))

    lock_rel = Path("formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md")
    payload = _load_first_json_block_from_markdown(repo_root / lock_rel)

    assert payload["schema"] == "OV-BR-05_bragg_lowk_slope_summary/v1"
    assert payload["observable_id"] == "OV-BR-05"
    assert payload["status"]["blocked"] is False

    rows = payload.get("rows")
    assert isinstance(rows, list) and rows

    by_condition: dict[str, dict] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        key = row.get("condition_key")
        if isinstance(key, str):
            by_condition[key] = row

    a = by_condition["condition_A"]
    b = by_condition["condition_B"]

    s_a = float(a["s_kHz_per_um_inv"])
    se_a = float(a["se_kHz_per_um_inv"])
    s_b = float(b["s_kHz_per_um_inv"])
    se_b = float(b["se_kHz_per_um_inv"])

    ia_lo, ia_hi = s_a - se_a, s_a + se_a
    ib_lo, ib_hi = s_b - se_b, s_b + se_b

    inter_lo = max(ia_lo, ib_lo)
    inter_hi = min(ia_hi, ib_hi)

    # Guard premise: BRIDGE_TICKET_0002 only makes sense if the overlap exists.
    assert inter_hi > inter_lo

    width = inter_hi - inter_lo

    # Robustness: multiple deterministic interior points should all succeed.
    c_interior = [
        inter_lo + 0.25 * width,
        inter_lo + 0.50 * width,
        inter_lo + 0.75 * width,
    ]

    for c in c_interior:
        assert ia_lo <= c <= ia_hi
        assert ib_lo <= c <= ib_hi

        slope_ucff = _ucff_lowk_slope_from_c(c=c)
        assert abs(slope_ucff - c) <= 1e-3 * max(1.0, abs(c))

    # Falsification: deterministic points outside the overlap must violate the window constraint.
    delta = 0.50 * width
    c_outside = [inter_lo - delta, inter_hi + delta]

    for c in c_outside:
        in_a = ia_lo <= c <= ia_hi
        in_b = ib_lo <= c <= ib_hi
        assert not (in_a and in_b)

        # UCFF can still represent the chosen slope; this is not a failure.
        # The failure is the Bragg compatibility constraint.
        slope_ucff = _ucff_lowk_slope_from_c(c=c)
        assert abs(slope_ucff - c) <= 1e-3 * max(1.0, abs(c))
