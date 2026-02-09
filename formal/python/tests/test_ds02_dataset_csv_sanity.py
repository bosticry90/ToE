from __future__ import annotations

import csv
from pathlib import Path

import pytest


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def test_ds02_dataset_csv_sanity_skips_until_populated_then_enforces_lowk_density():
    csv_path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_ds02_lowk_dataset_TBD"
        / "omega_k_data.csv"
    )

    # Scaffold must exist.
    assert csv_path.exists()

    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    # Keep the repo green while DS-02 is still a header-only scaffold.
    if len(rows) == 0:
        pytest.skip("DS-02 omega_k_data.csv not yet populated")

    # Enforce single-source, single-figure discipline to prevent accidental mixing.
    figures = {str(r.get("figure", "")).strip() for r in rows}
    sources = {str(r.get("source", "")).strip() for r in rows}
    assert len(figures) == 1
    assert len(sources) == 1
    assert next(iter(figures)) == "Fig. 2"
    assert next(iter(sources)) != ""

    ks = [float(r["k_um_inv"]) for r in rows]
    omegas = [float(r["omega_over_2pi_kHz"]) for r in rows]

    # Canonicalization rule: keep the CSV deterministically ordered.
    assert ks == sorted(ks)

    # Stronger: enforce uniqueness / no duplicates (prevents accidental weighting).
    assert all(ks[i] < ks[i + 1] for i in range(len(ks) - 1))

    assert all(k >= 0.0 for k in ks)

    # ω/2π should be non-negative for the plotted branch.
    assert all(w >= 0.0 for w in omegas)

    # Sigma columns, if present/filled, must be numeric and non-negative.
    for key in ("sigma_k_um_inv", "sigma_omega_over_2pi_kHz"):
        for r in rows:
            val = str(r.get(key, "")).strip()
            if val == "":
                continue
            assert float(val) >= 0.0

    # Optional series/marker guard: if the CSV includes a series label column,
    # enforce that it reflects the pinned "filled circles" selection.
    for key in ("series", "marker", "legend"):
        if key not in rows[0]:
            continue
        vals = {str(r.get(key, "")).strip().lower() for r in rows}
        # Allow empty if the column exists but is intentionally unused.
        if vals == {""}:
            continue
        assert len(vals) == 1
        v = next(iter(vals))
        assert "filled" in v
        assert "open" not in v

    # Row-count sanity: intended to be a moderately dense low-k dataset.
    assert 15 <= len(rows) <= 40

    # Bracketing constraints: enforce true low-k and ensure non-empty overlap
    # with the current OV-03x high-k anchor (~3.34 μm⁻¹).
    assert min(ks) <= 0.4
    assert max(ks) >= 3.33842

    # Low-k density constraint (highest-leverage early guardrail).
    # Target: ≥10 points in the low-k region.
    k_lowk_max = 1.5
    n_lowk_required = 10
    n_lowk = sum(1 for k in ks if k <= k_lowk_max)
    assert n_lowk >= n_lowk_required
