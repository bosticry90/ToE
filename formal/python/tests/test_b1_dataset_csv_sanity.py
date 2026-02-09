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


def test_b1_omega_k_csv_has_nonnegative_k_and_expected_density():
    """Sanity check for the B1 digitized dataset packet.

    This is non-interpretive hygiene only: the momentum magnitude |k| must be
    non-negative, and the frozen protocol targets a 15–25 point dataset.
    """

    csv_path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_b1_second_dataset_TBD"
        / "omega_k_data.csv"
    )

    if not csv_path.exists():
        pytest.skip("B1 omega_k_data.csv not present")

    rows: list[dict[str, str]] = []
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    assert 15 <= len(rows) <= 25

    k_vals: list[float] = []
    for r in rows:
        k_vals.append(float(r["k_um_inv"]))

    assert all(k >= 0.0 for k in k_vals)
    assert k_vals == sorted(k_vals)
