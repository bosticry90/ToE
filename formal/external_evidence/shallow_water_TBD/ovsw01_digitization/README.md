# Shallow-water lane (Axis C) — ingestion contract (governance-only)

Date: 2026-01-25

Status: contract-only (no data yet)

Purpose

- Define the accepted ingestion format for the Axis C shallow-water lane digitization.
- Specify pinned units and minimal CSV structure.
- Prevent interpretation leakage: this directory is an ingestion surface, not a cross-lane mapping surface.

Non-claims

- This lane does not assert any relationship to Bragg, sound, or any other lane.
- This lane does not assert the shallow-water model is correct.
- No cross-lane comparisons are authorized by the existence of this directory.

## Accepted quantity

We ingest a low-k dispersion plot expressed as:

- x-axis: wavenumber $k$ in `m^-1`
- y-axis: frequency $f = ω/(2π)$ in `s^-1`

The lane-level observable extracts a low-k slope in `(s^-1)/(m^-1)` (dimensionally `m/s`) via a pinned through-origin slope rule.

## Pinned units (must not vary)

- `k`: `m^-1`
- `f`: `s^-1`

Do not use `cm^-1`, `mm^-1`, `Hz` vs `kHz`, etc. Convert upstream before writing the frozen CSV.

## Expected files (future)

When digitized data is added, it must be pinned under this directory as:

- `omega_over_2pi_vs_k_lowk.csv`
- `omega_over_2pi_vs_k_lowk.metadata.json`

## CSV format (future)

Header row required. Columns:

- `k_m_inv` (float)
- `f_s_inv` (float)

Rules:

- `k_m_inv >= 0`
- All values finite
- No implied weighting

## Metadata JSON (future)

The metadata wrapper must include at minimum:

- `source_relpath` and `source_sha256` for the pinned source PDF/PNG
- a short description of the digitization method
- any page/figure identifiers

## Forbidden in this directory

- Mapping tuples to other lanes
- Claims that the exported slope is “the same speed” as any other lane
- Any attempt to justify cross-lane pairing

Cross-lane work, if ever attempted, must live in a dedicated mapping surface and must remain admissibility-gated.
