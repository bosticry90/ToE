# B1 candidate dataset (Ernst et al., arXiv:0908.4242)

This folder is reserved for the **B1 second external dataset** anchor.

## Paper

Philipp T. Ernst et al.,
"Momentum-Resolved Bragg Spectroscopy in Optical Lattices,"
arXiv:0908.4242 (2009).

Local copy: `0908.4242v1.pdf`

## Figure selection (locked)

Authoritative digitization source for B1:

> **Figure 2a** \u2014 resonance energy/frequency vs momentum transfer (dispersion-style \u03c9(k) plot).

Notes
- This figure is expected to provide many discrete (k, \u03c9) points suitable for populating `omega_k_data.csv`.
- We will digitize a conservative subset first (enough for N\u22655 low-k windowing), then expand if needed.

## Status

- Citation + figure selection are set.
- Digitization protocol is locked (see below).

## Digitization protocol (locked; auditable + repeatable)

Fixed scope
- Paper: `0908.4242v1.pdf`
- Figure: Fig. 2a
- Series: single series only (no mixing)
- Target: 15–25 (k, ω) points across the visible range

Point-picking rule
1) Identify the leftmost plotted marker on the chosen series and the rightmost plotted marker on the same series.
2) Digitize every visible marker on that series between those endpoints.
3) If markers are dense/ambiguous: digitize the marker center closest to the ideal position; do not invent midpoints.

Axis calibration (fixed for this digitization)
- Use two well-separated labeled ticks on each axis.
- Calibration ticks used (auto-detected from the PDF text layer on the Fig2a panel):
	- kBragg ticks: k = 0.0 and k = 1.0
	- ω ticks: ω/2π = 0.0 kHz and ω/2π = 2.5 kHz

Uncertainty placeholders (fixed)
- Error bars not digitized; placeholder sigmas are used uniformly for all rows:
	- sigma_k_um_inv = 0.05
	- sigma_omega_over_2pi_kHz = 0.10

Implementation (deterministic)
- Tool: `formal/python/tools/digitize_ernst_fig2a.py`
- Output: `omega_k_data.csv` (header unchanged; rows sorted by k)

Frozen invocation used for the current CSV
- `python -m formal.python.tools.digitize_ernst_fig2a --pdf .../0908.4242v1.pdf --out-csv .../omega_k_data.csv --crop-x0 0.18 --crop-x1 0.80 --crop-y0 0.08 --crop-y1 0.39 --dark-threshold 135 --min-area 6 --max-area 4000 --series-select strict-branch --k-cluster-tol 0.0005 --omega-nondecreasing-tol 0.03 --omega-decrease-penalty 5.0`
