# Digitization notes (B1 / Ernst et al. 2009)

Target: populate `omega_k_data.csv` from **Ernst et al. (arXiv:0908.4242), Fig. 2a**.

## CSV schema (do not change)

Columns:
- `source`: use `Ernst_2009_arXiv_0908.4242`
- `figure`: use `Fig2a`
- `k_um_inv`: momentum transfer magnitude in \u00b5m\u207b\u00b9
- `omega_over_2pi_kHz`: resonance frequency (\u03c9/2\u03c0) in kHz
- `sigma_k_um_inv`: optional; if not stated, use blank
- `sigma_omega_over_2pi_kHz`: optional; if not stated, use blank
- `notes`: any per-point note (e.g., which curve/lattice depth)

## Unit mapping intent

- If the figure reports energy as `E/h` in kHz, treat that as `omega_over_2pi_kHz`.
- Fig. 2a x-axis is `kBragg [\u03c0/a , \u03c0/a]` with **a = 515 nm** (paper text). The value 1.0 corresponds to the Brillouin-zone edge in the nodal ([1,1]) direction.
- Conversion used for this CSV: if the plotted coordinate is the scalar `s` where the Bragg momentum-transfer vector is `(s\u03c0/a, s\u03c0/a)`, then
	- `|k| = s * \sqrt{2} * \u03c0/a`
	- with `a = 0.515 \u00b5m`, so `|k| (\u00b5m\u207b\u00b9) = s * (\sqrt{2}\u03c0/0.515) \u2248 s * 8.626957`.

## Extraction method used (current CSV)

Digitization is performed deterministically using the in-repo tool:

- `python -m formal.python.tools.digitize_ernst_fig2a ...`

Method (high level)
- Render the Fig. 2 page from `0908.4242v1.pdf` at a fixed zoom.
- Select the Fig. 2a panel crop (fixed parameters used for the frozen CSV).
- Detect marker components in the plot region (threshold + connected components).
- Calibrate axes using two labeled ticks on each axis.
- Select a single series deterministically (no mixing).
- Emit `omega_k_data.csv` sorted by `k_um_inv`.

Important scope note (current freeze)
- The current frozen strict-branch extraction is **high-k only** (k starts at ~3.34 um^-1). Treat this dataset as a high-k robustness anchor; do not attach low-k regime claims to it unless a different digitization target/dataset is introduced.

## Axis calibration (frozen)

Ticks used:
- kBragg: 0.0 and 1.0
- ω/2π (kHz): 0.0 and 2.5

## Uncertainties (frozen placeholders)

Error bars were not digitized; placeholders are used uniformly for all rows:
- sigma_k_um_inv = 0.05
- sigma_omega_over_2pi_kHz = 0.10

## Frozen digitization parameters

The current frozen CSV was generated with:
- crop: x=[0.18, 0.80], y=[0.08, 0.39] (fractions of rendered page)
- detection: dark_threshold=135, min_area=6, max_area=4000
- series selection: strict-branch (single branch; no mixing)
	- k-cluster-tol = 0.0005
	- omega-nondecreasing-tol = 0.03 (soft tolerance; decreases beyond this are penalized)
	- omega-decrease-penalty = 5.0

## First-pass extraction plan (minimal, conservative)

- Start with a single curve/condition from Fig. 2a (one lattice depth / one branch) to keep B1 minimal.
- If low-k anchoring is required for the science intent, select a digitization target/dataset that actually includes low-k points; the current frozen strict-branch extraction does not.
- Prefer points with visible error bars; record whether error bars were used as `sigma_omega_over_2pi_kHz`.

## Provenance

When we digitize:
- Record the tool + settings (e.g., WebPlotDigitizer axis calibration points, scaling, export).
- Record any rounding rules (e.g., 4 decimals in k, 3 decimals in kHz).
