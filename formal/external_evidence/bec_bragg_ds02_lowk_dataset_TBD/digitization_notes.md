# DS-02 (low-k) digitization notes

Source
- Paper: Shammass et al. (2012), arXiv:1207.3440v2
- Figure: Fig. 2 (ω_k/2π in Hz vs k in μm⁻¹)

Unit note (important)
- Although the repository CSV column is named `omega_over_2pi_kHz` (legacy schema), the numeric values for DS-02 Fig. 2 are interpreted as **Hz**, not kHz.
- This is grounded in the paper text (e.g., statements of frequencies in Hz for the plotted series).

Digitization protocol (deterministic, audit-friendly)
1. Tool: WebPlotDigitizer (or equivalent) — record the exact version.
1.5. Use the repo-rendered figure image (high resolution):
	- `fig2_page5_z4.png` (rendered from `1207.3440v2.pdf`, page index 5)
2. Axis calibration:
	- X axis: k (μm⁻¹)
	- Y axis: ω_k/2π (Hz)
3. Series selection:
	- Pick exactly one of the two chemical-potential series for DS-02 initial anchoring.
	- Use **filled circles** (higher chemical potential / higher sound speed) only; ignore open circles.
	- Record the legend label verbatim for the filled-circle series.
4. Point selection:
	- Marker rule: pick the **centroid of each filled-circle marker** (do not bias toward the curve).
	- Target ~15–25 points.
	- Ensure dense low-k sampling near k→0 (target ≥10 points with k ≤ 1.5 μm⁻¹).
	- Ensure max(k) reaches at least 3.33842 μm⁻¹ so OV-XD overlap with OV-03x is meaningful.
	- Add extra density for k ≤ 1.0 μm⁻¹ when possible.
5. Export:
	- Export as CSV of (k, ω/2π) with as many significant digits as provided by the digitizer.
	- If visible error bars can be digitized reliably, record them in sigma columns.
	- If error bars are not digitized, leave sigma cells blank and note “error bars not digitized”.
	- Uncertainty placeholder policy: blank sigma fields mean **unknown / not recorded** (not assumed zero).
	- Sort rule (canonical): rows must be sorted by `k_um_inv` ascending.

CSV population workflow (recommended)
1. In WebPlotDigitizer, export the picked points as a 2-column CSV (x,y).
2. Convert the WPD export into the repository DS-02 schema:
	- `python -m formal.python.tools.convert_webplotdigitizer_to_ds02_csv --in <wpd_export.csv>`
3. Run `python -m formal.python.tools.generate_ds02_dr_artifacts --report` for immediate gate feedback.

Repository CSV format
- File: `omega_k_data.csv`
- Required columns (header):
	- `source,figure,k_um_inv,omega_over_2pi_kHz,sigma_k_um_inv,sigma_omega_over_2pi_kHz,notes`

Interpretation
- `k_um_inv` is in μm⁻¹.
- `omega_over_2pi_kHz` values are treated as **Hz** for DS-02 (despite the legacy name), and converted via ω = 2π f.

After digitization
- Freeze the CSV (no further edits without explicit new packet revision).
- Update `data_fingerprint.md` with sha256 and row count.
- Generate DS-02 DR artifacts (same 4-window pattern used for OV-03x/OV-01g) using the existing artifact generator.
