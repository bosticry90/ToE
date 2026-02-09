# OV-04x — Fit-family robustness on DS-02 low-k external dataset (locked)

This lock records the **DS-02 low-k external dataset** robustness-only evaluation.

Scope / limits
- Low-k dataset; does not generalize; no continuity claim.
- Robustness-only; no physics claim.
- β-null posture: β not inferred / compatible with 0.

Source (designated)
- Shammass et al. (2012), arXiv:1207.3440v2
- Local PDF: `formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/1207.3440v2.pdf`
- Figure: Fig. 2 (ω_k/2π vs k)

Digitization / units

- CSV: `formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv`
	- sha256: `f6d620fb7da9ec199953bed628dc72a98c74d0baa5bb52e78744ea398a2b8b9b`
	- rows: 25
- Series selection: Fig. 2 **filled circles** only (ignore open circles).

Window artifacts used (deterministic)

All artifacts are generated via `formal/python/tools/generate_ds02_dr_artifacts.py` from the frozen CSV.

- Linear (through-origin) artifacts: dr01/dr03/dr04d/dr05
- Curved artifacts (proxy ω/k = c0 + βk²): dr01/dr03/dr04d/dr05

OV-04x result (robustness-only)

Computed with `formal/python/toe/observables/ov04_fit_family_robustness_lowk_ds02.py` under `DQ-01_v1`: 

```json
{
  "adequacy_policy": "DQ-01_v1",
  "config_tag": "OV-04x_fit_family_robustness_v1",
  "curved_adequacy_passes": true,
  "curved_report_fingerprint": "d96540bd2e04976ad8586d5bd450b9fdcf9e266a4f564e45a6e9e3ad265c876b",
  "fn_fingerprint": "e7777a6932478ade74e4a8463a5ed023fa238a85a394c5135c1c7c001c32156d",
  "linear_report_fingerprint": "eec56c66668bb1dd2b4f7b1465f030410211c1b2dfc9910bb69efca7bff1cc42",
  "prefer_curved": true,
  "q_ratio": 0.8060220497327952,
  "q_threshold": 0.9,
  "r_max_curved": 0.7172088910074628,
  "r_max_linear": 0.8898129911523203,
  "r_rms_curved": 0.49620379974101825,
  "r_rms_linear": 0.6711592690599215,
  "robustness_failed": false
}
```

Report fingerprint: `f562944bc70ff2f892d571cb70627aa2e749dc6ef18dd031358eb17e54930915`
