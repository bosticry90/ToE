# OV-03x — Fit-family robustness on B1 second external dataset (locked)

This lock records the **B1 second external dataset** robustness-only evaluation.

Scope / limits
- Robustness-only; no physics claim.
- Dataset-specific; no continuity claim.
- β-null posture: β not inferred / compatible with 0.

Source (designated)
- Ernst et al. (2009), arXiv:0908.4242v1
- Local PDF: `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/0908.4242v1.pdf`
- Figure: Fig2a (ω/2π vs kBragg-converted)

Digitization / units

- CSV: `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv`
	- sha256: `088acb258716352bb141eae080fdc22fc5e4ab52f10ee2ebf2c94ba14538f216`
	- rows: 17
- Units: omega_over_2pi_kHz treated as kHz; omega = 2*pi*f.

Window artifacts used (deterministic)

All artifacts are generated via `formal/python/tools/generate_b1_dr_artifacts.py` from the frozen CSV.

- Linear (through-origin) artifacts: dr01/dr03/dr04d/dr05
- Curved artifacts (proxy ω/k = c0 + βk²): dr01/dr03/dr04d/dr05

OV-03x result (robustness-only)

Computed with `formal/python/toe/observables/ov03_fit_family_robustness.py` under `DQ-01_v2` with q_threshold=1.05: 

```json
{
  "adequacy_policy": "DQ-01_v2",
  "config_tag": "OV-03x_fit_family_robustness_DQ-01_v2_q1.05",
  "curved_adequacy_passes": true,
  "curved_report_fingerprint": "c5ad595d8df8c87c1b77018c6f868734c4c15725ec40d2441ea17a6c160b9cb3",
  "fn_fingerprint": "e7777a6932478ade74e4a8463a5ed023fa238a85a394c5135c1c7c001c32156d",
  "linear_report_fingerprint": "a1c505c54bb88ec7dbf2610762ce155cd36a39de1ba3c123dff3381793bd2df8",
  "prefer_curved": true,
  "q_ratio": 1.0241440175459013,
  "q_threshold": 1.05,
  "r_max_curved": 0.6107718647646012,
  "r_max_linear": 0.596373024009025,
  "r_rms_curved": 0.4172330239719786,
  "r_rms_linear": 0.4047134015392832,
  "robustness_failed": false
}
```

Report fingerprint: `f91cdb2b743de43903a1e28b0503d7ac4da8eea713e56682b79db54a2b4ce0bb`
