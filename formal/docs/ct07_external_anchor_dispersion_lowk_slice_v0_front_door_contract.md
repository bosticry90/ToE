# CT-07 External Anchor Dispersion Low-k Slice v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-07 external-anchor low-k slice dispersion reports from the pinned CT-06 origin dataset.

## Statement (bounded external anchor)
Given origin dataset `Steinhauer2001_Fig3a_Digitized_v1` and pinned low-k slice preprocessing, the candidate model must reproduce `omega_over_2pi_kHz_vs_k_um_inv` within tolerance or fail.

## Inputs
- Origin dataset CSV:
  - `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv`
- Dataset metadata:
  - `formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01/dataset_metadata.json`
- Tolerance profile (pinned by default):
  - `eps_rmse_kHz`, `eps_max_abs_error_kHz`, `eps_reduced_chi2`
- Pinned low-k slice controls:
  - `k_quantile`, computed `k_max_um_inv`
- Negative-control break:
  - `c_s2_scale_negative`

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01/ct07_reference_report.json`
  - `formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01/ct07_candidate_report.json`

## Report schema
`CT-07/external_anchor_dispersion_lowk_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: origin_dataset_id, origin_dataset_csv_relpath, origin_dataset_csv_sha256, preprocessing_tag, observable_id, fit_model, k_quantile, k_max_um_inv, n_slice_points, c_s2_scale_negative, eps_rmse_kHz, eps_max_abs_error_kHz, eps_reduced_chi2, non_independent_of_ct06.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control_model_break), `model_tag`.
  - `c_s2_kHz2_um2`, `alpha_kHz2_um4`, `c_s2_scale`.
  - `rmse_kHz`, `max_abs_error_kHz`, `reduced_chi2`, `n_points`.
- `fingerprint`: sha256 of report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned inputs and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.ct07_external_anchor_dispersion_lowk_front_door
```

