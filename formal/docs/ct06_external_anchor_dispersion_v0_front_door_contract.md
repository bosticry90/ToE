# CT-06 External Anchor Dispersion v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-06 external-anchor dispersion reports from the pinned in-repo dataset and preprocessing assumptions.

## Statement (bounded external anchor)
Given dataset `Steinhauer2001_Fig3a_Digitized_v1` and pinned preprocessing assumptions, a candidate model must reproduce `omega_over_2pi_kHz_vs_k_um_inv` within tolerance; otherwise it fails.

## Inputs
- Dataset CSV:
  - `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/dispersion_anchor_steinhauer_fig3a_omega_k.csv`
- Dataset metadata:
  - `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/dataset_metadata.json`
- Tolerance profile (pinned by default):
  - `eps_rmse_kHz`, `eps_max_abs_error_kHz`, `eps_reduced_chi2`
- Pinned preprocessing:
  - finite-row filter, ascending `k_um_inv` sort, no unit conversion.
- Negative-control break:
  - `alpha_scale_negative`.

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_reference_report.json`
  - `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_candidate_report.json`

## Report schema
`CT-06/external_anchor_dispersion_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: dataset_id, dataset_csv_relpath, dataset_csv_sha256, preprocessing_tag, observable_id, fit_model, alpha_scale_negative, eps_rmse_kHz, eps_max_abs_error_kHz, eps_reduced_chi2.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control_model_break), `model_tag`.
  - `c_s2_kHz2_um2`, `alpha_kHz2_um4`.
  - `rmse_kHz`, `max_abs_error_kHz`, `reduced_chi2`, `n_points`.
- `fingerprint`: sha256 of report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned inputs and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.ct06_external_anchor_dispersion_front_door
```

