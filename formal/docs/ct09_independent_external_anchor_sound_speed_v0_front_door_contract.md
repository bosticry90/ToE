# CT-09 Independent External Anchor Sound-Speed v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-09 independent external-anchor reports.

## Statement (bounded independent external anchor)
Under pinned dataset `Andrews1997_Fig2_DistanceTime_Digitized_v1`, pinned preprocessing, and pinned tolerance profile, a linear sound-speed model reproduces `distance_um_vs_time_ms` within tolerance while a scaled-speed break is explicitly detected.

## Inputs
- Pinned dataset: `formal/external_evidence/ct09_independent_sound_speed_domain_01/distance_vs_time_um_ms.csv`
- Pinned parameters: `c_scale_negative`, `sigma_distance_um`.
- Tolerance profile (pinned by default): `eps_rmse_um`, `eps_max_abs_error_um`, `eps_reduced_chi2`.

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_reference_report.json`
  - `formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_candidate_report.json`

## Report schema
`CT-09/independent_external_anchor_sound_speed_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: dataset_id, dataset_csv_relpath, dataset_csv_sha256, preprocessing_tag, observable_id, fit_model, c_scale_negative, sigma_distance_um, eps_rmse_um, eps_max_abs_error_um, eps_reduced_chi2.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control_model_break).
  - `model_tag`, `c_um_per_ms`, `intercept_um`, `rmse_um`, `max_abs_error_um`, `reduced_chi2`, `n_points`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned dataset and parameters.
- Report fingerprints must match recomputation in the comparator.
- Comparator profile is semantically binding: artifact-declared `eps_*` values must match the active comparator tolerance profile.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.ct09_independent_external_anchor_sound_speed_front_door
```
