# CT-09 Independent External Anchor Sound-Speed v0

Status: Pinned (v0)

Purpose
- Establish the first independent external-anchor lane beyond the CT-06/07/08 family.
- Use a pinned distance-time dataset to test sound-speed fit reproducibility.
- Keep claim scope bounded to deterministic dataset-conditional reproducibility only.

Statement (bounded independent external anchor)
- Given dataset `Andrews1997_Fig2_DistanceTime_Digitized_v1` and pinned preprocessing assumptions, the candidate linear speed model must reproduce `distance_um_vs_time_ms` within CT-09 tolerances; otherwise it fails.

Independence declaration
- CT-09 is independent of CT-06/CT-07/CT-08 source rows.
- CT-06 family root dataset is `Steinhauer2001_Fig3a_Digitized_v1` (Bragg dispersion).
- CT-09 dataset is distance-time propagation from `bec_sound_andrews_1997`.

Dataset anchor
- Dataset identifier: `Andrews1997_Fig2_DistanceTime_Digitized_v1`.
- Dataset path: `formal/external_evidence/ct09_independent_sound_speed_domain_01/distance_vs_time_um_ms.csv`.

Pinned preprocessing assumptions
- Read typed columns `time_ms`, `distance_um`.
- Drop non-finite rows.
- Sort rows by `time_ms` ascending.
- Keep units unchanged (`time` in ms, `distance` in um).

Controls (expectation-aware)
- Positive control: least-squares fit on `distance_um = c*time_ms + intercept_um`.
- Negative control: apply pinned model break (`c_scale_negative = 0.5`) and require explicit failure detection.

Pinned tolerances and pass/fail semantics
- `eps_rmse_um = 30.0`.
- `eps_max_abs_error_um = 50.0`.
- `eps_reduced_chi2 = 2.8`.
- Comparator profile is semantically binding: artifact-declared `eps_*` values must match active comparator tolerances.
- Positive control passes when all tolerance checks are satisfied.
- Negative control passes only when at least one tolerance is violated and failure is detected.

Required vocabulary
- CT-09
- independent external anchor
- distance_um_vs_time_ms
- Andrews1997_Fig2_DistanceTime_Digitized_v1
- positive control
- negative control
- eps_rmse_um
- eps_max_abs_error_um
- eps_reduced_chi2
- external_anchor_only
