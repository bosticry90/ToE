# Source citation

This folder pins external evidence used for CT-09 independent sound-speed anchor checks.

- Primary pinned source family: `formal/external_evidence/bec_sound_andrews_1997`
  - Kavoulakis & Pethick (1997), arXiv:9711224v1
  - Title: "Sound Propagation in Elongated Bose-Einstein Condensed Clouds"
  - Includes references to Andrews et al. sound-propagation measurements.

Pinned derived dataset for CT-09
- `distance_vs_time_um_ms.csv`
  - Deterministically copied from:
    `formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares.csv`
  - Columns: `time_ms`, `distance_um`

Independence statement
- This CT-09 lane is independent of CT-06/CT-07/CT-08 source rows and processing.
- CT-06 family anchors Bragg dispersion (`k_um_inv`, `omega_over_2pi_kHz`).
- CT-09 anchors distance-time propagation (`time_ms`, `distance_um`).
