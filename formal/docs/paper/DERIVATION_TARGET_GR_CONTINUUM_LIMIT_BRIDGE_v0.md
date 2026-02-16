# Derivation Target: GR Continuum-Limit Bridge v0

Spec ID:
- `DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0`

Target ID:
- `TARGET-GR-CONTINUUM-LIMIT-BRIDGE-v0`

Classification:
- `P-POLICY`

Purpose:
- Define a controlled bridge program from bounded/discrete GR closure surfaces
  to continuum-limit correspondence claims.

Adjudication token:
- `GR_CONTINUUM_LIMIT_ADJUDICATION: NOT_YET_DISCHARGED_v0`

Progress token:
- `GR_CONTINUUM_LIMIT_PROGRESS_v0: CYCLE1_REFINEMENT_TREND_TOKEN_PINNED`

Discharge-criteria token:
- `GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED`

Discharge criteria rows (cycle-010 pinned):
1. `GR_CONTINUUM_LIMIT_CRITERIA_ROW_01_v0: REFINEMENT_TREND_MONOTONIC_PINNED`
- required artifact token:
  - `gr_continuum_refinement_trend_cycle1_v0`

2. `GR_CONTINUUM_LIMIT_CRITERIA_ROW_02_v0: DISCRETE_TO_CONTINUUM_MAP_SURFACE_PINNED`
- required mapping surface:
  - `TARGET-GR-CONTINUUM-MICRO-01-REFINEMENT-TREND-v0`

3. `GR_CONTINUUM_LIMIT_CRITERIA_ROW_03_v0: BOUNDARY_ASSUMPTION_TRANSPARENCY_PINNED`
- required boundary posture token:
  - `no infinite-domain uniqueness claim`

4. `GR_CONTINUUM_LIMIT_CRITERIA_ROW_04_v0: STATE_GATE_SYNC_PINNED`
- required synchronization surfaces:
  - `State_of_the_Theory.md`
  - `formal/python/tests/test_qm_gr_regime_expansion_gate.py`

Criteria evidence artifact token:
- `GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_v0: gr_continuum_discharge_criteria_cycle10_v0`
- `GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0: babb6d8bbe262c7b17f494e0105eabc777f18479ef7e416570d303be448b7fb2`

Criteria evidence artifact pointer:
- `formal/output/gr_continuum_discharge_criteria_cycle10_v0.json`

Scope boundary:
- bridge-program planning surface only.
- no claim of completed continuum-limit theorem in this artifact.
- no infinite-domain uniqueness claim in this artifact.

Required discharge tracks:
1. Refinement consistency track:
- residual behavior is stable under mesh refinement.

2. Discrete-to-continuum mapping track:
- mapping assumptions are explicit and theorem-auditable.

3. Grid-independence sanity track:
- convergence behavior is not tied to a single discretization encoding.

4. Boundary-regime transparency track:
- boundary assumptions remain explicit at every bridge step.

Cycle-001 micro-targets (now pinned):
1. `TARGET-GR-CONTINUUM-MICRO-01-REFINEMENT-TREND-v0`
- artifact token:
  - `gr_continuum_refinement_trend_cycle1_v0`
- artifact pointer:
  - `formal/output/gr_continuum_refinement_trend_cycle1_v0.json`
- scope:
  - lock first deterministic refinement-trend record over bounded grids
    (`32/64/128`) and require monotonic non-increasing residual behavior.

Canonical pointers:
- `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
- `formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md`

Exit criteria (for future adjudication flip):
- continuum-bridge theorem token(s) pinned,
- refinement trend lock artifacts pinned,
- boundary assumptions explicitly preserved,
- adjudication synchronized to `DISCHARGED_v0_CONTINUUM_BRIDGE`.
