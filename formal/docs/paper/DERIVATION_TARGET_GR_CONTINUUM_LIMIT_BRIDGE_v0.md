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
- `GR_CONTINUUM_LIMIT_ADJUDICATION: DISCHARGED_v0_CONTINUUM_BRIDGE`

Progress token:
- `GR_CONTINUUM_LIMIT_PROGRESS_v0: CYCLE1_REFINEMENT_TREND_TOKEN_PINNED`
- `GR_CONTINUUM_LIMIT_PROGRESS_CYCLE2_v0: GRID_INDEPENDENCE_SANITY_TOKEN_PINNED`
- `GR_CONTINUUM_LIMIT_PROGRESS_CYCLE3_v0: BRIDGE_THEOREM_SURFACE_TOKEN_PINNED`

Bounded scientific increment (2026-03-25):
- `GR_CONTINUUM_SCI_INCREMENT_20260325_STATUS_v0: RESIDUAL_ORDER_ESTIMATE_PINNED_NONCLAIM`
- `GR_CONTINUUM_SCI_INCREMENT_20260325_ARTIFACT_v0: gr_continuum_science_increment_20260325_v0`
- artifact pointer:
  - `formal/output/gr_continuum_science_increment_20260325_v0.json`
- mathematical closure payload:
  - `GR_CONTINUUM_RESIDUAL_ORDER_MODEL_v0: E_H_LEQ_C_TIMES_H_POWER_P_ON_BOUNDED_DOMAINS`
  - `GR_CONTINUUM_RESIDUAL_ORDER_ESTIMATE_v0: P_APPROX_2_FROM_TWO_LEVEL_REFINEMENT_RATIO`
  - `GR_CONTINUUM_REFINE_RATIO_WITNESS_v0: E_1_OVER_32_OVER_E_1_OVER_64_APPROX_4_AND_E_1_OVER_64_OVER_E_1_OVER_128_APPROX_4`
  - `GR_CONTINUUM_BOUNDARY_SCOPE_v0: NO_INFINITE_DOMAIN_OR_SINGULAR_SOURCE_COMPLETION_CLAIM`

Bounded W2 continuation increment (2026-03-25):
- `GR_W2_CONTINUATION_INCREMENT_20260325_STATUS_v0: BOUNDED_W2_CONTINUATION_INCREMENT_PINNED_NONCLAIM`
- `GR_W2_CONTINUATION_INCREMENT_20260325_ARTIFACT_v0: gr_w2_continuum_regularity_increment_20260325_v0`
- artifact pointer:
  - `formal/output/gr_w2_continuum_regularity_increment_20260325_v0.json`
- continuation payload:
  - `GR_W2_RESIDUAL_ORDER_STABILITY_v0: FOUR_LEVEL_REFINEMENT_RATIO_AND_P_WINDOW_PINNED`
  - `GR_W2_ROUTE_TO_EVIDENCE_STEP_v0: LOCAL_H1_BOUND_AND_WEAK_GRADIENT_CAUCHY_TEMPLATE_LINKED_NONCLAIM`

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
- `GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0: aefe5054b14554a3e3ec1607f27558002e2faab8a6e0b06bd13b90329ecf83e8`

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

Cycle-002 micro-targets (now pinned):
1. `TARGET-GR-CONTINUUM-MICRO-02-GRID-INDEPENDENCE-SANITY-v0`
- artifact token:
  - `gr_continuum_grid_independence_cycle2_v0`
- artifact pointer:
  - `formal/output/gr_continuum_grid_independence_cycle2_v0.json`
- scope:
  - lock first deterministic grid-independence sanity record across
    non-isomorphic bounded encodings while preserving bounded-domain assumptions.

Cycle-003 micro-targets (now pinned):
1. `TARGET-GR-CONTINUUM-MICRO-03-BRIDGE-THEOREM-SURFACE-v0`
- artifact token:
  - `gr_continuum_bridge_theorem_surface_cycle3_v0`
- artifact pointer:
  - `formal/output/gr_continuum_bridge_theorem_surface_cycle3_v0.json`
- scope:
  - lock first continuum-bridge theorem-surface registry with explicit
    bounded-domain assumptions, mapping hypotheses, and discharge-route hooks.

Canonical pointers:
- `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`
- `formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md`

Exit criteria (for future adjudication flip):
- continuum-bridge theorem token(s) pinned,
- refinement trend lock artifacts pinned,
- boundary assumptions explicitly preserved,
- adjudication synchronized to `DISCHARGED_v0_CONTINUUM_BRIDGE`.
