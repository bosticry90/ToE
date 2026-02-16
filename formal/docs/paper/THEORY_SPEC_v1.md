# Theory Spec v1

Spec ID:
- `THEORY_SPEC_v1`

Purpose:
- Provide a paper-facing theory specification that is explicit about model objects, symmetries, conserved quantities, interpretation mapping, and units posture.
- Keep claim posture aligned with governance labels (`T-PROVED`, `T-CONDITIONAL`, `E-REPRO`, `P-POLICY`, `B-BLOCKED`).

Scope and non-claim boundary:
- This specification is a formal model-surface declaration.
- No external truth claim is made.

## 1. Fundamental Degrees of Freedom

- Canonical computational representations: Rep32 and Rep64 bounded surfaces.
- Default formal derivation route is currently Rep32 default quotient path.
- Domain assumptions and boundary surfaces are explicit per lane; no hidden domain promotion is permitted.

## 2. Action / Variational Object

- Paper-facing action surface:
  - `actionRep32.action` and `actionRep32Cubic declared_g_rep32`
  - formal route: `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean`
- Current claim posture:
  - EL/P equality is `T-CONDITIONAL` under explicit default-path assumptions.
- TOE-GR-01 theorem-surface module:
  - `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`

## 3. Symmetry Group Surface

- Structural symmetry closure route:
  - SYM-01 and variational symmetry linkage surfaces.
- Current status:
  - symmetry closure is structurally implemented; physics-level promotion remains scoped and explicit.

## 4. Conserved Quantities / Noether Surface

- Noether-style conserved quantity surface is present in structural form.
- Conserved-quantity physics interpretation remains conditional on action/dynamics closure assumptions.

## 5. Interpretation Map (Model Object -> Observable Role)

| Model object | Paper-facing role | Current status |
|---|---|---|
| `EL_toe_rep32` | Euler-Lagrange operator surface | `T-CONDITIONAL` linkage to `P_cubic_rep32_def` |
| `P_cubic_rep32_def` | Declared cubic update/policy surface | `T-CONDITIONAL` default-path linkage |
| RL/CT observables | bounded correspondence probes | `E-REPRO` only |
| RAC obligations | admissibility/promotion controls | `P-POLICY` |

## 6. Units and Dimensional Analysis Posture

- Units/dimension mapping is currently explicit but not fully promoted to a calibrated SI-ready theorem surface.
- Required outputs for ToE-claim upgrade:
  - units table for primitive and derived quantities,
  - dimensionless control parameters,
  - calibration policy and anchor selection rule.
- Current calibration protocol artifact:
  - `formal/docs/paper/TOE_GR01_KAPPA_CALIBRATION_v0.md`
- GR01 weak-field symbol dictionary surfaces:
  - `formal/docs/paper/TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md`
  - `formal/docs/paper/TOE_GR01_LAPLACIAN_EXTRACTION_v0.md`
  - `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`

## 7. Calibration and Prediction Posture

- Current posture: bounded reproducibility and deterministic comparator evidence.
- Required for ToE-claim upgrade:
  - at least one pinned calibration protocol,
  - at least one quantitative prediction surface with explicit non-claim boundaries.

## 8. Assumption Classification Policy

- `T-PROVED`: theorem-level discharge in Lean.
- `T-CONDITIONAL`: theorem under explicit assumptions.
- `P-POLICY`: declared admissibility principle not yet theorem-promoted.
- `B-BLOCKED`: explicitly not yet discharged; no implied promotion.
- TOE-GR-01 bridge split (v0):
  - `ProjectionMapWellFormed` -> `T-CONDITIONAL` via `GR01SymmetryPromotion.lean`
  - `WeakFieldScalingHierarchy` / `HigherOrderTermsNegligible` -> `T-CONDITIONAL` via `GR01ScalingPromotion.lean`
  - `WeakFieldTruncationSound` -> theorem-surface bridge component remains explicit
  - `OperatorToDiscreteResidual` -> `T-CONDITIONAL` target
  - `ELImpliesDiscretePoissonResidual` -> `T-CONDITIONAL` via `GR01BridgePromotion.lean`
  - end-to-end theorem-chain composition -> `T-CONDITIONAL` via `GR01EndToEndClosure.lean`
  - solver-elimination promotion rule (Track B):
    - rows with explicit solver assumptions may be promoted to `T-PROVED` when theorem statements
      eliminate explicit candidate-field input (`Φ`) and expose existential output (`∃ Φ` / `∃! Φ`)
      under pinned non-claim boundaries.
  - publication-grade derivation gate (v0 policy):
    - `T-PROVED` theorem shape is not sufficient by itself for publication-grade derivation claims.
    - publication-grade promotion requires closure of:
      - `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md`
      - target ID: `TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN`
    - gate layers required for closure:
      - analytic discharge completeness,
      - mainstream equivalence proof,
      - assumption minimization audit,
      - literature alignment mapping.
  - reference: `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
  - closure target pointer: `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`

Current dominant blocker:
- Full-derivation discharge remains open even though derivation-grade governance
  package rows are synchronized.
- Default-route weak-field GR01 still carries placeholder/axiomatic and
  bridge-promotion dependencies that prevent "action alone implies Poisson"
  discharge.
- Canonical blocker inventory pointer:
  `formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`.

## 9. 3D Posture And Falsifiability (GR01 Weak-Field)

- 3D reporting posture token:
  - `nabla_3D^2 Phi = kappa * rho`
- Lean posture tokens:
  - `DiscreteLaplacian3D`
  - `DiscretePoissonResidual3D`
  - `PoissonEquation3D`
- 3D mapping assumptions + conditional lift theorem tokens:
  - `Separable3DMappingAssumptions`
  - `poissonEquation3D_of_componentwise_poissonEquation1D_under_separable`
- embedding-example 3D mapping tokens:
  - `Lift1DTo3DMappingAssumptions`
  - `poissonEquation3D_of_poissonEquation1D_under_lift_x_only`
- Falsifiability hooks:
  - failure of first-order weak-field remainder suppression invalidates GR01 scoped derivation claims,
  - failure of units consistency (`Phi`, `rho`, `kappa`) invalidates interpretation-layer claims,
  - undocumented removal of action/RAC dependencies invalidates conditional-derivation posture.
- Action/RAC stance policy pointer:
  - `formal/docs/paper/TOE_GR01_ACTION_RAC_STANCE_v0.md`
- Minimal conservation compatibility blocker pointer:
  - `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md`
