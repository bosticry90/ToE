# Structural Closeness Map v0

Spec ID:
- `STRUCTURAL_CLOSENESS_MAP_v0`

Classification:
- `P-POLICY`

Purpose:
- planning-only coverage map for structural overlap against mainstream-physics pillars.
- non-claim roadmap artifact for prioritization and scope hygiene.
- input to gating and roadmap language only.

Non-claim boundary:
- This artifact is planning-only.
- This artifact is a non-claim and non-evidence surface.
- This artifact does not promote any claim label or theorem status.
- This artifact does not substitute for derivations, proofs, or reproducibility artifacts.

Legend:
- `T-CONDITIONAL`: theorem surface under explicit assumptions.
- `E-REPRO`: deterministic evidence/lock surface.
- `P-POLICY`: declared modeling/planning posture.
- `B-BLOCKED`: explicit missing discharge target.
- `ABSENT`: structural object is not currently present on the canonical surface.

## Coverage Matrix

| Pillar ID | Structural object | Current status | Claim/Target ID | Canonical artifact pointer | Closure definition |
|---|---|---|---|---|---|
| `PILLAR-CFT` | state | `T-CONDITIONAL` | `FV-EL-01` | `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean` | Keep default-quotient assumptions explicit and auditable. |
| `PILLAR-CFT` | evolution rule | `T-CONDITIONAL` | `FV-EL-01` | `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean` | Derivation remains assumption-scoped until promotion artifacts exist. |
| `PILLAR-CFT` | action / variational object | `T-CONDITIONAL` | `FV-EL-01` | `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean` | Preserve non-tautological EL/P route and lock pointers. |
| `PILLAR-CFT` | symmetry machinery | `P-POLICY` | `TOE-SPEC-01` | `formal/docs/paper/THEORY_SPEC_v1.md` | Upgrade only via explicit theorem surfaces, not planning text. |
| `PILLAR-CFT` | conservation laws | `P-POLICY` | `TOE-SPEC-01` | `formal/docs/paper/THEORY_SPEC_v1.md` | Keep conservation map as declared structure until theorem discharge. |
| `PILLAR-CFT` | limit recoveries | `T-CONDITIONAL` | `TOE-GR-DER-01` | `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md` + `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean` | Weak-field scaffold chain is theorem-conditional under explicit assumptions; derivation-grade package remains open. |
| `PILLAR-CFT` | measurement/data anchoring | `E-REPRO` | `TOE-GR-CAL-01` | `formal/docs/paper/TOE_GR01_KAPPA_CALIBRATION_v0.md` | Deterministic lock remains support-only and non-claim. |
| `PILLAR-SR` | state | `P-POLICY` | `TOE-SR-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | Add explicit theorem surface before any posture upgrade. |
| `PILLAR-SR` | evolution rule | `E-REPRO` | `TOE-SR-01` | `formal/docs/rl12_lorentz_poincare_invariance_proxy_lane_spec.md` | Proxy evidence remains bounded-support only. |
| `PILLAR-SR` | action / variational object | `ABSENT` | `TOE-SR-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No canonical SR action object yet on theorem path. |
| `PILLAR-SR` | symmetry machinery | `P-POLICY` | `TOE-SR-01` | `formal/docs/rl12_lorentz_poincare_invariance_proxy_lane_spec.md` | Promote via explicit invariance theorem contract. |
| `PILLAR-SR` | conservation laws | `ABSENT` | `TOE-SR-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No SR conservation theorem surface yet. |
| `PILLAR-SR` | limit recoveries | `E-REPRO` | `TOE-SR-01` | `formal/docs/rl12_lorentz_poincare_invariance_proxy_lane_spec.md` | Keep as bounded proxy until derivation target is frozen. |
| `PILLAR-SR` | measurement/data anchoring | `ABSENT` | `TOE-SR-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No independent SR anchoring protocol declared. |
| `PILLAR-QM` | state | `P-POLICY` | `TOE-QM-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | Keep QM theorem target explicit but not claimed. |
| `PILLAR-QM` | evolution rule | `T-CONDITIONAL` | `TOE-QM-THM-01` | `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` | Contract theorem exists under explicit assumptions; derivational recovery remains out of scope. |
| `PILLAR-QM` | evolution rule (planning-pointer) | `P-POLICY` | `TARGET-QM-EVOL-PLAN` | `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md` | Frozen planning artifact retained for scope boundaries after theorem promotion checkpoint. |
| `PILLAR-QM` | action / variational object | `P-POLICY` | `TOE-QM-01` | `formal/docs/paper/THEORY_SPEC_v1.md` | Promote only when QM theorem-surface assumptions are frozen. |
| `PILLAR-QM` | symmetry machinery | `P-POLICY` | `TOE-QM-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No theorem-grade QM symmetry discharge yet. |
| `PILLAR-QM` | symmetry machinery (planning-pointer) | `P-POLICY` | `TARGET-QM-SYMM-PLAN` | `formal/docs/paper/DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md` | Frozen planning target defines typed QM symmetry objects and invariance contract without claim promotion. |
| `PILLAR-QM` | conservation laws | `ABSENT` | `TOE-QM-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | QM conservation theorem surface not present. |
| `PILLAR-QM` | limit recoveries | `E-REPRO` | `TOE-QM-01` | `formal/docs/nonrelativistic_limit_nlse_lane_spec.md` | Bounded lane is support-only and not derivation closure. |
| `PILLAR-QM` | measurement/data anchoring | `ABSENT` | `TOE-QM-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | Born-like measurement layer is not formalized on the theorem surface. |
| `PILLAR-QM` | measurement/data anchoring (planning-pointer) | `P-POLICY` | `TARGET-QM-MEAS-PLAN` | `formal/docs/paper/DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md` | Frozen planning target defines minimal typed objects and closure criteria without claim promotion. |
| `PILLAR-QFT` | state | `ABSENT` | `TOE-QFT-PLAN-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No canonical QFT theorem target is active. |
| `PILLAR-QFT` | evolution rule | `ABSENT` | `TOE-QFT-PLAN-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No quantized field evolution surface on main path. |
| `PILLAR-QFT` | evolution rule (planning-pointer) | `P-POLICY` | `TARGET-QFT-EVOL-PLAN` | `formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md` | Frozen planning target defines typed QFT evolution objects and contract surface without claim promotion. |
| `PILLAR-QFT` | action / variational object | `ABSENT` | `TOE-QFT-PLAN-01` | `formal/docs/paper/THEORY_SPEC_v1.md` | No QFT action layer with local gauge structure yet. |
| `PILLAR-QFT` | symmetry machinery | `ABSENT` | `TOE-QFT-PLAN-01` | `formal/docs/paper/THEORY_SPEC_v1.md` | No U(1)/SU(2)/SU(3) theorem-grade symmetry surface. |
| `PILLAR-QFT` | symmetry machinery (planning-pointer) | `P-POLICY` | `TARGET-QFT-GAUGE-PLAN` | `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md` | Frozen planning target defines typed gauge objects and invariance contract without claim promotion. |
| `PILLAR-QFT` | conservation laws | `ABSENT` | `TOE-QFT-PLAN-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No QFT conservation closure artifact present. |
| `PILLAR-QFT` | limit recoveries | `ABSENT` | `TOE-QFT-PLAN-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No SM/QFT recovery target has been frozen. |
| `PILLAR-QFT` | measurement/data anchoring | `ABSENT` | `TOE-QFT-PLAN-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No QFT empirical anchoring program is declared. |
| `PILLAR-GR` | weak-field potential state (bounded) | `P-POLICY` | `TOE-GR-01` | `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md` | Keep weak-field modeling assumptions explicit in theorem signature. |
| `PILLAR-GR` | evolution rule | `T-CONDITIONAL` | `TOE-GR-DER-01` | `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md` + `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean` | Weak-field expansion/potential/laplacian scaffold bundle is theorem-conditional under explicit assumptions; derivation-grade package remains open. |
| `PILLAR-GR` | evolution rule (planning-pointer) | `P-POLICY` | `TARGET-GR01-REG-PROMO-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md` | Frozen weak-field regime-promotion target with no-lane-expansion guarantee. |
| `PILLAR-GR` | action / variational object | `T-CONDITIONAL` | `TOE-GR-THM-01` | `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean` | Maintain non-vacuous theorem surface under explicit assumptions. |
| `PILLAR-GR` | symmetry machinery | `T-CONDITIONAL` | `TOE-GR-SYM-01` | `formal/toe_formal/ToeFormal/Variational/GR01SymmetryPromotion.lean` | Projection-map well-formedness is theorem-conditional under explicit carrier/regime assumptions. |
| `PILLAR-GR` | symmetry machinery (planning-pointer) | `P-POLICY` | `TARGET-GR-GEOM-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md` | Frozen planning target defines typed geometry objects and invariance contract without claim promotion. |
| `PILLAR-GR` | conservation laws | `ABSENT` | `TOE-GR-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No GR conservation theorem family in canonical lane. |
| `PILLAR-GR` | conservation compatibility (weak-field) | `T-CONDITIONAL` | `TOE-GR-CONS-01` | `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md` + `formal/toe_formal/ToeFormal/GR/ConservationContract.lean` | Bridge-composed conservation compatibility is theorem-conditional under weak-field/default-quotient assumptions; full conservation theorem family remains future-scoped. |
| `PILLAR-GR` | conservation laws (planning-pointer) | `P-POLICY` | `TARGET-GR-CONS-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md` | Frozen planning target defines typed GR conservation objects and contract surface without claim promotion. |
| `PILLAR-GR` | 3D weak-field mapping (embedding example) | `T-CONDITIONAL` | `TOE-GR-3D-01` | `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean` | Conditional x-only lift maps 1D residual closure to 3D residual posture as an embedding example only. |
| `PILLAR-GR` | 3D weak-field mapping (separable) | `T-CONDITIONAL` | `TOE-GR-3D-02` | `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean` | Conditional separable 3D mapping is pinned as improved 3D posture beyond x-only embedding. |
| `PILLAR-GR` | 3D weak-field mapping (mainstream-class gate) | `T-CONDITIONAL` | `TOE-GR-3D-03` | `formal/docs/paper/DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md` + `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md` + `formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md` + `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean` + `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean` | Closure is satisfied under v0 bounded/discrete interpretation via synchronized Track A mapping-bridge tokens and Track B solver/existential closure tokens (`ADJUDICATION: SATISFIED_v0_DISCRETE`); non-claim boundaries remain explicit. |
| `PILLAR-GR` | limit recoveries | `T-CONDITIONAL` | `TOE-GR-DER-02` | `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md` + `formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md` | Derivation-grade analytic package and action/RAC alignment are conditional-discharge synchronized under explicit weak-field/default-quotient scope; conservation compatibility is tracked separately via `TOE-GR-CONS-01`. |
| `PILLAR-GR` | limit recoveries (planning-pointer) | `P-POLICY` | `TARGET-GR01-BRIDGE-PROMO-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md` | Frozen blocker-focused bridge-promotion target with no-lane-expansion guarantee. |
| `PILLAR-GR` | end-to-end closure criteria (planning-pointer) | `P-POLICY` | `TARGET-GR01-END2END-CLOSURE-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md` | Frozen end-to-end theorem-chain closure audit target; no-lane-expansion guarantee remains in force. |
| `PILLAR-GR` | derivation-grade discharge checklist (planning-pointer) | `P-POLICY` | `TARGET-GR01-DERIV-CHECKLIST-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md` | Frozen checklist target for scaffold-to-discharge upgrades and action/RAC retirement alignment under unchanged scope. |
| `PILLAR-GR` | approximation hierarchy (planning-pointer) | `P-POLICY` | `TARGET-GR01-SCALING-PROMO-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md` | Frozen blocker-focused scaling-promotion target with no-lane-expansion guarantee. |
| `PILLAR-GR` | projection consistency (planning-pointer) | `P-POLICY` | `TARGET-GR01-SYM-PROMO-PLAN` | `formal/docs/paper/DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md` | Frozen blocker-focused symmetry-promotion target with no-lane-expansion guarantee. |
| `PILLAR-GR` | measurement/data anchoring | `E-REPRO` | `TOE-GR-CAL-01` | `formal/output/toe_gr01_kappa_calibration_v0.json` | Lock-pinned calibration remains support-only. |
| `PILLAR-STAT` | state | `P-POLICY` | `TOE-TH-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | Keep thermodynamic target explicit and non-claim. |
| `PILLAR-STAT` | evolution rule | `E-REPRO` | `TOE-TH-01` | `formal/docs/rl10_entropy_balance_lane_spec.md` | Comparator lane is bounded-support only. |
| `PILLAR-STAT` | action / variational object | `ABSENT` | `TOE-TH-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No entropy-balance action theorem surface yet. |
| `PILLAR-STAT` | symmetry machinery | `ABSENT` | `TOE-TH-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No theorem-grade thermodynamic symmetry layer. |
| `PILLAR-STAT` | conservation laws | `P-POLICY` | `TOE-SPEC-01` | `formal/docs/paper/THEORY_SPEC_v1.md` | Conservation posture remains specification-level. |
| `PILLAR-STAT` | limit recoveries | `E-REPRO` | `TOE-TH-01` | `formal/docs/rl10_entropy_balance_lane_spec.md` | Keep as bounded correspondence only. |
| `PILLAR-STAT` | measurement/data anchoring | `ABSENT` | `TOE-TH-01` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | No thermodynamic anchoring protocol is pinned. |

## Frozen Structural-Object Targets (Planning Controls)

- `TARGET-QM-MEAS-PLAN`: measurement/probability semantics surface (status path `ABSENT` -> `P-POLICY` -> `T-CONDITIONAL`), frozen by `formal/docs/paper/DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md`.
- `TARGET-QM-EVOL-PLAN`: QM evolution-object planning artifact retained after promotion checkpoint (`TOE-QM-THM-01`); frozen by `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md`.
- `TARGET-QM-SYMM-PLAN`: QM symmetry-object surface (status path `ABSENT` -> `P-POLICY` -> `T-CONDITIONAL`), frozen by `formal/docs/paper/DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md`.
- `TARGET-QFT-EVOL-PLAN`: QFT evolution-object surface (status path `ABSENT` -> `P-POLICY` -> `T-CONDITIONAL`), frozen by `formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md`.
- `TARGET-QFT-GAUGE-PLAN`: local gauge-group structure surface (status path `ABSENT` -> `P-POLICY` -> `T-CONDITIONAL`), frozen by `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md`.
- `TARGET-GR-GEOM-PLAN`: metric/diffeomorphism object surface (status path `ABSENT` -> `P-POLICY` -> `T-CONDITIONAL`), frozen by `formal/docs/paper/DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md`.
- `TARGET-GR-CONS-PLAN`: conservation-object surface (status path `ABSENT` -> `P-POLICY` -> `T-CONDITIONAL`), frozen by `formal/docs/paper/DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md`.
- `TOE-GR-CONS-01`: minimal weak-field conservation-compatibility surface promoted to theorem-conditional status under explicit bridge assumptions, pinned by `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md`.
- `TARGET-GR01-3D-03-PLAN`: mainstream-class 3D closure gate target (spherical/Green-class), frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md` with Track A partial theorem-surface pointer `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean` and Track B point-source pointer `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`.
- `TARGET-GR01-3D-POINT-SOURCE-PLAN`: Track B bounded point-source-class closure sub-target, frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`.
- `TARGET-GR01-BRIDGE-PROMO-PLAN`: GR01 modeling-bridge promotion surface for `ASM-GR01-APP-02`, frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md`.
- `TARGET-GR01-REG-PROMO-PLAN`: GR01 weak-field regime-promotion surface for `ASM-GR01-REG-01`, frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md`.
- `TARGET-GR01-SCALING-PROMO-PLAN`: GR01 first-order scaling-promotion surface for `ASM-GR01-APP-01`, frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md`.
- `TARGET-GR01-SYM-PROMO-PLAN`: GR01 projection-map/symmetry-promotion surface for `ASM-GR01-SYM-01`, frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md`.
- `TARGET-GR01-END2END-CLOSURE-PLAN`: GR01 end-to-end theorem-chain closure audit surface, frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md`.
- `TARGET-GR01-DERIV-CHECKLIST-PLAN`: GR01 derivation-grade discharge checklist surface, frozen by `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`.

Promotion rule:
- Any upgrade from this map must go through canonical theorem/evidence artifacts and claim-taxonomy gates.
- No row in this map can directly change claim labels in `RESULTS_TABLE_v0.md`.
