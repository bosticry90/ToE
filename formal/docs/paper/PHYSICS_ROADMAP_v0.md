# Physics Roadmap v0

Spec ID:
- `PHYSICS_ROADMAP_v0`

Classification:
- `P-POLICY`

Purpose:
- Define an authoritative, physics-first multi-pillar completion roadmap.
- Enforce sequencing so governance does not drift away from physics closure work.
- Pin per-pillar target IDs, artifact pointers, and minimum publishable closure criteria.

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- no comparator-lane authorization by itself.
- no external truth claim.

Status semantics:
- `ACTIVE`: currently authorized pillar execution lane.
- `LOCKED`: target exists but prerequisites are not yet closed.
- `CLOSED`: closure criteria are satisfied under pinned scope.

Blocker discharge-attempt semantics (active-pillar blockers):
- `B-AWAITING-DISCHARGE-ATTEMPT`: blocker has a frozen promotion hypothesis/mechanism,
  but no recorded discharge-attempt cycle.
- `B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN`: discharge attempt cycle executed with pinned artifacts,
  but promotion theorem is not yet proven/discharged.
- blocking without any recorded attempt cycle under a defined discharge path is a governance failure.

Promotion attempt trigger and execution requirement:
- if a blocker has `Discharge path defined = YES`, an attempt cycle must be recorded.
- each blocker row in the promotion-attempt log must pin:
  - promotion hypothesis,
  - promotion mechanism,
  - promotion attempt cycle,
  - attempt status,
  - discharge-path flag,
  - discharge scaffold module pointer.
  - next promotion objective theorem token.
  - bounded attempt-package target/artifact pointer when the blocker is `TOE-GR-3D-03`.
  - closure-package target/artifact pointer when the blocker is `TOE-GR-3D-03`.
- blockers may remain unproven, but not attempt-free when a discharge path is defined.

Derivation completeness gate semantics (publication-grade tier):
- `T-PROVED` can certify theorem-level closure under explicit assumptions, but does not by itself certify publication-grade derivation completeness.
- publication-grade promotion requires `DERIVATION_COMPLETENESS_GATE` closure via:
  - analytic discharge completeness,
  - mainstream equivalence proof,
  - assumption minimization audit,
  - literature alignment mapping.
- canonical GR01 gate target:
  - `TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN`
  - `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md`

No-deviation sequencing rule:
- At most one pillar may be `ACTIVE` at a time.
- During v0, `PILLAR-GR` is the only allowed `ACTIVE` pillar until
  full-derivation + governance closure surfaces are discharged.
- A pillar may become `ACTIVE` only when all prerequisite target IDs are `CLOSED`.
- No pillar may be marked `CLOSED` without its required artifact set and closure criteria tokens.
- Post-GR01 unlock queue (frozen order intent):
  - first unlock cohort: `PILLAR-SR` and `PILLAR-EM` after `TARGET-GR01-DERIV-CHECKLIST-PLAN` is `CLOSED`,
  - downstream unlocks (`PILLAR-QFT`, `PILLAR-STAT`, `PILLAR-COSMO`) remain blocked by their listed prerequisites.
- Path 2 closure sprint lock (GR-only):
  - do not unlock `PILLAR-QM`, `PILLAR-EM`, or `PILLAR-SR` while `TOE-GR-3D-03`
    remains blocker-facing or while action/RAC alignment adjudication remains
    `NOT_YET_DISCHARGED`.
  - after bounded/discrete 3D closure adjudication is satisfied, the next
    GR-only depth target is
    `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`.

Pillar-claim mapping rule (new-claim gate):
- No new `TOE-<pillar>-*` theory claim row may be added unless the claim prefix maps to a frozen pillar closure token.
- Frozen claim-prefix -> closure-token map:
  - `TOE-GR-*` -> `TARGET-GR01-DERIV-CHECKLIST-PLAN`
  - `TOE-SR-*` -> `TARGET-SR-COV-PLAN`
  - `TOE-EM-*` -> `TARGET-EM-U1-PLAN`
  - `TOE-QM-*` -> `TARGET-QM-EVOL-PLAN;TARGET-QM-MEAS-PLAN;TARGET-QM-SYMM-PLAN`
  - `TOE-QFT-*` -> `TARGET-QFT-GAUGE-PLAN;TARGET-QFT-EVOL-PLAN`
  - `TOE-STAT-*` -> `TARGET-TH-ENTROPY-PLAN`
  - `TOE-COSMO-*` -> `TARGET-COSMO-BG-PLAN`

## Dual-Layer Closure Semantics (v0)

Purpose:
- Separate theorem-chain physics sufficiency from governance/publishability closure.
- Avoid claim inflation while preserving forward theorem engineering.

Definitions:
- `PHYSICS-CLOSED`: core theorem-chain objective is discharged under explicit assumptions and pinned non-claim boundaries.
- `GOVERNANCE-CLOSED`: roadmap closure criteria are satisfied (no required blocker rows remain `B-*` for the pillar closure package).
- `MATRIX-CLOSED`: pillar matrix `Status: CLOSED` under canonical unlock/publishability policy.

Terminology discipline:
- Conversational `closed` defaults to `PHYSICS-CLOSED` unless explicitly qualified.
- Use `MATRIX-CLOSED` (or `GOVERNANCE-CLOSED`) for canonical pillar-matrix closure claims.

Rule:
- Pillar matrix `Status` remains canonical for unlock policy (`ACTIVE`/`LOCKED`/`CLOSED`).
- Dual-layer status lines are diagnostic and do not override matrix status.
- Proceed gate:
  - Theorem-engineering progression to next-pillar targets is allowed only when
    `PILLAR-*_PHYSICS_STATUS` is `CLOSED_*` under explicit assumptions and
    pinned non-claim boundaries.
- Matrix closure gate:
  - Pillar matrix promotion to `CLOSED` is allowed only when
    `PILLAR-*_GOVERNANCE_STATUS` is `CLOSED_*` and all required blocker rows
    for that pillar are non-`B-*` in `RESULTS_TABLE_v0.md`.

Current dual-layer snapshot (machine-checkable tokens):
- `PILLAR-GR_PHYSICS_STATUS: CLOSED_v0_DISCRETE_CONDITIONAL`
- `PILLAR-GR_GOVERNANCE_STATUS: CLOSED_v0_REQUIRED_ROWS_CLEARED`
- `PROCEED_GATE_GR: ALLOWED_v0_PHYSICS_CLOSED`
- `MATRIX_CLOSURE_GATE_GR: ALLOWED_v0_GOVERNANCE_CLOSED`
- `REQUIRED_GR_CLOSURE_ROWS: TOE-GR-DER-01,TOE-GR-DER-02,TOE-GR-CONS-01`
- blocker references:
  - none (all required GR closure rows are non-`B-*`)

GR v0 matrix-closure unblock priority (remaining execution order):
1. none (required GR closure rows cleared for v0 matrix-closure gate).

Completed unblock milestone:
- `TOE-GR-DER-01` promoted to `T-CONDITIONAL` via
  `gr01_der01_scaffold_bundle_under_promoted_assumptions` in
  `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean`.
- `TOE-GR-DER-02` promoted to `T-CONDITIONAL` via synchronized derivation-grade
  package and action/RAC retirement alignment under conditional-publish endpoint:
  - `DER02_CHECKLIST_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
  - `ALIGNMENT_ADJUDICATION: DISCHARGED_CONDITIONAL_PUBLISH_v0`
  - lock pointers synchronized across checklist/newtonian/roadmap/state:
    - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md`
    - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md`
    - `formal/markdown/locks/functionals/FN-DERIVE_default_quotient_bridge_discharge_object_v0.md`
- `TOE-GR-CONS-01` promoted to `T-CONDITIONAL` via bridge-composed conservation
  compatibility theorem surface in `ConservationContract.lean`:
  - `gr01_conservation_compatibility_from_poisson_residual_v0`
  - `gr01_conservation_compatibility_from_bridge_promotion_chain_v0`
  - `CONS01_ADJUDICATION: DISCHARGED_CONDITIONAL_v0`
- Full-derivation escalation lane is discharged for bounded/discrete v0 scope:
  - target artifact:
    `formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`
  - adjudication token:
    `FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0_DISCRETE`
  - synchronized result row:
    `TOE-GR-FULL-01: T-PROVED`

Matrix-closure promotion gate is allowed for GR v0 because all required blocker
rows above are non-`B-*`; pillar-matrix status promotion remains a separate
governance decision.

## Pillar Activation Matrix

| Pillar ID | Status | Target IDs | Target Artifacts | Prerequisites | Minimum publishable closure criteria |
|---|---|---|---|---|---|
| `PILLAR-GR` | `CLOSED` | `TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-GR01-3D-03-PLAN;TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN;TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN;TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN;TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0;TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN;TARGET-GR01-FULL-DERIVATION-DISCHARGE-v0` | `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md;formal/docs/paper/DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md;formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md;formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md;formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md;formal/docs/paper/DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md;formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md;formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md` | `NONE` | Derivation-grade GR01 analytic discharge package closure including improved 3D mapping milestone `TOE-GR-3D-02`, mainstream-class 3D gate milestone `TOE-GR-3D-03` (`TARGET-GR01-3D-03-PLAN`), bounded discharge-attempt package target `TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN` (`DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md`), closure-focused 3D gate package target `TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN` (`DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md`), Track B bounded point-source sub-target `TARGET-GR01-3D-POINT-SOURCE-PLAN` (`formal/docs/paper/DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md`), minimal conservation compatibility surface `TOE-GR-CONS-01`, explicit action/RAC `conditional-publish endpoint` posture in `TOE_GR01_ACTION_RAC_STANCE_v0.md`, action/RAC retirement-alignment target `TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN` (`DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md`), upstream depth micro-target `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0` (`DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0.md`), and publication-grade derivation completeness gate token (already `CLOSED` for v0 discrete-only scope) via `TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN` (`DERIVATION_COMPLETENESS_GATE_v0.md`). |
| `PILLAR-QM` | `CLOSED` | `TARGET-QM-EVOL-PLAN;TARGET-QM-MEAS-PLAN;TARGET-QM-SYMM-PLAN;TARGET-QM-FULL-DERIVATION-DISCHARGE-v0` | `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md;formal/docs/paper/DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md;formal/docs/paper/DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md;formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md` | `TARGET-GR01-DERIV-CHECKLIST-PLAN` | QM evolution theorem chain is `T-PROVED` and full-derivation adjudication is discharged under explicit typed assumptions and anti-circularity controls; bounded inevitability is discharged on theorem surfaces and non-claim scope remains explicit. |
| `PILLAR-EM` | `ACTIVE` | `TARGET-EM-U1-PLAN` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md` | `TARGET-GR01-DERIV-CHECKLIST-PLAN` | U(1)/Maxwell-object recovery kickoff is active under architecture-v1 phase discipline with bounded/non-claim scope, explicit assumption classes, anti-shortcut guards, and falsifiable interfaces. |
| `PILLAR-SR` | `CLOSED` | `TARGET-SR-COV-PLAN;TARGET-SR-COV-THEOREM-SURFACE-PLAN;TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN;TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN` | `formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md;formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_THEOREM_SURFACE_v0.md;formal/docs/paper/DERIVATION_TARGET_SR_DERIVATION_COMPLETENESS_GATE_v0.md;formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md` | `TARGET-GR01-DERIV-CHECKLIST-PLAN` | Covariance/kinematics theorem chain discharged under explicit Lorentz and bounded-domain assumptions, derivation-completeness failure-trigger set theorem-discharged, bounded inevitability necessity/counterfactual surface theorem-discharged, and authoritative no-deviation full-derivation/discharge/inevitability roadmap closure synchronized to results/matrix promotion surfaces. |
| `PILLAR-QFT` | `LOCKED` | `TARGET-QFT-GAUGE-PLAN;TARGET-QFT-EVOL-PLAN` | `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md;formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md` | `TARGET-EM-U1-PLAN;TARGET-SR-COV-PLAN` | Gauge and field-evolution contract targets with explicit quantization posture and no over-claim. |
| `PILLAR-STAT` | `LOCKED` | `TARGET-TH-ENTROPY-PLAN` | `formal/docs/paper/DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md` | `TARGET-GR01-DERIV-CHECKLIST-PLAN` | Entropy-balance/thermodynamic closure target with explicit regime and non-equilibrium assumptions. |
| `PILLAR-COSMO` | `LOCKED` | `TARGET-COSMO-BG-PLAN` | `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md` | `TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN` | Background-cosmology target with explicit metric/expansion assumptions and falsifiable hooks. |

## Promotion Attempt Log

| Pillar / Blocker | Target ID | Promotion hypothesis | Promotion mechanism | Promotion attempt cycle | Attempt status | Discharge path defined | Discharge scaffold module | Next promotion objective (token) | Result |
|---|---|---|---|---|---|---|---|---|---|
| `PILLAR-GR / TOE-GR-3D-03 (Track B)` | `TARGET-GR01-3D-POINT-SOURCE-PLAN` | Bounded-domain Dirichlet point-source posture can support domain-wise residual characterization and away-from-source Poisson closure under explicit assumptions. | Freeze `PointSourceDirichletBoundaryAssumptions`, then pin finite-domain operator-equation/linear-system/system/candidate bridge objects and theorem tokens without continuum or infinite-domain inversion claims; keep bounded attempt package pinned in `TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN` (`formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md`) and closure-focused package pinned in `TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN` (`formal/docs/paper/DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md`). | `Cycle-002 (2026-02-14)` | `B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN` | `YES` | `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean` | `gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility` | Attempt executed; objective advanced to existential away-from-source closure token; status remains blocker-facing and unproven for promotion. |
| `PILLAR-GR / TOE-GR-CONS-01` | `TARGET-GR-CONS-PLAN` | Weak-field conservation compatibility can be promoted from contract baseline to a bridge-composed theorem-surface token under explicit assumptions. | Compose GR01 bridge residual closure with conservation compatibility theorem tokens in `ConservationContract.lean`, bind assumption IDs, and enforce non-claim boundaries with promotion tests. | `Cycle-008 (2026-02-15)` | `DISCHARGED_CONDITIONAL_v0` | `YES` | `formal/toe_formal/ToeFormal/GR/ConservationContract.lean` | `gr01_conservation_compatibility_from_bridge_promotion_chain_v0` | Promotion executed: `TOE-GR-CONS-01` moved to non-blocked theorem-conditional status; compatibility closure is explicit under weak-field/default-quotient assumptions while full conservation-family completion remains out of scope. |
| `PILLAR-GR / action-to-operator upstream depth` | `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0` | Discrete action surface can discharge operator-side posture under explicit finite-difference variation assumptions and bounded/non-claim constraints. | Freeze the action/variation bridge route (`ActionRep32FiniteDifferenceRepresentsP`, `ActionVariationBridgeRep32At`), discharge evaluator transport (`MICRO-03A2`, `MICRO-03A3`) with a bridge witness constructor route, and keep bounded/non-claim boundaries explicit. | `Cycle-004 (2026-02-14)` | `DISCHARGED_v0_DISCRETE` | `YES` | `formal/toe_formal/ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean` | `actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_v0` | Discharge route assembled in-module via `mk_ELImpliesDiscretePoissonResidual_from_bridge_v0` and guarded end-to-end theorem chain; adjudication synchronized to `ACTION_TO_OPERATOR_ADJUDICATION: DISCHARGED_v0_DISCRETE`; enforcement gate pinned at `formal/python/tests/test_gr01_action_operator_discharge_gate.py`. |
| `PILLAR-GR / full-derivation discharge` | `TARGET-GR01-FULL-DERIVATION-DISCHARGE_v0` | Weak-field Poisson operator posture should be derivable from the declared action route without policy bridge assumptions. | Convert the current contract-level EL->residual bridge into an algebra-level derivation path by eliminating placeholder/axiomatic default-route objects and proving a direct action-side discharge theorem; keep bounded/discrete/non-claim limits explicit. | `Cycle-009 (2026-02-15)` | `B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN` | `YES` | `formal/toe_formal/ToeFormal/Variational/ActionRep32QuadraticCubic.lean` | `actionRep32_produces_operator_equation_discrete_without_bridge_assumptions_v0` | Blocker inventory is pinned in `DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`; deviation expansion theorem token exists (`differenceQuotientRep32_cubic_deviation_expand`), but adjudication remains open. |

## Enforcement Hooks

- Canonical tests:
  - `formal/python/tests/test_pillar_dual_layer_gate_template.py`
  - `formal/python/tests/test_gr01_dual_closure_and_blockers.py`
- Physics-first outline pointer: `formal/docs/paper/PHYSICS_PAPER_OUTLINE_v0.md`
- Required governance suite (minimum):
  - `formal/python/tests/test_gr01_full_derivation_status_sync.py`
  - `formal/python/tests/test_gr01_hardening_roadmap_gate.py`
  - `formal/python/tests/test_qm_evolution_hardening_roadmap_gate.py`
  - `formal/python/tests/test_qm_gr_regime_expansion_gate.py`

## Freeze Policy

- No new pillar can move from `LOCKED` to `ACTIVE` without:
  - prerequisite closure checks passing,
  - roadmap update and doc-gate update,
  - governance-suite pass on pinned tests.
