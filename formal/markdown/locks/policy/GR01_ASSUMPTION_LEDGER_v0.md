# GR01 Assumption Ledger v0

Ledger ID:
- `GR01_ASSUMPTION_LEDGER_v0`

Classification:
- `P-POLICY`

Purpose:
- Record the exact canonical assumption surface for `TOE-GR-FULL-01` in bounded/discrete weak-field v0.
- Classify every assumption as exactly one of `MATH`, `DEF`, `POLICY`, `SCOPE`.
- Bind the markdown ledger to a machine-checkable Lean bundle (`GR01Assumptions_v0`).
- Record Phase II minimization progress (`POLICY -> MATH` reclassification set).

Machine-checkable bundle pointer:
- `formal/toe_formal/ToeFormal/Variational/GR01AssumptionLedger.lean`
- token: `structure GR01Assumptions_v0`
- token: `structure GR01Assumptions_v0_min1`
- token: `structure GR01Assumptions_v0_min2`
- token: `structure GR01Assumptions_v0_min3`

Class map pointer:
- token: `inductive GR01AssumptionClass_v0`
- token: `def gr01AssumptionClass_v0`

Scope boundary:
- bounded/discrete weak-field v0 only
- no continuum-limit promotion
- no uniqueness/infinite-domain inversion promotion
- no full-GR/black-hole claim

## Canonical assumption list (`GR01Assumptions_v0`)

| Assumption token | Class | Role |
|---|---|---|
| `hε : ε ≠ 0` | `SCOPE` | Nondegenerate discretization/expansion regime. |
| `hAction : actionRep32.action = actionRep32Cubic declared_g_rep32` | `MATH` | Reclassified on minimized route via theorem-side default action binding; removed from `GR01Assumptions_v0_min3`. |
| `hRAC : RACRep32CubicObligationSet declared_g_rep32` | `POLICY` | Admissibility/regularity policy obligations. |
| `hP : P_rep32 = P_cubic_rep32_def declared_g_rep32` | `MATH` | Reclassified via theorem-bound default identity token `P_rep32_def` and eliminated from minimized bundle `GR01Assumptions_v0_min1`. |
| `hPotentialIdentification : PotentialIdentification` | `DEF` | Choice of potential carrier encoding. |
| `hSourceIdentification : SourceIdentification` | `DEF` | Choice of source carrier encoding. |
| `hLaplacianExtraction : LaplacianExtraction` | `DEF` | Choice of discrete operator extraction encoding. |
| `hUnitsAndCalibration : UnitsAndCalibration` | `DEF` | Choice of κ/G_N encoding relation. |
| `carrierWitness : ProjectionCarrierWitness` | `DEF` | Explicit carrier witness object for projection map. |
| `hPotentialCarrierEq` | `DEF` | Witness equality for potential carrier map. |
| `hSourceCarrierEq` | `DEF` | Witness equality for source carrier map. |
| `hWeakFieldUniformBound` | `SCOPE` | Bounded weak-field regime assumption. |
| `hPhiBoundWithin` | `SCOPE` | Potential bound is inside selected regime bound. |
| `hRhoBoundWithin` | `SCOPE` | Source bound is inside selected regime bound. |
| `hPhiScaleDominates` | `SCOPE` | Potential scaling hierarchy constraint. |
| `hRhoScaleDominates` | `SCOPE` | Source scaling hierarchy constraint. |
| `hHigherOrderTermsNegligible` | `MATH` | Reclassified on minimized route by replacing bounded higher-order policy input with direct `FirstOrderRemainderSuppressed` witness (`GR01Assumptions_v0_min2`). |
| `hRemainderScaleZero : remainderScale = 0` | `SCOPE` | Explicit bounded-v0 first-order regime choice. |
| `hELImpliesOperatorResidualUnderBound` | `POLICY` | Main bridge-side modeling postulate in canonical chain input. |

## Classification discipline

- Exactly-one-class invariant: each canonical assumption token appears in exactly one class.
- Promotion objective for hardening:
  - move at least 1–3 assumptions from `POLICY` to `MATH` where derivable in discrete scope.
- Current postulate concentration target:
  - isolate `ELImpliesDiscretePoissonResidual` (or weakened equivalent) as sole remaining physics-mode postulate.

## Phase II minimization checkpoint (first landed)

- Reclassification token:
  - `GR01_RECLASSIFICATION_v0_MIN1: hP_POLICY_TO_MATH_via_P_rep32_def`
- Lean witness pointers:
  - `gr01AssumptionClass_v0` maps `pRep32DefaultBinding -> MATH`
  - `gr01_end_to_end_poisson_equation_of_GR01Assumptions_v0_min1`
- Reduction statement:
  - canonical minimized bundle `GR01Assumptions_v0_min1` removes explicit `hP` input and routes through theorem-side default binding.

## Phase II minimization checkpoint (second landed)

- Reclassification token:
  - `GR01_RECLASSIFICATION_v0_MIN2: hHigherOrderTermsNegligible_POLICY_TO_MATH_via_FirstOrderRemainderSuppressed`
- Lean witness pointers:
  - `gr01AssumptionClass_v0` maps `higherOrderTermsNegligible -> MATH`
  - `gr01_poisson_equation_of_GR01Assumptions_v0_min2`
- Reduction statement:
  - canonical minimized bundle `GR01Assumptions_v0_min2` replaces
    `hHigherOrderTermsNegligible` + scaling-truncation plumbing with direct
    `hFirstOrderRemainderSuppressed` and closes through
    `gr01_discrete_residual_from_bridge_promotion_chain`.

## Phase II minimization checkpoint (third landed)

- Reclassification token:
  - `GR01_RECLASSIFICATION_v0_MIN3: hAction_POLICY_TO_MATH_via_default_binding_route`
- Lean witness pointers:
  - `gr01AssumptionClass_v0` maps `actionDefaultBinding -> MATH`
  - `gr01_poisson_equation_of_GR01Assumptions_v0_min3`
- Reduction statement:
  - canonical minimized bundle `GR01Assumptions_v0_min3` removes explicit
    `hAction` input and closes through
    `gr01_discrete_residual_from_bridge_promotion_chain_default_binding`.

## Synchronization pointers

- Hardening target:
  - `formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md`
- State checkpoint:
  - `State_of_the_Theory.md` (`GR01_HARDENING_ADJUDICATION` family)
