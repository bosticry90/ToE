# TOE-GR-01 Weak-Field Expansion Note v0

Spec ID:
- `TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0`

Purpose:
- Provide the explicit analytic-bridge checklist for weak-field expansion on the TOE-GR-01 path.
- Fix the expansion assumptions and prevent silent changes to approximation scope.

Scope:
- Weak-field, small-perturbation regime only.
- Structural derivation note; no claim of full nonlinear gravity closure.

## Assumption Freeze And Inputs

Assumption IDs:
- `ASM-GR01-REG-01`: weak-field regime predicate (`T-CONDITIONAL`).
- `ASM-GR01-APP-01`: first-order truncation/scaling (`T-CONDITIONAL`).
- `ASM-GR01-APP-03`: remainder suppression posture (`P-POLICY`).
- `ASM-GR01-BND-01`: boundary conventions (`P-POLICY`).
- `ASM-GR01-NRM-01`: normalization conventions (`P-POLICY`).

Canonical pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/Variational/GR01ScalingPromotion.lean`

## Expansion Scaffold (Discharge-Oriented v0)

1. Introduce weak-field ansatz:
   - `g = g0 + eta * h`, with `|eta| << 1`.
2. Select perturbation ordering:
   - keep `O(eta)` terms for leading-order Poisson-form extraction.
3. Declare source scaling:
   - matter/source term enters at leading weak-field order.
4. Define retained and dropped terms:
   - retained: terms contributing to scalar-potential Laplacian balance,
   - dropped: `O(eta^2)` and above, under explicit boundedness assumptions.

## Approximation Bookkeeping

- Small parameter:
  - `eta` is the weak-field perturbation control parameter.
- Retained order:
  - first-order (`O(eta)`) terms only.
- Discarded order:
  - second-order and higher (`O(eta^2+)`) terms.
- Closure token:
  - retained-order consistency is represented by `gr01_first_order_truncation_sound`.

## Units And Symbol Dictionary (Weak-Field Scope)

- `Phi`:
  - scalar potential role in weak-field identification.
  - conventional dimensional posture: potential-like quantity (`L^2 / T^2`) when mapped to Newtonian units.
- `rho`:
  - source-density role in weak-field extraction (`M / L^3` under standard interpretation).
- `kappa`:
  - coupling constant pinned in calibration surface `TOE_GR01_KAPPA_CALIBRATION_v0.md`.
- This note is units-explicit but does not claim a full SI-complete derivation discharge.

## Correspondence Checkpoints (Mainstream Weak-Field Reading)

- Checkpoint A:
  - perturbative weak-field ansatz is explicit and bounded.
- Checkpoint B:
  - first-order truncation criterion is explicit and test-auditable.
- Checkpoint C:
  - extracted operator route is constrained to Poisson-form projection under scoped assumptions.

Required discharge objects:
- explicit weak-field ansatz object,
- explicit perturbation-order bookkeeping,
- explicit remainder control statement.

Dependencies:
- theorem surface: `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
- derivation target: `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md`

## DER-01 Theorem-Surface Token (v0)

- Canonical scaffold-bundle theorem token:
  - `gr01_der01_scaffold_bundle_under_promoted_assumptions`
  - module: `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean`
- This token bundles weak-field regime predicate, scaling/truncation soundness,
  projection-map well-formedness, and discrete residual closure under explicit
  assumptions.

Non-claim:
- This note does not claim full GR recovery.
- This note does not claim external empirical validation.

## Failure Modes And Falsifiability Hooks

- If first-order truncation cannot bound remainder terms, the weak-field derivation path fails.
- If symbol-to-units mapping for `Phi`, `rho`, `kappa` is inconsistent with calibration locks, the interpretation fails.
- If discrete-to-continuum reporting correspondence is not maintained transparently, paper-facing claims must remain blocked.
