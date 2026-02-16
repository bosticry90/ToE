# TOE-GR-01 Potential Identification v0

Spec ID:
- `TOE_GR01_POTENTIAL_IDENTIFICATION_v0`

Purpose:
- Define the explicit mapping from weak-field perturbation objects to a scalar potential surface `Phi`.
- Prevent proxy-only interpretation drift on the TOE-GR-01 derivation path.

## Assumption Freeze And Inputs

Assumption IDs:
- `ASM-GR01-NRM-01`: potential/source normalization convention.
- `ASM-GR01-BND-01`: periodic/discrete boundary convention.
- `ASM-GR01-REG-01`: weak-field regime predicate (upstream theorem-conditional token).
- `ASM-GR01-SYM-01`: projection-map well-formedness token.

Canonical pointers:
- `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/Variational/GR01SymmetryPromotion.lean`

## Mapping Scaffold (v0)

1. Select scalar potential carrier:
   - define a scalar observable `Phi` on the weak-field domain.
2. Identify perturbation-to-potential relation:
   - `Phi` is defined as the leading-order scalar part of the perturbation surface.
3. Pin gauge convention:
   - periodic/mean-zero gauge condition is explicit on bounded domains.
4. Source coupling identity:
   - define the source surface `rho` and its leading-order coupling to `Phi`.

## Symbol Dictionary And Units Posture

- `Phi`:
  - scalar potential carrier for weak-field projection.
  - interpreted as a potential-like scalar under conventional Newtonian weak-field reading.
- `rho`:
  - source-density carrier for weak-field projection.
  - interpreted as source-like density under scoped assumptions.
- `kappa`:
  - coupling coefficient linked by calibration note `TOE_GR01_KAPPA_CALIBRATION_v0.md`.
- Units are stated for interpretation discipline only; this note does not claim full unit-discharge completeness.

## Correspondence Checkpoints

- Checkpoint A:
  - potential carrier is explicit and witness-carrying (no placeholder carrier semantics).
- Checkpoint B:
  - source carrier is explicit and gauge/boundary conventions are pinned.
- Checkpoint C:
  - projection mapping remains compatible with theorem-chain outputs (`ProjectionMapWellFormed`).

Required assumptions (explicit):
- weak-field ansatz,
- perturbation truncation control,
- gauge admissibility,
- source regularity assumptions for bounded-domain extraction.

Dependencies:
- weak-field expansion note: `formal/docs/paper/TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md`
- front-door comparator contract (bounded support only):
  - `formal/docs/rl03_weak_field_poisson_v0_front_door_contract.md`

## DER-01 Theorem-Surface Linkage (v0)

- Canonical scaffold-bundle theorem token:
  - `gr01_der01_scaffold_bundle_under_promoted_assumptions`
  - module: `formal/toe_formal/ToeFormal/Variational/GR01DerivationScaffoldPromotion.lean`
- Potential/source identification closure remains assumption-scoped and
  participates in the scaffold bundle through explicit carrier-equality inputs.

Non-claim:
- This document does not claim theorem-level uniqueness of potential identification.
- This document does not claim external truth correspondence.

## Failure Modes And Falsifiability Hooks

- If potential/source carrier mapping cannot be made witness-carrying, the projection layer is invalid.
- If gauge convention changes alter `Phi`/`rho` interpretation without explicit re-freeze, the mapping is invalid.
- If interpretation mapping cannot be matched to the calibration posture for `kappa`, downstream physics claims remain blocked.
