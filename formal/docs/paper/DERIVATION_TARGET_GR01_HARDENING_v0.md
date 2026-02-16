# Derivation Target: GR01 Hardening v0

Spec ID:
- `DERIVATION_TARGET_GR01_HARDENING_v0`

Classification:
- `T-PROVED`

Purpose:
- Convert GR01 from “proved inside bounded/discrete v0 scope” into a robust and
  minimized research artifact inside the same scope.
- Enforce hardening criteria without promoting any continuum-GR claim.

Adjudication token:
- `GR01_HARDENING_ADJUDICATION: DISCHARGED_v0_DISCRETE_HARDENED`

Scope boundary (non-negotiable):
- Bounded/discrete weak-field v0 only.
- No continuum-limit promotion.
- No uniqueness or infinite-domain inversion promotion.
- No black-hole/full-GR semantics.

## Hardening done criteria (exit criteria)

GR01 is hardened only when all are true:

1. Assumptions are minimal and classified:
- Every assumption used by `TOE-GR-FULL-01` is classed as exactly one of:
  - `MATH` (provable in the discrete setting)
  - `DEF` (definition/encoding choice)
  - `POLICY` (modeling postulate)
  - `SCOPE` (bounded/weak-field/discretization regime)

2. Main modeling postulate is isolated:
- `ELImpliesDiscretePoissonResidual` is the only remaining physics-mode
  postulate in the canonical chain, or any remainder is explicitly weakened and
  justified.

3. Robustness is demonstrated:
- Controlled perturbations either preserve the derivation or fail with explicit,
  pinned failure reasons.

4. Legacy routes cannot re-enter canonical surface:
- Deprecated bridge routes are quarantined and forbidden in canonical theorem
  surfaces.

## Phase plan (authoritative)

### Phase I — Canonicalization & Hygiene

1) Legacy bridge ambiguity removal
- Canonical route must be pinned through:
  - `ELImpliesDiscretePoissonResidual`
  - transport lemmas only when explicitly required.
- Any legacy bridge route must live under `Deprecated.*` and be forbidden from
  canonical theorem signatures.

2) Structure-obligation normalization
- `ProjectionMapWellFormed`-family obligations must contain no placeholder
  `True` fields at hardening discharge.
- Equivalent obligation structures (for example `WeakFieldTruncationSound`) are
  included in the same anti-placeholder policy.

### Phase II — Assumption minimization

1) GR01 assumption ledger bundle
- Add canonical bundle token:
  - `GR01Assumptions_v0`
- Bundle is machine-checkable and categorizes each assumption as `MATH` / `DEF`
  / `POLICY` / `SCOPE`.
- Canonical artifact pointers:
  - `formal/toe_formal/ToeFormal/Variational/GR01AssumptionLedger.lean`
  - `formal/markdown/locks/policy/GR01_ASSUMPTION_LEDGER_v0.md`

2) Reclassification target
- Reclassify at least 1–3 assumptions from `POLICY` to `MATH`.

### Phase III — Robustness stress tests

1) Perturbation robustness record
- Add lock record token:
  - `GR01_ROBUSTNESS_RECORD_v0`
- Canonical artifact pointer:
  - `formal/markdown/locks/policy/GR01_ROBUSTNESS_RECORD_v0.md`
- Required perturbation families:
  - source perturbation (`ρ`)
  - potential perturbation (`Φ`)
  - discretization-parameter perturbation
  - boundary-handling perturbation
  - projection-condition perturbation (while well-formed)

2) Negative controls
- Add lock record token:
  - `GR01_NEGATIVE_CONTROL_RECORD_v0`
- Canonical artifact pointer:
  - `formal/markdown/locks/policy/GR01_NEGATIVE_CONTROL_RECORD_v0.md`
- Required hard negatives:
  - wrong coupling sign (`κ`)
  - broken scaling hierarchy
  - broken weak-field bound
  - broken symmetry obligation
  - incompatible carriers

### Phase IV — Optional continuum-alignment sanity checks

1) Multi-resolution trend record
- Add lock record token:
  - `GR01_RESOLUTION_TREND_RECORD_v0`
- Canonical artifact pointer:
  - `formal/markdown/locks/policy/GR01_RESOLUTION_TREND_RECORD_v0.md`
- Track at least:
  - residual norms
  - convergence trend
  - κ-calibration stability (if applicable)

2) Explicit limit-break accounting
- Non-convergence is admissible but must be explicitly documented as a scope
  boundary.

### Phase V — Pillar package freeze

Freeze package contents:
- one-page plain-language summary
- assumption ledger
- canonical theorem chain map
- robustness record
- negative-control record
- optional resolution trend record
- explicit limitation list (no continuum/full-GR claim)
- Canonical artifact pointers:
  - `formal/markdown/locks/policy/GR01_PILLAR_PACKAGE_v0.md`
  - `formal/docs/paper/TOE_GR01_PILLAR_SUMMARY_v0.md`
  - `formal/docs/paper/TOE_GR01_CANONICAL_CHAIN_MAP_v0.md`

## Enforcement contract (gate policy)

Hardening adjudication may flip to
`GR01_HARDENING_ADJUDICATION: DISCHARGED_v0_DISCRETE_HARDENED` only if all
conditions below are true and pinned:

1) Canonical anti-legacy gate:
- `ELImpliesProjectedResidual` absent from canonical GR01 theorem surfaces.

2) Placeholder-obligation gate:
- no `: True` placeholder fields remain in hardening-scoped obligation
  structures (`ProjectionMapWellFormed` family and equivalents used by the
  canonical GR01 route).

3) Assumption-ledger gate:
- `GR01Assumptions_v0` exists and each element has exactly one class in
  `MATH|DEF|POLICY|SCOPE`.
- `GR01_ASSUMPTION_LEDGER_v0` lock is present and synchronized with
  `GR01AssumptionLedger.lean`.

4) Robustness/negative-control gate:
- both `GR01_ROBUSTNESS_RECORD_v0` and `GR01_NEGATIVE_CONTROL_RECORD_v0`
  exist and are linked from this target document.

5) State sync gate:
- `State_of_the_Theory.md` carries the same hardening adjudication token.

6) Frozen-watch reopen gate:
- `GR01_PILLAR_PACKAGE_v0` must carry:
  - `GR01_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION`
  - `REOPEN_TRIGGER_CANONICAL_TOKEN_DRIFT_v0`
  - `REOPEN_TRIGGER_ROBUSTNESS_NEGCTRL_REGRESSION_v0`
  - `REOPEN_TRIGGER_RESOLUTION_TREND_BREAK_v0`

## Post-discharge handoff (next pillar selection)

- Discharging this target does not unlock comparator expansion or alter scope limits.
- Immediate next pillar focus is selected in state tokens and must be explicit:
  - `NEXT_PILLAR_FOCUS_v0`
  - `NEXT_PILLAR_PRIMARY_LANE_v0`

## Priority order

1. Phase I (canonicalization + quarantine)
2. Phase II (assumption ledger + 1–3 reclassifications)
3. Phase III (robustness + negatives)
4. Phase IV (resolution trends)
5. Phase V (pillar package)

## Single next move

Build the `GR01Assumptions_v0` bundle and classify each assumption as
`MATH` / `DEF` / `POLICY` / `SCOPE`; this determines the exact remaining
hardening work.
