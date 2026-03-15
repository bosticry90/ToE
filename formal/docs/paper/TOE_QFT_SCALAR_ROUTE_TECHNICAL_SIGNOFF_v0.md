# TOE QFT Scalar Route Technical Sign-Off v0

Sign-off ID:
- TOE_QFT_SCALAR_ROUTE_TECHNICAL_SIGNOFF_v0

Scope:
- Rigor-first scalar technical sign-off for the bounded free-scalar QFT-to-QM lane.
- This sign-off is a technical completeness and bounded-debt declaration, not a publication-format declaration.

Sign-off status tokens:
- SCALAR_ROUTE_TECHNICAL_SIGNOFF_STATUS_v0: SIGNED_OFF_BOUNDED_RIGOR_BASELINE_v0
- SCALAR_ROUTE_TECHNICAL_SIGNOFF_DEBT_CLASS_v0: BOUNDED_LINKAGE_RECOVERY_DEBT_v0
- SCALAR_ROUTE_TECHNICAL_SIGNOFF_GATE_v0: REQUIRED_TECHNICAL_SIGNOFF_SCHEMA_AND_PARITY
- SCALAR_ROUTE_TECHNICAL_SIGNOFF_ARTIFACT_v0: toe_qft_scalar_route_technical_signoff_checkpoint_v0

## Technical Completeness Summary

- ledger_claims: 9
- full_derived: 9
- summarized_only: 0
- distributed_derivation: 0
- missing_derivation: 0
- paper_may_rely_with_gap_flag: 0
- paper_must_not_rely: 0

Interpretation:
- Scalar derivation capture is complete at bounded-lane technical-record level.
- Paper reliance no longer depends on gap-flagged claims.

## Remaining Bounded Debts

1. Non-blocking for scalar paper:
- Partial linkage recovery items that remain explicitly bounded and do not alter current non-claim scope.
- Claims currently tracked as PARTIAL_LINKED_v0 with LINKAGE_RECOVERY_REQUIRED_v0.

2. Blocking for stronger claims:
- Claims requiring theorem-level linkage closure before any scope expansion or stronger claim labels.
- Includes scope-downgrade debt where broader interpretations are intentionally disallowed.

3. Deferred to later lanes:
- Interacting-field completion.
- Gauge-sector completion.
- Renormalization and multiparticle-scattering completion.

## Debt Classification Table

- debt_id: DEBT-SCALAR-LINKAGE-01
  claim_id: SCALAR-CLAIM-03-CANONICAL-QUANTIZATION
  class: BLOCKING_FOR_STRONGER_CLAIMS
  disposition: LINKAGE_RECOVERY_REQUIRED_v0
  scalar_paper_effect: NON_BLOCKING_FOR_SCALAR_PAPER

- debt_id: DEBT-SCALAR-LINKAGE-02
  claim_id: SCALAR-CLAIM-09-NONRELATIVISTIC-LIMIT
  class: BLOCKING_FOR_STRONGER_CLAIMS
  disposition: LINKAGE_BLOCKER_v0
  scalar_paper_effect: NON_BLOCKING_FOR_SCALAR_PAPER

- debt_id: DEBT-SCALAR-LINKAGE-03
  claim_id: SCALAR-CLAIM-02-COVARIANCE
  class: NON_BLOCKING_FOR_SCALAR_PAPER
  disposition: LINKAGE_RECOVERY_REQUIRED_v0
  scalar_paper_effect: NON_BLOCKING_FOR_SCALAR_PAPER

- debt_id: DEBT-SCALAR-LINKAGE-04
  claim_id: SCALAR-CLAIM-04-HAMILTONIAN-DENSITY
  class: NON_BLOCKING_FOR_SCALAR_PAPER
  disposition: LINKAGE_RECOVERY_REQUIRED_v0
  scalar_paper_effect: NON_BLOCKING_FOR_SCALAR_PAPER

## Claim Envelope (Honest Scope)

Allowed for current scalar paper:
- bounded free-scalar route with explicit assumptions, limits, and non-claim boundaries.

Not allowed for current scalar paper:
- stronger claim labels requiring theorem-level linkage closure beyond current bounded sign-off.

## Reproducibility Pointers

- formal/docs/paper/TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_v0.md
- formal/output/toe_qft_scalar_route_full_technical_record_checkpoint_v0.json
- formal/output/toe_qft_scalar_route_technical_signoff_checkpoint_v0.json
- formal/python/tests/test_toe_qft_scalar_route_full_technical_record_gate.py
- formal/python/tests/test_toe_qft_scalar_route_technical_signoff_gate.py

Non-claim boundary:
- This sign-off does not authorize seam promotion.
- This sign-off does not authorize scope expansion beyond bounded scalar route claims.
