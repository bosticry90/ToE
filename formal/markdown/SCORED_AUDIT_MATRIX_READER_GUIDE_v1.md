# Scored Audit Matrix Reader Guide v1

Purpose:
- Provide a reader-facing interpretation of `formal/docs/release/SCORED_AUDIT_MATRIX_v1.json`.
- Keep score interpretation bounded and non-overread safe.

How to read scores:
- Scores are on a 0-10 scale per domain.
- High governance scores indicate process and documentation discipline, not global physics adequacy.
- High seam-physics scores indicate bounded closure for declared scope only.

Non-claim boundary:
- This matrix does not claim a physics-complete ToE.
- This matrix does not claim external-truth confirmation.
- This matrix does not claim all-regime seam completion.

Domain definitions:
- `ARCHITECTURE_GOVERNANCE`: policy closure, guardrail presence, and cross-pin discipline.
- `DERIVATION_CHAIN_COMPLETENESS`: bounded completion of required derivation rows.
- `SEAM_PHYSICS_CLOSURE`: bounded seam closure posture and explicit unresolved debt.
- `EVIDENCE_TIER_PROGRESSION`: comparator progression level under current protocol.
- `MATHEMATICAL_FORMALIZATION`: formal witness/proof posture under bounded assumptions.
- `MAINTENANCE_HEALTH`: active test and governance lane stability.

Interpretation rules:
- Any row with `SEAM_PHYSICS_CLOSURE` less than 5 must include explicit open debt in the JSON artifact.
- Any row with high closure scores must still carry bounded-scope qualifiers.
- Summary rows must preserve `OVERALL_SEAM_PHYSICS_COMPLETE_GLOBAL: NO` unless all seam physics closure evidence changes and is re-audited.
