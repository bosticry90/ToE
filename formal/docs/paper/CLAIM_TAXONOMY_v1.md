# Claim Taxonomy v1

Spec ID:
- `CLAIM_TAXONOMY_v1`

Classification:
- `P-POLICY`

Purpose:
- Define the release-facing claim labels for the ToE v0.1-alpha criticizability standard.
- Separate Lean-backed theorems, supplied semantic structures, reproducible evidence, blockers, policy claims, and hypotheses.
- Preserve legacy labels only for historical or unmigrated non-release contexts.

Current release-facing labels:
- `T-LEAN-UNCOND`: Lean-backed theorem with no unresolved project-specific assumptions, no retained project axioms, no supplied semantic structures, and only ordinary accepted Lean/mathlib foundations.
- `T-LEAN-COND`: Lean-backed theorem under explicit hypotheses or supplied project structures, without retained project axiom dependence.
- `T-LEAN-AXIOMED`: Lean-backed theorem whose release audit row depends on retained project-specific axioms.
- `E-REPRO`: reproducible computational or Python evidence.
- `S-SUPPLIED`: supplied semantic/spec structure, not derived.
- `B-BLOCKED`: known blocker, missing witness, or retained unresolved obligation.
- `P-POLICY`: governance, schema, control-plane, or nonclaim policy statement.
- `H-HYP`: candidate physical hypothesis or interpretive organizing claim.

Legacy labels:
- `T-PROVED`
- `T-CONDITIONAL`
- `DISCHARGED_v0`
- `LOCKED`

Legacy rule:
- Legacy labels are not release-facing v0.1-alpha labels.
- They may remain in historical, archived, or unmigrated non-release surfaces.
- They must not appear as the `primary_label` or `supporting_labels` of v0.1-alpha ledger rows.

Multi-label rule:
- Each release-facing row has exactly one `primary_label`.
- Additional authority classes may appear in `supporting_labels`.
- The primary label records the main public authority posture of the row.

Nonclaim boundary:
- This taxonomy does not promote the master action.
- It does not claim pillar completion, seam closure, Phase 2 readiness, empirical adequacy, canonical ToE status, or QFT-GR source-map closure.
