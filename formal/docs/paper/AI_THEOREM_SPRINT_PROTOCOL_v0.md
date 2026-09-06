# AI Theorem Sprint Protocol v0

Spec ID:
- `AI_THEOREM_SPRINT_PROTOCOL_v0`

Status:
- `AVAILABLE_NONLIVE_METHOD_PROTOCOL`

Purpose:
- Define one bounded, auditable way to use AI search on a high-leverage mathematical
  blocker after the physics question has been converted into a closed theorem target.
- Increase search breadth without converting model confidence into mathematical or
  physical authority.

Non-claim boundary:
- This protocol proves nothing by itself.
- A completed formal proof establishes only that a conclusion follows from formalized
  assumptions.
- Statement correspondence and physical applicability require separate reviews.
- No sprint may validate the ToE, select nature's ontology, close a seam, or settle an
  empirical question merely because a proof assistant accepts a theorem.

## Eligibility gate

A target is eligible only when all are true:

1. The theorem statement is closed and exact.
2. Definitions and assumptions are explicit.
3. The endpoint is binary or tightly classified.
4. A concrete Lean target is defined.
5. The result has high leverage for one selected pillar or seam.
6. No unresolved empirical or interpretive choice is hidden inside the statement.
7. A counterexample or insufficiency result is accepted as useful progress.

Suitable examples:
- Conservation identity under explicit regularity assumptions.
- Consistent-truncation theorem.
- Counterexample to a claimed seam implication.
- Bounded equivalence theorem between two formulations.
- Theorem proving that current assumptions are insufficient.
- Explicit source-admissibility or exchange theorem.

Ineligible examples:
- Whether the candidate master action is physically true.
- Whether a bookkeeping condition should become a law of nature.
- Whether an unexplained numerical pattern is physically real.
- Whether CCFT is empirically valid.
- Which interpretation of quantum mechanics is correct.

## Frozen sprint packet

Before search begins, freeze:

- The theorem statement and Lean signature.
- Definitions, domains, regularity assumptions, and imported results.
- Nonclaims and forbidden assumption substitutions.
- Acceptance tests and axiom audit.
- Time, compute, and route-count budget.
- The exact result classes: `PROVED`, `REFUTED_BY_COUNTEREXAMPLE`,
  `ASSUMPTIONS_INSUFFICIENT`, or `UNRESOLVED_WITH_EXACT_GAP`.

## Execution

1. Start several genuinely different proof families when resources justify them.
2. Include at least one counterexample, impossibility, or assumption-insufficiency route.
3. Maintain a compact route registry with premises, progress, and first blocker.
4. Stop routes that only restate the target or depend on theorem-strength unproved lemmas.
5. Allow cross-pollination only after independent routes have produced concrete objects.
6. Require a surviving route to expose lemmas and constructions, not confidence reports.
7. Adversarially review the strongest proof and actively search for edge cases.
8. Translate the surviving result into Lean when the target was Lean-eligible.
9. Audit axioms, `sorry`, `admit`, unsafe declarations, and theorem-statement drift.
10. Independently check that the formal theorem matches the intended physical statement.

Parallel agents are optional. No fixed agent count or permanent hierarchy is required.

## Acceptance gates

### Logical correctness

- Lean target builds.
- No forbidden proof holes or project-specific axioms.
- Imported assumptions are listed.
- Edge cases and domain conditions are explicit.

### Statement correspondence

- A reviewer maps every formal object to the intended mathematical object.
- The formal conclusion is neither weaker nor differently scoped than the stated target.
- Reductions and equivalence steps preserve the target's meaning.

### Physical applicability

- A separate review states whether the assumptions can describe the intended physical
  regime.
- Formal success does not upgrade empirical status.
- A failed applicability review preserves the theorem as mathematics while blocking the
  physical claim.

## Stopping rule

- Run one sprint, issue one adversarial review, and adjudicate the result.
- Do not extend the sprint merely because additional search might be interesting.
- A successor sprint requires a new target or a concrete defect in the frozen statement,
  proof, formalization, or correspondence audit.

## Required output

Each sprint must produce one compact record containing:

- Target and Lean signature.
- Assumptions and nonclaims.
- Route registry and blocker outcomes.
- Counterexample-search outcome.
- Surviving proof or exact remaining gap.
- Lean build and axiom-audit result.
- Statement-correspondence review.
- Physical-applicability status.
- Final result class and next action.

## Source context

- OpenAI proof artifact:
  https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_proof.pdf
- OpenAI prompt artifact:
  https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_prompt.pdf

These sources motivate the orchestration pattern only. This protocol does not record the
external proof as refereed, independently accepted, or machine-verified.

