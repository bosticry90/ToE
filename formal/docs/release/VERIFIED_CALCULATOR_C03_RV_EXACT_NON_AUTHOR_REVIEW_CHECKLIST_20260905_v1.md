# C03/RV Exact Profile — Non-Author Review Checklist

Status: `DRAFT_CHECKLIST_FOR_PENDING_NON_AUTHOR_REVIEW`

This checklist governs review of the frozen C03/RV exact pre-release computation. The reviewer evaluates whether the computation deserves its bounded `VERIFIED_EXACT` claims. The review cannot validate SU(5), CCFT, the ToE, product v1, production activation, or any topology outside the seven frozen records.

Record criterion-by-criterion findings in `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_NON_AUTHOR_REVIEW_EVIDENCE_MATRIX_20260905_v1.md`. This checklist supplies the review instructions; the matrix supplies the complete source, operation, root, challenge, formal-evidence, and authority census that must be dispositioned.

## 0. Reviewer eligibility and custody

- [ ] Identify the reviewer and review date.
- [ ] Declare that the reviewer did not author the trusted operations, Python verifier, Julia route, Lean checker, candidate adapter, challenge registry, or frozen evidence.
- [ ] Disclose relevant conflicts, prior contributions, and any AI assistance used during review.
- [ ] Review commit `9a118bf71d2501a839437f7630bf1de0c9c4190c`, or independently establish that every dependency-closure file matches the frozen bundle.
- [ ] Replay `formal/docs/release/verified_calculator/c03_rv_exact/93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f.json` and confirm bundle hash `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f`.
- [ ] Confirm computation ID `2b8ab72bd24775bfc8914e85546484f244dddc9cb5bd43dc116db0aacf2f4e8a`, profile hash `e131c6f94014082b8dd78bb680f1acdcf76e924b0cbe8fb62eafdda5af860617`, and policy hash `ecda89e1e6b47db2f2ec8057656cd7d622944c0202eda58ab0cd907e48c2711b`.
- [ ] Stop and report a custody defect rather than repairing or silently substituting any mismatched artifact.

## 1. Scope and anti-tautology review

- [ ] Confirm the profile contains exactly 31 source nodes, 160 derived nodes, and 16 authoritative roots across C03 and RV01–RV06.
- [ ] Confirm the source-material contract is not an expected-answer table disguised as source evidence.
- [ ] Search the trusted package and Julia route for authoritative output literals, comparison-answer imports, historical oracle calls, acceptance-table lookups, or code paths that manufacture expected roots.
- [ ] Determine whether the chosen roots, source facts, or challenge applicability rules make agreement inevitable by construction; document every shared assumption that remains common-mode across Python and Julia.
- [ ] Confirm candidate production remains untrusted and no producer path can issue or promote a trusted receipt.

## 2. Source-binding audit — all 31 sources

For every source node, record source ID, typed locator, artifact hash, resolved value, scientific meaning, and disposition.

- [ ] Every `JsonPointerValueRef`, `UniqueTableCellRef`, `TensorComponentRef`, and `NamedConventionRef` resolves exactly one intended value.
- [ ] Evidence-only hashes are never accepted as value locators.
- [ ] Source normalization preserves the intended convention and does not launder an expected output into an input.
- [ ] C03 N7 and N8 source boundaries are real, active, and correctly typed.
- [ ] RV03 uses the intended representation and source channel.
- [ ] Each source has appropriate semantic type, representation tags, index spaces, physical dimension, unit convention, and domain.
- [ ] Any scientific ambiguity is listed as a limitation or defect; computational hash agreement does not resolve semantic ambiguity.

## 3. Trusted operation audit — all 19 operations

For each operation, review its input schema, output schema, arity, semantic/type checks, unit/domain constraints, Python implementation, Julia counterpart where applicable, failure modes, and adversarial coverage:

- [ ] `ANGULAR_AVERAGE`
- [ ] `DOMAIN_PREDICATE`
- [ ] `EPISTEMIC_CLASSIFICATION`
- [ ] `EXACT_CLIFFORD_ACTION`
- [ ] `EXACT_MATRIX_PROJECTION`
- [ ] `GAUGE_GENERATOR_ACTION`
- [ ] `INVERTIBLE_NORMALIZATION`
- [ ] `LINEAR_COMBINATION`
- [ ] `NORMALIZATION_MONOMIAL`
- [ ] `NORMALIZATION_RECIPROCAL`
- [ ] `NORMALIZATION_REFERENCE_SCALAR`
- [ ] `PERMUTATION_PARITY`
- [ ] `PRODUCT`
- [ ] `RELATION_REDUCTION`
- [ ] `TENSOR_DIFFERENCE`
- [ ] `TENSOR_EXCHANGE_EIGENVALUE`
- [ ] `TENSOR_SUM`
- [ ] `WARD_REDUCTION`
- [ ] `OUTPUT_BIND`

The reviewer must explicitly answer:

- [ ] Does each operation express the intended physics rather than merely recover the preserved result?
- [ ] Are domain-neutral shared primitives narrow enough to avoid common physics-routine reuse?
- [ ] Are invalid units, representations, indices, domains, parent signatures, and unsupported operations rejected before verification?

## 4. Complete lowering review — all 160 derived nodes

- [ ] Map every derived node to one of the 19 operations and its exact parents.
- [ ] Confirm no node receives authority solely because its claimed value matches a historical transcript.
- [ ] Confirm every derived node lies in the ancestry of at least one authoritative root and no decorative computation is used to imply coverage.
- [ ] Inspect the complete 160/160 corruption record and confirm each mutation attacks the claimed intermediate while retaining the frozen baseline's confinement rules.
- [ ] Confirm zero unexpected survivors without treating expected verifier crashes or harness failures as successful scientific rejection.

## 5. Independent Julia/Nemo route

- [ ] Confirm Julia consumes only the frozen problem definition, source artifacts, and candidate packet—not Python intermediate values, Python receipts, or expected-answer tables.
- [ ] Trace all 16 authoritative roots from source to result in Julia.
- [ ] Confirm the common algebraic field, embedding, basis coordinates, symbolic variables, normalization, phases, tensor conventions, and output serialization agree by specification rather than shared physics code.
- [ ] Enumerate common-mode assumptions shared with Python and judge whether they are appropriately represented as profile assumptions rather than independent confirmation.
- [ ] Confirm Julia rejects profile, policy, request, computation, candidate, and algebraic-field identity mismatches.

## 6. Runtime certificate and Lean binding

- [ ] Confirm the certificate was generated from the actual executed graph and values.
- [ ] Confirm Lean checks the concrete computation, candidate, profile, policy, source, graph, node-trace, output, and status bindings covered by its stated semantics.
- [ ] Repeat or inspect negative controls for altered graph hashes, values, source hashes, output bindings, certificate-file hashes, and promoted statuses.
- [ ] State precisely what Lean proves and what remains trusted runtime code or out-of-scope physics.
- [ ] Reject any summary that describes Lean as proving SU(5) or the physical truth of the model.

## 7. Mandatory challenge corpus — 373 instances

- [ ] Reconcile all 10 accepted falsifier classes with the policy-freeze timestamp and confirm no accepted historical falsifier is unclassified.
- [ ] Confirm the baseline graph—not the mutant—determines permitted descendants and affected roots.
- [ ] Verify the instance census: 160 derived corruptions, 31 source-locator attacks, 160 unknown-operation attacks, 16 output-binding attacks, and one instance each for parent bypass, stale edge, RV03 phase, N7 boundary, N8 boundary, and evaluated-zero semantics.
- [ ] Inspect representative raw packets and verifier errors from every challenge class; verify descriptions match actual mutations and acceptance criteria.
- [ ] Confirm per-root challenge isolation neither spares an affected root nor downgrades an unrelated root.
- [ ] Confirm an optional AI challenge can only preserve or reduce assurance and cannot self-promote into the mandatory registry.

## 8. Replay, closure, and platform evidence

- [ ] Confirm both Windows replay records reproduce the same frozen bundle hash.
- [ ] Recompute the generated dependency closure and confirm 54 Python files, 5 Julia files, 4 Lean files, 9 fixed artifacts, zero unresolved dependencies, and zero manual exclusions.
- [ ] Confirm content-addressed evidence is protected from newline conversion and frozen means hash-bound rather than filesystem-immutable.
- [ ] Treat the Linux egress-denied test as pending until an actual preserved result exists; its definition alone is not Linux evidence.
- [ ] If Linux evidence is available, verify kernel network-namespace isolation, only-loopback interfaces, no default route, failed active egress probe, all exact identities, all non-environment receipt fields, all 16 roots, all 373 challenges, and Linux bundle replay.

## 9. Claim-ledger and authority-boundary review

- [ ] Review every one of the 16 claim-ledger entries and its `does_not_claim` boundaries.
- [ ] Confirm existing historical scientific authority is attached claim by claim and is not used as computational input.
- [ ] Confirm changing an authority attachment cannot change computation ID or verification receipt.
- [ ] Confirm `calculator_profile_review_status` remains `SCIENTIFIC_REQUALIFICATION_NOT_EARNED` until a valid non-author result is accepted through a separate authority action.
- [ ] Confirm the evidence never promotes SU(5), CCFT, the ToE, the generic runner, 1,188 topology classes, product v1, or production activation.

## 10. Required reviewer report

The report must contain:

- [ ] Reviewer identity, eligibility declaration, conflicts, methods, environment, and exact artifacts/hashes inspected.
- [ ] A disposition and rationale for every checklist section and every discovered defect or limitation.
- [ ] A root-by-root table stating whether `VERIFIED_EXACT` is supported, withheld, or requires amendment.
- [ ] An operation-by-operation table covering all 19 trusted operations.
- [ ] A source-by-source table covering all 31 source bindings.
- [ ] A challenge-class table covering all 10 classes and 373 instances.
- [ ] One final disposition: `SUPPORTED_WITHIN_STATED_COMPUTATIONAL_SCOPE`, `SUPPORTED_WITH_REQUIRED_AMENDMENTS`, or `NOT_SUPPORTED`.
- [ ] Explicit statements that `scientific_promotion = false`, `product_v1_release = false`, and `production_activation = false`.
- [ ] A content hash for the completed report and an unambiguous link to this checklist and the frozen bundle.

Unchecked items, unresolved discrepancies, missing artifacts, or reviewer non-independence prevent a clean supported disposition. Review findings must produce a new version or amendment; they must not mutate the frozen exact packet in place.
