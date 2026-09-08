# C03/RV Exact Computation — Non-Author Review Evidence Matrix

Status: `PENDING_NON_AUTHOR_REVIEW`

This matrix operationalizes the frozen review checklist. It does not record a review result, change the frozen calculation, or earn scientific requalification. Every disposition begins `PENDING`; only an eligible non-author reviewer may replace it in a separately hash-bound review result.

## Frozen review target

| Identity | Frozen value |
| --- | --- |
| Computation | `2b8ab72bd24775bfc8914e85546484f244dddc9cb5bd43dc116db0aacf2f4e8a` |
| Candidate | `fe0c6fa2133a7a9ed8bb94df3a91265e91d9db1a16206b487895a3c7e4353966` |
| Physics profile | `e131c6f94014082b8dd78bb680f1acdcf76e924b0cbe8fb62eafdda5af860617` |
| Verification policy | `ecda89e1e6b47db2f2ec8057656cd7d622944c0202eda58ab0cd907e48c2711b` |
| Verification receipt | `68f7e4c7f23c264da19e53e5cf24db1fcf8ae61c79a58848cc2f4e647045028f` |
| Runtime certificate | `5d08aa26f2f9396d76cefc2501339bb61fa3fb0df11f4b151c19e34257978e84` |
| Dependency closure | `5f08deda84148b2ac4249de4b44b914fd27c6274a127762017d614d5282cd204` |
| Frozen bundle | `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f` |

The primary evidence object is `formal/docs/release/verified_calculator/c03_rv_exact/93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f.json`. Locator expressions below are human-readable selectors into that object, not RFC 6901 pointers. The reviewer must record the exact artifact hash and any code revision actually inspected.

Disposition vocabulary: `PENDING`, `SUPPORTED`, `AMENDMENT_REQUIRED`, `NOT_SUPPORTED`, `NOT_APPLICABLE`. `NOT_APPLICABLE` requires a written rationale. Sampling is not sufficient where the matrix says `ALL`.

## A. Custody, independence, and anti-tautology

| ID | Assertion under review | Evidence locator | Required reviewer action | Acceptance condition | Disposition / finding |
| --- | --- | --- | --- | --- | --- |
| GOV-01 | The reviewer did not author the implementation, operation definitions, candidate, or frozen evidence. | Reviewer identity and contribution history | Declare identity, affiliations, conflicts, and authorship exclusions. | Non-authorship and relevant conflicts are explicit. | `PENDING` |
| GOV-02 | The review target is the exact frozen bundle above. | Bundle top level and filename | Recompute the content-addressed bundle identity using the trusted canonical format. | Recomputed identity is the frozen bundle hash. | `PENDING` |
| GOV-03 | Profile, policy, candidate, receipt, certificate, and closure identities are mutually bound. | Bundle top level; `request`; `verification_receipt`; `runtime_certificate` | Trace every hash edge and report missing or circular self-authorization. | Every declared edge resolves; no unbound substitute is accepted. | `PENDING` |
| GOV-04 | Expected-answer material does not authorize source or derived nodes. | `candidate.graph`; trusted Python imports; Julia route | Search data flow and imports for historical outputs, oracle receipts, and comparison answers. | No expected-answer value is used as an input or authority. | `PENDING` |
| GOV-05 | The trusted package does not import historical runner, candidate-generation, oracle, or acceptance code. | `formal/python/toe/generic_runner/verified_calculator/`; generated dependency closure | Independently inspect imports and generated closure. | Trust-boundary imports remain one-way and domain-neutral sharing is bounded. | `PENDING` |
| GOV-06 | Scientific authority is attached after computation and cannot change computation identity. | `request`; `authority_bindings`; `authority_attachments`; receipt | Recompute identity with authority-only changes or inspect the corresponding test evidence. | Computation and receipt stay fixed; attachment and outer bundle change. | `PENDING` |
| GOV-07 | The review cannot silently modify the successful packet. | Git object history; frozen artifact | Compare reviewed bytes to the frozen hash before and after review. | Any repair uses a new versioned lineage; this packet is unchanged. | `PENDING` |
| GOV-08 | Review conclusions remain within computational scope. | `verification_receipt.claim_ledger`; review result | Inspect every positive and negative claim. | No statement promotes SU(5), CCFT, ToE, product v1, or production authority. | `PENDING` |

## B. Source-binding census — all 31 required

For every row, inspect `candidate.graph.nodes[node_id=<source>]`, the matching `candidate.source_bindings`, and `verification_receipt.source_evidence`. Resolve the typed locator against the hash-bound local artifact and compare the resolved canonical value, semantic type, index/representation tags, dimension, unit convention, and domain with the node. Acceptance requires a real value locator, not an artifact hash masquerading as one.

| ID | Source node | Required action | Acceptance condition | Disposition / finding |
| --- | --- | --- | --- | --- |
| SRC-01 | `C03.CONVENTION.WILSON_SYMBOL` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-02 | `C03.NATIVE.SOURCE.COLUMNS` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-03 | `C03.NATIVE.SOURCE.DEFECTS` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-04 | `C03.NATIVE.SOURCE.DUAL_CACHE` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-05 | `C03.NATIVE.SOURCE.K_CACHE` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-06 | `C03.NATIVE.SOURCE.LEDGER` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-07 | `C03.NATIVE.SOURCE.OCCURRENCES` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-08 | `C03.NATIVE.SOURCE.ORDER` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-09 | `C03.NATIVE.SOURCE.Q_CACHE` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-10 | `C03.NATIVE.SOURCE.RELATIONS` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-11 | `C03.NATIVE.SOURCE.REPRESENTATIVES` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-12 | `C03.NATIVE.SOURCE.REP_CACHE` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-13 | `C03.NATIVE.SOURCE.REQUESTS` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-14 | `C03.SOURCE.CLIFFORD_DOMAIN` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-15 | `C03.SOURCE.COLOR_TENSOR` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-16 | `C03.SOURCE.COMMON_PREFACTOR` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-17 | `C03.SOURCE.COUPLING_MONOMIAL` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-18 | `C03.SOURCE.DIAGRAM_PHASE` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-19 | `C03.SOURCE.GAUGE_PARAMETER` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-20 | `C03.SOURCE.HYPERCHARGE_D` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-21 | `C03.SOURCE.HYPERCHARGE_E` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-22 | `C03.SOURCE.NORMALIZATION_DOMAIN` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-23 | `C03.SOURCE.ORDERED_FIELDS` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-24 | `C03.SOURCE.SPINOR_X` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-25 | `C03.SOURCE.SPINOR_Y` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-26 | `RV01.SOURCE.CONTEXT` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-27 | `RV02.SOURCE.CONTEXT` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-28 | `RV03.SOURCE.CONTEXT` | Resolve and check provenance/semantics. | Exact resolved value, phase/channel semantics, and all type metadata agree. | `PENDING` |
| SRC-29 | `RV04.SOURCE.CONTEXT` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-30 | `RV05.SOURCE.CONTEXT` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |
| SRC-31 | `RV06.SOURCE.CONTEXT` | Resolve and check provenance/semantics. | Exact resolved value and all type metadata agree. | `PENDING` |

Source totality gate: `31/31 SUPPORTED`, with zero unresolved or evidence-only locators.

## C. Trusted physics-operation vocabulary — all 19 required

Inspect the operation contract plus its Python and Julia implementations. For each operation, verify the exact input/output schema, scientific meaning, semantic/index/representation constraints, dimension/domain rules, provenance propagation, deterministic failure behavior, and absence of expected-answer branching. At least one positive control and one scientifically meaningful negative/adversarial control must be identified for every operation.

| ID | Operation | Implementations/evidence | Acceptance condition | Disposition / finding |
| --- | --- | --- | --- | --- |
| OP-01 | `ANGULAR_AVERAGE` | Operation contracts; C03 Python operations; Julia C03/RV route | Semantics and independent implementations agree. | `PENDING` |
| OP-02 | `DOMAIN_PREDICATE` | Operation contracts; C03/native Python operations; Julia route | Domain truth is computed, not asserted. | `PENDING` |
| OP-03 | `EPISTEMIC_CLASSIFICATION` | Operation contracts; C03/native Python operations; Julia route | Classification preserves evaluated/unevaluated distinctions. | `PENDING` |
| OP-04 | `EXACT_CLIFFORD_ACTION` | Operation contracts; C03 Python operations; Julia route | Exact Clifford action and domain constraints are faithful. | `PENDING` |
| OP-05 | `EXACT_MATRIX_PROJECTION` | Operation contracts; C03 Python operations; Julia route | Projection, basis, and index semantics are faithful. | `PENDING` |
| OP-06 | `GAUGE_GENERATOR_ACTION` | Operation contracts; C03 Python operations; Julia route | Generator representation/action is faithful. | `PENDING` |
| OP-07 | `INVERTIBLE_NORMALIZATION` | Operation contracts; C03 Python operations; Julia route | Nonzero/invertibility preconditions are checked. | `PENDING` |
| OP-08 | `LINEAR_COMBINATION` | Operation contracts; generic trusted evaluator; Julia route | Canonical coefficients and compatible types/units are enforced. | `PENDING` |
| OP-09 | `NORMALIZATION_MONOMIAL` | Operation contracts; C03 Python operations; Julia route | Monomial convention and provenance are faithful. | `PENDING` |
| OP-10 | `NORMALIZATION_RECIPROCAL` | Operation contracts; C03 Python operations; Julia route | Reciprocal rejects zero and preserves exactness. | `PENDING` |
| OP-11 | `NORMALIZATION_REFERENCE_SCALAR` | Operation contracts; C03 Python operations; Julia route | Reference scalar is source-derived, not answer-derived. | `PENDING` |
| OP-12 | `PERMUTATION_PARITY` | Operation contracts; C03/RV Python operations; Julia route | Ordering and exchange-sign conventions are faithful. | `PENDING` |
| OP-13 | `PRODUCT` | Operation contracts; generic trusted evaluator; Julia route | Canonical exact product and type/unit composition are enforced. | `PENDING` |
| OP-14 | `RELATION_REDUCTION` | Operation contracts; native Python operations; Julia route | Only declared relations reduce the expression. | `PENDING` |
| OP-15 | `TENSOR_DIFFERENCE` | Operation contracts; C03/RV Python operations; Julia route | Tensor shape/index/representation compatibility is enforced. | `PENDING` |
| OP-16 | `TENSOR_EXCHANGE_EIGENVALUE` | Operation contracts; C03/RV Python operations; Julia route | Exchange channel and eigenvalue sign are faithful. | `PENDING` |
| OP-17 | `TENSOR_SUM` | Operation contracts; C03/RV Python operations; Julia route | Tensor shape/index/representation compatibility is enforced. | `PENDING` |
| OP-18 | `WARD_REDUCTION` | Operation contracts; native Python operations; Julia route | Ward relation application and prerequisites are faithful. | `PENDING` |
| OP-19 | `OUTPUT_BIND` | Operation contracts; trusted evaluator; Julia route | Output root binds the recomputed parent and cannot bypass ancestry. | `PENDING` |

Operation totality gate: `19/19 SUPPORTED`, with no physics-specific implementation shared between candidate production and trusted verification in a way that defeats independence.

## D. Authoritative outputs, independent reconstruction, and claims — all 16 required

For every row inspect the complete ancestor subgraph, `verification_receipt.outputs[root_id=<root>]`, the Julia receipt, Lean certificate binding, applicable challenge coverage, and corresponding claim-ledger entry. Independently trace at least the final source-to-root calculation; do not rely only on the recorded status label.

| ID | Root | Claim ID | Acceptance condition | Disposition / finding |
| --- | --- | --- | --- | --- |
| ROOT-01 | `C03.OUTPUT.PHYSICAL_COEFFICIENT` | `C03.claim.PHYSICAL_COEFFICIENT` | Exact Python/Julia value, Lean binding, ancestry, challenges, and bounded claim agree. | `PENDING` |
| ROOT-02 | `C03.OUTPUT.EVANESCENT_COORDINATES` | `C03.claim.EVANESCENT_COORDINATES` | Exact Python/Julia value, Lean binding, ancestry, challenges, and bounded claim agree. | `PENDING` |
| ROOT-03 | `C03.OUTPUT.EVANESCENT_STATE` | `C03.claim.EVANESCENT_STATE` | Exact Python/Julia value, Lean binding, ancestry, challenges, and bounded claim agree. | `PENDING` |
| ROOT-04 | `RV01.OUTPUT.PHYSICAL_COEFFICIENT` | `RV01.claim.PHYSICAL_COEFFICIENT` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-05 | `RV01.OUTPUT.EVANESCENT_STATE` | `RV01.claim.EVANESCENT_STATE` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-06 | `RV02.OUTPUT.PHYSICAL_COEFFICIENT` | `RV02.claim.PHYSICAL_COEFFICIENT` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-07 | `RV02.OUTPUT.EVANESCENT_STATE` | `RV02.claim.EVANESCENT_STATE` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-08 | `RV03.OUTPUT.PHYSICAL_COEFFICIENT` | `RV03.claim.PHYSICAL_COEFFICIENT` | Exact independent routes, phase/channel ancestry, and bounded claim agree. | `PENDING` |
| ROOT-09 | `RV03.OUTPUT.EVANESCENT_STATE` | `RV03.claim.EVANESCENT_STATE` | Exact independent routes, phase/channel ancestry, and bounded claim agree. | `PENDING` |
| ROOT-10 | `RV03.OUTPUT.SOURCE_CHANNEL` | `RV03.claim.SOURCE_CHANNEL` | The explicit source channel is independently reconstructed and bound. | `PENDING` |
| ROOT-11 | `RV04.OUTPUT.PHYSICAL_COEFFICIENT` | `RV04.claim.PHYSICAL_COEFFICIENT` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-12 | `RV04.OUTPUT.EVANESCENT_STATE` | `RV04.claim.EVANESCENT_STATE` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-13 | `RV05.OUTPUT.PHYSICAL_COEFFICIENT` | `RV05.claim.PHYSICAL_COEFFICIENT` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-14 | `RV05.OUTPUT.EVANESCENT_STATE` | `RV05.claim.EVANESCENT_STATE` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-15 | `RV06.OUTPUT.PHYSICAL_COEFFICIENT` | `RV06.claim.PHYSICAL_COEFFICIENT` | Exact independent routes and bounded claim agree. | `PENDING` |
| ROOT-16 | `RV06.OUTPUT.EVANESCENT_STATE` | `RV06.claim.EVANESCENT_STATE` | Exact independent routes and bounded claim agree. | `PENDING` |

Root totality gate: `16/16 SUPPORTED`; every root must have `VERIFIED_EXACT`, complete applicable mandatory challenges, one Python receipt hash, one independently produced Julia receipt hash, one actual-runtime Lean certificate hash, and a claim ledger that includes explicit `does_not_claim` limits.

## E. Complete lowering and corruption census

| ID | Assertion under review | Evidence locator | Required reviewer action | Acceptance condition | Disposition / finding |
| --- | --- | --- | --- | --- | --- |
| DAG-01 | The graph contains exactly 31 source, 160 derived, and 16 output nodes. | `candidate.graph.nodes` | Recount by kind and compare all node IDs with the generated census. | `31 + 160 + 16 = 207` graph nodes; no hidden authoritative transcript node. | `PENDING` |
| DAG-02 | All 160 derived nodes use only the 19 permitted operations. | Derived nodes; frozen profile operation declarations | Enumerate operation usage and unknown/untyped paths. | Every derived node is typed, ancestral, and permitted. | `PENDING` |
| DAG-03 | All 16 roots are reached through `OUTPUT_BIND`. | Root nodes and profile root declarations | Trace each root to its recomputed parent. | No direct claimed-output or comparison-answer bypass. | `PENDING` |
| DAG-04 | Every derived-node value was independently recomputed. | Python per-node evidence; runtime certificate | Compare claims to evaluator outputs and execution evidence. | `160/160` recomputed; no preserved value grants authority. | `PENDING` |
| DAG-05 | Every single-node corruption is rejected despite preserving final claims. | Challenge results for `ALL_DERIVED_INTERMEDIATE_CORRUPTION` | Check all 160 instances and affected roots. | `160/160` rejected; zero unexpected survivors. | `PENDING` |

## F. Mandatory challenge evidence — all 373 instances

Inspect the frozen `challenge_specs`, every `challenge_packet`, and every `verification_receipt.challenge_results` row. Recompute each permitted-descendant set from the unmodified baseline and verify per-root applicability. The counts below are requirements, not sampling quotas.

| ID | Challenge specification | Instances | Acceptance condition | Disposition / finding |
| --- | --- | ---: | --- | --- |
| CH-01 | `ALL_DERIVED_INTERMEDIATE_CORRUPTION` | 160 | Every derived-node corruption is detected; zero survivors. | `PENDING` |
| CH-02 | `SOURCE_LOCATOR_MUST_RESOLVE` | 31 | Every invalid/unresolved typed locator is rejected. | `PENDING` |
| CH-03 | `UNKNOWN_OPERATION_FAILS_CLOSED` | 160 | Every derived-node unknown-operation substitution is rejected. | `PENDING` |
| CH-04 | `OUTPUT_BINDING_CORRUPTION_REJECTED` | 16 | Every authoritative output-binding corruption is rejected. | `PENDING` |
| CH-05 | `C03_N7_SOURCE_BOUNDARY` | 1 | N7 boundary violation is rejected with intended consequence. | `PENDING` |
| CH-06 | `C03_N8_SOURCE_BOUNDARY` | 1 | N8 boundary violation is rejected with intended consequence. | `PENDING` |
| CH-07 | `EVALUATED_ZERO_IS_NOT_UNEVALUATED` | 1 | Evaluated zero cannot be laundered into unevaluated status or vice versa. | `PENDING` |
| CH-08 | `PARENT_BYPASS_REJECTED` | 1 | Ancestry/parent bypass is rejected. | `PENDING` |
| CH-09 | `RV03_PHASE_SENSITIVITY` | 1 | Wrong RV03 phase/channel changes are detected. | `PENDING` |
| CH-10 | `STALE_EDGE_REJECTED` | 1 | Mutated/stale graph edge and self-expanded closure are rejected. | `PENDING` |

Challenge totality gate: `373/373 PASSED`, every accepted pre-freeze falsifier classified, every packet bound to the baseline graph, and no optional failure affecting a verified root.

## G. Julia, Lean, replay, and dependency closure

| ID | Assertion under review | Evidence locator | Required reviewer action | Acceptance condition | Disposition / finding |
| --- | --- | --- | --- | --- | --- |
| IND-01 | Julia/Nemo reconstructs all 16 roots from declared sources. | `formal/tooling/scientific_compute/julia/verified_calculator_c03_rv_v1.jl`; output receipts | Trace inputs and recompute all roots without Python intermediates. | `16/16` exact canonical values agree. | `PENDING` |
| IND-02 | Julia does not consume expected-output receipts. | Julia imports/data flow/generated closure | Search for output/oracle/candidate-value dependencies. | No comparison answer participates in computation. | `PENDING` |
| IND-03 | Shared facilities are domain-neutral. | Python/Julia implementation boundaries | Identify common code/data and classify it. | Physics-specific transformations remain independently implemented. | `PENDING` |
| FRM-01 | Lean parses the actual runtime certificate. | Bundle `runtime_certificate`; Lean checker invocation | Re-run checker on the frozen certificate. | Actual certificate and external file hash are accepted. | `PENDING` |
| FRM-02 | Lean binds contract, graph, sources, outputs, and allowed status. | Lean checker and certificate fields | Trace the checked hashes and theorem preconditions. | No parallel hand-authored object substitutes for runtime evidence. | `PENDING` |
| FRM-03 | Certificate mutations fail closed. | Certificate mutation tests | Alter graph, value, source hash, output binding, and status. | Every required mutation is rejected. | `PENDING` |
| REP-01 | Separate local processes reproduce the frozen object. | Milestone replay evidence | Independently replay twice from frozen inputs. | Both yield the frozen bundle identity. | `PENDING` |
| REP-02 | The generated closure is complete and not manually narrowed. | `dependency_manifests`; closure generator | Regenerate imports/artifact/runtime closure. | 54 Python, 5 Julia, 4 Lean, 9 fixed artifacts; zero unresolved and zero exclusions. | `PENDING` |
| REP-03 | Trusted execution does not require historical oracle access. | Generated closure and isolated replay | Inspect and, if feasible, deny/move oracle-only material. | Exact verification remains source-derived and fail-closed. | `PENDING` |
| REP-04 | Linux egress-denied qualification is independently assessed when available. | Linux result/failure artifact and acceptance criteria | Do not infer a pass from this matrix; inspect the actual CI artifact. | Separate Linux disposition is recorded; absence leaves this row pending. | `PENDING` |

## H. Authority and claim limits

| ID | Assertion under review | Evidence locator | Required reviewer action | Acceptance condition | Disposition / finding |
| --- | --- | --- | --- | --- | --- |
| AUTH-01 | Existing scientific authority is preserved claim by claim. | `authority_bindings`; claim ledger | Compare all 16 bindings with cited authority records. | Exact historical labels, scope, ceilings, and limitations agree. | `PENDING` |
| AUTH-02 | Calculator-profile review remains unearned before this review. | Authority binding and milestone | Check status and transition logic. | `SCIENTIFIC_REQUALIFICATION_NOT_EARNED` is unchanged. | `PENDING` |
| AUTH-03 | Computation cannot promote authority. | Lean non-promotion checks; receipt flags | Inspect both implementation and executed certificate. | `scientific_promotion=false`; no operation can alter authority. | `PENDING` |
| AUTH-04 | Product and production claims remain false. | Bundle, milestone, review result template | Inspect all summary surfaces. | `product_v1_release=false` and `production_activation=false`. | `PENDING` |
| AUTH-05 | Limitations are material and visible downstream. | All 16 claim-ledger entries | Inspect `limitations` and `does_not_claim`. | No root can be summarized as validating SU(5), CCFT, ToE, or global runner reliability. | `PENDING` |

## Required result and decision rule

The reviewer must return a separately hash-bound result containing:

- reviewer identity, eligibility, conflicts, date, reviewed Git commit, and tool/runtime versions;
- the hash of every artifact inspected and this matrix version;
- a disposition and evidence note for every matrix row;
- explicit totals for sources (`31`), operations (`19`), roots (`16`), derived nodes (`160`), challenge instances (`373`), and unexpected survivors (`0`);
- all discovered defects, amendments, common-mode assumptions, and residual limitations;
- one overall disposition: `SUPPORTED_WITHIN_STATED_COMPUTATIONAL_SCOPE`, `SUPPORTED_WITH_REQUIRED_AMENDMENTS`, or `NOT_SUPPORTED`;
- the exact statements `scientific_promotion = false`, `product_v1_release = false`, and `production_activation = false`.

`SUPPORTED_WITHIN_STATED_COMPUTATIONAL_SCOPE` is permitted only when every non-optional row is `SUPPORTED`, all census totals close, no unresolved material defect remains, and the reviewer affirms that `VERIFIED_EXACT` is justified for each of the 16 roots under the frozen contracts. A failed or amendment-required row cannot be averaged away. A review failure creates a new versioned repair lineage; it does not modify this frozen packet.
