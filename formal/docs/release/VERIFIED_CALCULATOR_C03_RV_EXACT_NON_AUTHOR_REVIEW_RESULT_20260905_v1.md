# C03/RV exact Verified Physics Calculator — non-author review result

Review date: `2026-09-05` (`America/Denver`)

Overall disposition: `SUPPORTED_WITH_REQUIRED_AMENDMENTS`

This is a computational review of the frozen C03/RV exact profile. It is not a scientific requalification, a product release decision, a production activation, or external expert peer review.

## Reviewer identity, eligibility, and limits

Reviewer: an OpenAI Codex AI agent acting as a non-author computational reviewer. I did not author the implementation, operation definitions, candidate packet, frozen evidence bundle, review request, checklist, or evidence matrix, and I made no change to any of them. I have no human institutional affiliation, financial interest, or personal conflict to declare. I was assigned this review after the target was frozen.

Independence limitation: this review and the authored implementation use an OpenAI model/provider environment and the same repository corpus. The Python and Julia routes share the same frozen source artifacts, source-material contract, profile, policy, canonical symbol set, field embedding, basis, conventions, relation/cache premises, and repository-maintained test assumptions. This review is therefore a genuine non-author computational check, but not an external domain-expert physics review and not independent experimental evidence.

The reviewer did not repair either material defect found below. The frozen packet remains unchanged.

## Exact target and custody

Git object reviewed:

- commit: `7d3d81fc3a4dcbff58d1ce02a4ec3cd2e581d516`
- tree: `446a04693f60dd8091972b6627d7442449cec5e9`
- parent: `ae9c9722b89e8e7b92e5afcd423a1272ad8d1d60`
- commit date: `2026-09-05T20:45:21-06:00`
- subject: `Define C03 RV qualification acceptance evidence`

The scoped implementation and evidence files were byte-clean against that commit before this result was created. The checklist names commit `9a118bf71d2501a839437f7630bf1de0c9c4190c` or, alternatively, an independent exact dependency-closure match. This review inspected the assigned later commit above and satisfied the checklist's alternative by regenerating and exactly matching every closure member. Unrelated pre-existing worktree changes were not inspected as review inputs and were not modified.

Frozen identities, independently recomputed with the repository canonical/domain-separated encodings:

| Object | Identity |
| --- | --- |
| Computation | `2b8ab72bd24775bfc8914e85546484f244dddc9cb5bd43dc116db0aacf2f4e8a` |
| Candidate | `fe0c6fa2133a7a9ed8bb94df3a91265e91d9db1a16206b487895a3c7e4353966` |
| Physics profile | `e131c6f94014082b8dd78bb680f1acdcf76e924b0cbe8fb62eafdda5af860617` |
| Verification policy | `ecda89e1e6b47db2f2ec8057656cd7d622944c0202eda58ab0cd907e48c2711b` |
| Candidate graph | `67375b58adb278dfa377cab633e29c261c8b1d90f7710e3e855523a7f96c58e6` |
| Verification receipt | `68f7e4c7f23c264da19e53e5cf24db1fcf8ae61c79a58848cc2f4e647045028f` |
| Runtime certificate | `5d08aa26f2f9396d76cefc2501339bb61fa3fb0df11f4b151c19e34257978e84` |
| Python evidence receipt | `71bf84a5d93beef014669ac75800e2d7846e7d3c81f98f6b53b8fb6f5ffe9654` |
| Julia evidence receipt | `09f178755fc8362f3cd8b702698b214c2d4b70baa5201ef7f2a30c18f581995f` |
| Lean evidence receipt | `6beca3e6a71e92c16f81c5f46705b7e74f7eaf3e741b8325ff503a8681984ee3` |
| Dependency closure | `5f08deda84148b2ac4249de4b44b914fd27c6274a127762017d614d5282cd204` |
| Authority binding | `44c6720eb71131285900fa836dc4feec88885afc37fb9633ac4cad383f70c024` |
| Authority attachment | `8989db6781d8fca32f6fc10fc1154afd3d77a50a6dd2744d7cb758e0c324d80e` |
| Exact milestone (domain identity) | `bf001d80e2ad9c87f45f801f5fe5fe051731799d70c5d3c62955f2c7ed61a7e2` |
| Frozen bundle (domain identity and filename) | `93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f` |
| Frozen bundle raw file SHA-256 | `7496caaa2f63915cf3adf5d81776ee3298decd204f745ae65e8a38b6c80b1bcf` |
| Runtime certificate canonical file SHA-256 | `aadd3b708691e642903f12ad7e8eb51df799ade8bc6dff9b4b258fb917e7fe42` |

Primary documents and executable review surfaces inspected:

| Artifact | Raw SHA-256 |
| --- | --- |
| `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_COMPUTATION_NON_AUTHOR_REVIEW_REQUEST_20260905_v1.md` | `9d31ef5991c774e784dc8c06434a7714d7291bc239d14ec0e3838748fc4f8f28` |
| `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_NON_AUTHOR_REVIEW_CHECKLIST_20260905_v1.md` | `9d39744ae30d0fcd8279bf2f52d8353ba3f3c9332382a66b9b2483245e5b4af8` |
| `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_NON_AUTHOR_REVIEW_EVIDENCE_MATRIX_20260905_v1.md` | `15301d996a36e73ada3ef4ec7db0c45479ebe279850ce198627bb0d2932766e3` |
| `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_LINUX_ACCEPTANCE_CRITERIA_20260905_v1.md` | `3993adc805784f87e4a4efeac99c96cd94561868f6fad946dec26eb8746c2081` |
| `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_LINUX_TEST_20260905_v1.json` | `0ad25b2f9dcdaefd5ee10082506b91f1bda95cfd5dffd82cff507c60f43d0f68` |
| `formal/docs/release/VERIFIED_CALCULATOR_IMPLEMENTATION_STATUS_20260905_v1.md` | `2decbd4a871c1b94bf00012d39e9296cf085ee5870dc9d6f4289af8ad3a295fb` |
| `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_MILESTONE_20260905_v1.md` | `7ad54d5c33ac713db26e28e468c1c3ef0d3c7711e917b14c8a4f0575bd246725` |
| `formal/docs/release/VERIFIED_CALCULATOR_POLICY_FREEZE_20260905_v1.md` | `c86c8b65f58c619c7896a2f157ae16e472821edaf2182d53f91089bc542e1244` |
| `formal/docs/release/VERIFIED_CALCULATOR_C03_RV_SOURCE_MATERIAL_CONTRACT_20260905_v1.json` | `b550bf1269092538cd2b43bd655ac275e7ca654d18631bb386a29286cefe42c2` |
| `.github/workflows/verified-calculator-c03-rv-exact-linux.yml` | `54413eff9dea1979298d41abfa2514c06a02b91bfbc10fdef313b8a2d1496ed8` |
| `formal/python/toe/generic_runner/verified_calculator/c03_rv_exact_verifier.py` | `4524b4a52b105502d461febc0dddaee0552ad794305b5bfe095362d7d08d32f5` |
| `formal/python/toe/generic_runner/verified_calculator/c03_rv_operation_contracts.py` | `64aae0dfc0fc214c8c0b63715f84d170fd22b8b346973dcebee2891a82ff31e1` |
| `formal/python/toe/generic_runner/verified_calculator/independent.py` | `dace6df0eacaaf2afeabe510360603383d579562f15718530fb665f243d63e82` |
| `formal/python/toe/generic_runner/verified_calculator/evidence.py` | `7e377b449c99959a31c8cbbcab9a4abec6c69db854d9b7809d95f3f1025c80bd` |
| `formal/tooling/scientific_compute/julia/verified_calculator_c03_rv_v1.jl` | `833657b7bb06d9c20f433cd91417f8625258d144038caf718b6dc31745469699` |
| `formal/toe_formal/ToeFormal/VerifiedCalculator/RuntimeCertificateV1.lean` | `0c37bd78d169289aecef21547f511f00ecaaf874ad02ef0e770f1e956a3a2ade` |
| `formal/python/tests/test_verified_calculator_v1.py` | `d310d8fa4f21d3387d219d26672a17d673de9c1a539d64d568bcad621e99d98d` |

All remaining inspected runtime files are individually hash-bound by the regenerated closure object: 54 Python files, 5 Julia files, 4 Lean files, and 9 fixed artifacts. Regeneration produced zero file differences, zero unresolved dynamic imports, zero unresolved runtime requirements, and zero manual exclusions. This is the exact artifact-hash inventory for the remaining closure members, rather than an unhashed path assertion.

The 15 distinct provenance artifacts reached by the 134 typed source references also matched their declared raw SHA-256 values: `646503046f4ab3fc0dd7109964cd8a47eb4b68ee38bab1bc7e2d4988c45372fa`, `029081f527b5605f38e8530a24d650fbca59446c40cadf339deb70a2518724bf`, `2751f36438f8f74a746f490064ce96bc88a7e89706a2f99213c11cc5cb1c4523`, `6e491932e709d29395c98a5f74e40d39be4f1d0cb5915cc04416d5a13ccf3750`, `d6cc476381c3bdebc5a1031c955aacede4bf8d808eb8df50a01b46030d7bbd04`, `17338c6fbe68015441e88976be1e3e8e56be4d9a7c8cb5fe757241c69f1b1d4a`, `36a1a4feceb6946f9bb412912ef0cea8377d2847e5c2fb1b291020b34769f726`, `d205c833592a57d4f43243445ec4ab3ee16b495aa0cd55dfcd3f2ad36b8aa523`, `83a50263d089810fd1cd21711b3a2b5691ed2ca816ce3d8c4fcc1675f9b38fc8`, `3e4e37560e1b98abe7df4d220f5bfee9b7ea2a48e1a61e47016118d235287bed`, `e86d536ce2f028c418fa8711f7cf72941afb18c15333dcf052377943cbd448f8`, `3d447864640648bbed12a08b02b94d28cfe718cd5ac49c79bbd184292cefc7c6`, `5efee72ec111483c022af97be30ae63e5235b3feda5e986c9172412522612269`, `e5091237105f119bafad82a98fc41a5810297df4890576afc857a84b9918f63a`, and `7277f21024000c18298ceae12b0c04e928e4fff30794c2b415a0319359623fb3`.

## Reproducible evidence commands and locators

Commands were run from repository root in PowerShell. `B` below means the frozen bundle JSON, `G = B.candidate.graph`, `R = B.verification_receipt`, and `C = B.runtime_certificate`.

| Code | Command/check and result |
| --- | --- |
| E01 | `git rev-parse HEAD^{commit}; git show -s --format=%T%n%P%n%cI%n%s 7d3d81fc...` and scoped `git diff --check 7d3d81fc... -- <trusted Python, Julia, Lean paths>` established the commit/tree/parent and clean scoped bytes. |
| E02 | PowerShell `Get-FileHash -Algorithm SHA256 -LiteralPath <artifact>` produced the raw hashes listed above. Domain identities were recomputed with `verified_calculator.canonical.digest` and each schema's `to_dict()` representation. |
| E03 | `python -m formal.python.toe.generic_runner.verified_calculator replay formal/docs/release/verified_calculator/c03_rv_exact/93691fa8...1471f.json` was run in two separate processes; both returned `replay_status: MATCHED`, the frozen bundle hash, computation ID, and `structural_and_hash_bindings_checked: true`. |
| E04 | A read-only Python closure audit called the repository closure generator and compared the complete regenerated dictionary and every member hash to `B.dependency_manifests[0]`: exact equality; counts `54/5/4/9`; unresolved `0/0`; exclusions `0`; file differences `0`. |
| E05 | `$env:VPC_REQUIRE_CROSS_LANGUAGE='1'; python -m pytest -q formal/python/tests/test_verified_calculator_v1.py` returned `32 passed, 1 warning in 235.46s`. |
| E06 | A fresh `api.evaluate_candidate` of the frozen candidate reconstructed graph `67375b...58e6`, 207 nodes and all 16 outputs. A separate full `execute_challenges` pass took 171.842 seconds and was object-for-object equal to all 373 frozen results. |
| E07 | An independent census script used `CandidatePacketV1.from_dict`, `FrozenEvidenceBundleV1`, resolver calls for every `SOURCE`, and canonical value hashing. It asserted exact sets for 31 sources, 160 derived nodes, 16 outputs, 19 operations, 134 locator receipts, 67 distinct typed locators, and zero unresolved/evidence-only locators. |
| E08 | An independent challenge audit rebuilt all accepted-on instances, descendant/root sets and packet domain hashes from the unmodified graph. It proved 373 unique packets, 373 unique results, exact set equality, baseline graph binding for every packet, exact affected-root equality, and zero unexpected survivors. |
| E09 | Static import/data-flow review used `rg` across the closure. The trusted package has no candidate/historical/oracle/acceptance import; candidate code is outside the trusted package; Julia receives profile, policy, request, candidate and source root, and does not consume Python intermediates or expected-output receipts. |
| E10 | The actual Lean executable was exercised through the cross-language suite and directly on the canonical embedded certificate. It accepted the exact certificate bytes and external file hash. Lean version `4.27.0-rc1`, commit `2fcce7258eeb6e324366bc25f9058293b04b7547`; checker executable SHA-256 `32f5061f76c4a3a55986cf21c8304927a2d639ce2e4acaadfddde56562264aa3`. |
| E11 | Lean adversarial checks wrote only temporary certificate copies, recomputed each temporary raw file SHA, and invoked the actual checker. Valid-hex mutations to graph hash, source-receipt hashes, output-value hash, four contract identity fields, allowed status ceiling, and the caller-supplied accepted-certificate hash were accepted; details are under D-01. |
| E12 | Value-type adversarial checks mutated only `C03.SOURCE.COLOR_TENSOR.value_type`, rebuilt `CandidatePacketV1`, and called trusted `api.evaluate_candidate`. Alternate allowed representation tag, nonzero dimension, `NATIVE_E` index space, and arbitrary domain were all accepted and issued new certificates; details are under D-02. |
| E13 | Authority audit recomputed the binding and attachment identities, compared all 16 claim-ledger records with the three cited authority records, and verified authority-only data remains outside computation/candidate/receipt identity inputs. |

Runtime: Windows `Windows-10-10.0.26200-SP0`; Python `3.10.11`, executable `C:\Program Files\Python310\python.exe`, executable SHA-256 `3cce33d75d6fdae4e004d0bdf149320b3147482a9caf370079dcb9c191a1b260`; SymPy `1.14.0`; jsonschema `4.26.0`; Julia `1.12.6`, executable SHA-256 `e7e81912dfe8a70ea9b5e7ac21b761fe0be678842109b411f877b8b17d1ed4b2`.

## Material defects and required amendments

### D-01 — the Lean checker accepts a caller-asserted certificate identity

Severity: material. Affects `GOV-03`, every `ROOT-*`, `FRM-02`, and `FRM-03`.

`RuntimeCertificateV1.lean:147-178` parses the actual JSON and checks schema, non-promotion, status, syntactic 64-hex strings, trace/output key agreement, and trace output digests. It does not recompute the domain-separated runtime-certificate hash, recompute graph hash from the trace, recompute source receipt hashes, bind `output_value_hashes` to exact output values, or bind the computation/candidate/profile/policy hashes to an independently supplied contract object. At lines 198-221 it validates `acceptedCertificateHash` only as 64 hex characters and prints that caller-supplied string on success. Python `independent.py:65-76` supplies its own `run.certificate.certificate_hash`, then treats the exact echo as Lean evidence. Python `evidence.py:96-110` performs stronger source/output/hash relations, but those are Python trust, not Lean proof.

Actual checker outcomes, each with a recomputed correct raw-file hash:

| Mutation | Exit/result |
| --- | --- |
| graph hash unrelated to trace, accepted hash argument `ff...ff` | exit `0`, `ACCEPTED ff...ff`, mutated file SHA `f67f529c...` |
| all source receipt hashes replaced by zero hashes | exit `0`, `ACCEPTED ff...ff`, mutated file SHA `35517bee...` |
| one exact output value hash replaced by zero hash | exit `0`, `ACCEPTED ff...ff`, mutated file SHA `2cdc6bab...` |
| computation/candidate/profile/policy identities replaced by unrelated valid hashes | exit `0`, `ACCEPTED ff...ff`, mutated file SHA `3717835c...` |
| status ceiling changed from `DETERMINISTICALLY_RECOMPUTED` to `VERIFIED_EXACT` | exit `0`, `ACCEPTED ff...ff`, mutated file SHA `2768134b...` |
| unchanged certificate with caller-chosen accepted hash `00...00` | exit `0`, `ACCEPTED 00...00`, canonical file SHA `aadd3b70...` |

Required amendment: a new versioned checker must derive or recompute the certificate identity it reports, cryptographically bind the contract identities, graph, source receipts, exact output values, trace output digests, allowed status and non-promotion flag, and reject every listed mutation. A new evidence lineage must be generated; this frozen bundle must not be edited.

### D-02 — frozen per-node value-type metadata is not enforced

Severity: material. Affects all `OP-*` acceptance conditions because those require enforceable semantic/index/representation/dimension/unit/domain contracts.

`c03_rv_exact_verifier.py:56-75` fixes node set, kind, operation, parents, semantic type, and a coarse output-vs-document mathematical-kind condition. It does not compare `dimension`, `unit_convention`, `index_spaces`, `representation_tags`, or `domain` to an exact source/derived signature. `c03_rv_operation_contracts.py:18-80` records unit/domain/semantic requirements as descriptive strings, not an executable edge/type relation. The source-material check at lines 99-117 binds semantic type and value digest but not the missing type metadata.

Trusted evaluation accepted four independently mutated candidates for `C03.SOURCE.COLOR_TENSOR`:

| Mutation | Issued certificate |
| --- | --- |
| `representation_tags = ["BMHV"]` | `a011b81318f07bc63c68cb081e0940c870115f61c3485c016da5cd9f8df9f489` |
| `dimension = ["1","0","0"]` | `1bf0a20ebae4eeabc57102105d095cdcb30d99017e380b5b449ec07c5c5aab6f` |
| `index_spaces = ["NATIVE_E"]` | `44011d6840ce37473570efd3fc8dbba6276be29d2286db1a5ab68904980b0040` |
| `domain = {"profile":"OTHER"}` | `8e0cb1218148dc145dd08e5c687e1de508c5fdb6ae62e6f0f2e068356b365bac` |

Required amendment: exact source and derived `ValueTypeV1` signatures, including edge compatibility and declared unit/domain rules, must be executable trusted constraints. Add mechanically complete metadata mutation challenges (not just unknown-operation and claimed-value corruption) and create a new frozen lineage.

### D-03 — Linux qualification is absent

Severity: residual release limitation, not evidence of a failed Linux run. Affects `REP-04` only.

The Linux object says `DEFINED_NOT_EXECUTED`; the status document has `successful_result_artifact: null`. The workflow definition is not a result artifact. This row remains `PENDING` exactly as required by the matrix.

## A. Custody, independence, and anti-tautology dispositions

| ID | Disposition | Evidence/finding |
| --- | --- | --- |
| GOV-01 | `SUPPORTED` | Reviewer declaration above; non-author AI with shared-provider/common-source limitation, not external expert peer review. |
| GOV-02 | `SUPPORTED` | E02/E03; recomputed domain identity equals filename and matrix target. |
| GOV-03 | `AMENDMENT_REQUIRED` | All Python bundle edges resolve, but D-01 shows the claimed Lean certificate identity edge is circular/caller-asserted. |
| GOV-04 | `SUPPORTED` | E07/E09; all authoritative inputs resolve to declared source artifacts; no expected-output receipt feeds a source or operation. |
| GOV-05 | `SUPPORTED` | E04/E09; one-way trusted imports, complete closure, no historical/candidate/oracle/acceptance import in trusted package. |
| GOV-06 | `SUPPORTED` | E13; authority attachment changes outer authority/bundle identity only, not computation/candidate/receipt identity. |
| GOV-07 | `SUPPORTED` | E01/E02; frozen bytes were not modified; this result is a new file and amendments require new lineage. |
| GOV-08 | `SUPPORTED` | E13; every claim has computational limits and explicit non-claims; no SU(5), CCFT, ToE, product, or production promotion. |

## B. Source-binding census: all 31

For each row the locator is the unique matching `G.nodes[node_id]`, `B.candidate.source_bindings[node_id]`, and `R.source_evidence` material/evidence receipts. E07 resolved every `JsonPointerValueRef` against the declared artifact bytes, compared its canonical value digest, semantic type and the frozen node's complete metadata, and found zero baseline mismatches. The reference count is the number of independently resolved evidence references in that row. D-02 is a fail-closed acceptance defect for alternate candidate metadata; it does not change the fact that all 31 source records in this frozen packet agree with their referenced values and metadata.

| ID | Source node | Semantic type | Refs | Disposition |
| --- | --- | --- | ---: | --- |
| SRC-01 | `C03.CONVENTION.WILSON_SYMBOL` | `SYMBOL` | 1 | `SUPPORTED` |
| SRC-02 | `C03.NATIVE.SOURCE.COLUMNS` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-03 | `C03.NATIVE.SOURCE.DEFECTS` | `INHERITED_RELATION_CONTEXT` | 1 | `SUPPORTED` |
| SRC-04 | `C03.NATIVE.SOURCE.DUAL_CACHE` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-05 | `C03.NATIVE.SOURCE.K_CACHE` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-06 | `C03.NATIVE.SOURCE.LEDGER` | `INHERITED_RELATION_CONTEXT` | 1 | `SUPPORTED` |
| SRC-07 | `C03.NATIVE.SOURCE.OCCURRENCES` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-08 | `C03.NATIVE.SOURCE.ORDER` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-09 | `C03.NATIVE.SOURCE.Q_CACHE` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-10 | `C03.NATIVE.SOURCE.RELATIONS` | `INHERITED_RELATION_CONTEXT` | 1 | `SUPPORTED` |
| SRC-11 | `C03.NATIVE.SOURCE.REPRESENTATIVES` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-12 | `C03.NATIVE.SOURCE.REP_CACHE` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-13 | `C03.NATIVE.SOURCE.REQUESTS` | `SOURCE_CONTEXT` | 1 | `SUPPORTED` |
| SRC-14 | `C03.SOURCE.CLIFFORD_DOMAIN` | `CLIFFORD_DOMAIN_CONTEXT` | 3 | `SUPPORTED` |
| SRC-15 | `C03.SOURCE.COLOR_TENSOR` | `COLOR_EXCHANGE_CONTEXT` | 2 | `SUPPORTED` |
| SRC-16 | `C03.SOURCE.COMMON_PREFACTOR` | `SYMBOLIC_SCALAR` | 1 | `SUPPORTED` |
| SRC-17 | `C03.SOURCE.COUPLING_MONOMIAL` | `GAUGE_MONOMIAL` | 1 | `SUPPORTED` |
| SRC-18 | `C03.SOURCE.DIAGRAM_PHASE` | `RAW_FEYNMAN_LEDGER` | 9 | `SUPPORTED` |
| SRC-19 | `C03.SOURCE.GAUGE_PARAMETER` | `GAUGE_SYMBOL_CONTEXT` | 2 | `SUPPORTED` |
| SRC-20 | `C03.SOURCE.HYPERCHARGE_D` | `RATIONAL` | 1 | `SUPPORTED` |
| SRC-21 | `C03.SOURCE.HYPERCHARGE_E` | `RATIONAL` | 1 | `SUPPORTED` |
| SRC-22 | `C03.SOURCE.NORMALIZATION_DOMAIN` | `NORMALIZATION_DOMAIN_CONTEXT` | 2 | `SUPPORTED` |
| SRC-23 | `C03.SOURCE.ORDERED_FIELDS` | `LABELLED_FIELD_CONTEXT` | 2 | `SUPPORTED` |
| SRC-24 | `C03.SOURCE.SPINOR_X` | `SOURCE_BILINEAR_CONTEXT` | 5 | `SUPPORTED` |
| SRC-25 | `C03.SOURCE.SPINOR_Y` | `SOURCE_BILINEAR_CONTEXT` | 5 | `SUPPORTED` |
| SRC-26 | `RV01.SOURCE.CONTEXT` | `SOURCE_CONTEXT` | 16 | `SUPPORTED` |
| SRC-27 | `RV02.SOURCE.CONTEXT` | `SOURCE_CONTEXT` | 16 | `SUPPORTED` |
| SRC-28 | `RV03.SOURCE.CONTEXT` | `SOURCE_CONTEXT` | 14 | `SUPPORTED` |
| SRC-29 | `RV04.SOURCE.CONTEXT` | `SOURCE_CONTEXT` | 13 | `SUPPORTED` |
| SRC-30 | `RV05.SOURCE.CONTEXT` | `SOURCE_CONTEXT` | 14 | `SUPPORTED` |
| SRC-31 | `RV06.SOURCE.CONTEXT` | `SOURCE_CONTEXT` | 14 | `SUPPORTED` |

Source totality: `31/31 SUPPORTED`; 134 references, 67 distinct typed locators, zero unresolved and zero evidence-only locators.

## C. Trusted operation vocabulary: all 19

E05-E09 establish the positive-control count below, exact Python/Julia agreement, and a corruption plus unknown-operation negative control for every instantiated derived node. However, the matrix requires enforceable semantic/index/representation/dimension/unit/domain schemas and scientifically meaningful negative controls, not merely descriptive contract text. D-02 is a systematic failure of that acceptance condition, so none of the 19 operations earns `SUPPORTED` even though its frozen positive evaluations agree.

| ID | Operation | Frozen uses | Disposition | Evidence/finding |
| --- | --- | ---: | --- | --- |
| OP-01 | `ANGULAR_AVERAGE` | 7 | `AMENDMENT_REQUIRED` | Positive results agree; D-02 type/domain enforcement gap. |
| OP-02 | `DOMAIN_PREDICATE` | 19 | `AMENDMENT_REQUIRED` | Predicates compute frozen truth; declared node domain metadata can be substituted. |
| OP-03 | `EPISTEMIC_CLASSIFICATION` | 7 | `AMENDMENT_REQUIRED` | Evaluated-state controls pass; complete typed prerequisite contract is not enforced. |
| OP-04 | `EXACT_CLIFFORD_ACTION` | 15 | `AMENDMENT_REQUIRED` | Exact action agrees; BMHV/index/domain metadata is not signature-bound. |
| OP-05 | `EXACT_MATRIX_PROJECTION` | 24 | `AMENDMENT_REQUIRED` | Projection values agree; shape/index metadata contract is not signature-bound. |
| OP-06 | `GAUGE_GENERATOR_ACTION` | 6 | `AMENDMENT_REQUIRED` | Generator images agree; representation metadata can be substituted. |
| OP-07 | `INVERTIBLE_NORMALIZATION` | 7 | `AMENDMENT_REQUIRED` | Frozen inverse controls pass; type/unit/domain signature remains descriptive. |
| OP-08 | `LINEAR_COMBINATION` | 9 | `AMENDMENT_REQUIRED` | Exact values agree; compatible types/units are not fully enforced as metadata. |
| OP-09 | `NORMALIZATION_MONOMIAL` | 1 | `AMENDMENT_REQUIRED` | Frozen monomial agrees; typed/unit signature remains descriptive. |
| OP-10 | `NORMALIZATION_RECIPROCAL` | 1 | `AMENDMENT_REQUIRED` | Zero rejection/exact reciprocal tests pass; type/unit signature remains descriptive. |
| OP-11 | `NORMALIZATION_REFERENCE_SCALAR` | 1 | `AMENDMENT_REQUIRED` | Source-derived result agrees; type/unit/domain signature remains descriptive. |
| OP-12 | `PERMUTATION_PARITY` | 1 | `AMENDMENT_REQUIRED` | Sign agrees; index/representation signature remains descriptive. |
| OP-13 | `PRODUCT` | 26 | `AMENDMENT_REQUIRED` | Exact products agree; dimension/unit composition metadata is not enforced. |
| OP-14 | `RELATION_REDUCTION` | 10 | `AMENDMENT_REQUIRED` | Frozen reductions/residuals agree; basis/index/domain metadata is not bound. |
| OP-15 | `TENSOR_DIFFERENCE` | 3 | `AMENDMENT_REQUIRED` | Exact differences agree; identical shape/index/representation metadata is not enforced. |
| OP-16 | `TENSOR_EXCHANGE_EIGENVALUE` | 1 | `AMENDMENT_REQUIRED` | Frozen exchange sign agrees; channel/representation metadata is not bound. |
| OP-17 | `TENSOR_SUM` | 14 | `AMENDMENT_REQUIRED` | Exact sums agree; matching shape/index/representation metadata is not enforced. |
| OP-18 | `WARD_REDUCTION` | 8 | `AMENDMENT_REQUIRED` | Ward results agree; routing/index/domain metadata is not signature-bound. |
| OP-19 | `OUTPUT_BIND` | 16 | `AMENDMENT_REQUIRED` | Parent/value ancestry is enforced; full identical value-type metadata is not. |

Operation totality: `0/19 SUPPORTED`, `19/19 AMENDMENT_REQUIRED`; frozen positive-use census `160/160` and no unknown operations.

## D. Roots and claims: all 16

E05-E08 reconstructed every value and complete ancestry in Python and Julia, with matching canonical hashes and bounded claim-ledger entries. The matrix's root totality gate also requires an actual-runtime Lean certificate hash. D-01 shows that the Lean acceptance hash is caller-asserted rather than derived. Accordingly every root is amendment-required even though the underlying exact Python/Julia result and challenge coverage agree.

| ID | Root / exact value summary | Exact output value hash | Claim | Disposition |
| --- | --- | --- | --- | --- |
| ROOT-01 | `C03.OUTPUT.PHYSICAL_COEFFICIENT = xi1 - 1` | `f4a8b12315f1b8988c6e94b08df23c4bb5f847ec723c26760e0b1c4d00f105c1` | `C03.claim.PHYSICAL_COEFFICIENT` | `AMENDMENT_REQUIRED` |
| ROOT-02 | `C03.OUTPUT.EVANESCENT_COORDINATES`, exact 14-vector in the bundle | `59c9bde97896bee76cb2175664d69bedea39f0c02eda55fcb5b25b221022dba0` | `C03.claim.EVANESCENT_COORDINATES` | `AMENDMENT_REQUIRED` |
| ROOT-03 | `C03.OUTPUT.EVANESCENT_STATE = EVALUATED_NONZERO` | `707f5ec2eb2c8d4eee0ffa8fbfe5d9836a4645a48635230c6ddb047f6aef8b84` | `C03.claim.EVANESCENT_STATE` | `AMENDMENT_REQUIRED` |
| ROOT-04 | `RV01.OUTPUT.PHYSICAL_COEFFICIENT = -g3^2*xi3/3 - g3^2` | `6feb15ffc21da4c16214941871c4cb6e6e627ec087274d151fdfd9ddd689fb79` | `RV01.claim.PHYSICAL_COEFFICIENT` | `AMENDMENT_REQUIRED` |
| ROOT-05 | `RV01.OUTPUT.EVANESCENT_STATE = EVALUATED_ZERO` | `af9313261daa285b5907c78d50166aa122d021486712bcfbd36bd55892eaf27b` | `RV01.claim.EVANESCENT_STATE` | `AMENDMENT_REQUIRED` |
| ROOT-06 | `RV02.OUTPUT.PHYSICAL_COEFFICIENT = 2*g3^2*xi3/3 + 2*g3^2` | `7de34400005fa5b796b70553ac0131a580ed0830aa81b7f5a90a74c22586f4a6` | `RV02.claim.PHYSICAL_COEFFICIENT` | `AMENDMENT_REQUIRED` |
| ROOT-07 | `RV02.OUTPUT.EVANESCENT_STATE = EVALUATED_ZERO` | `af9313261daa285b5907c78d50166aa122d021486712bcfbd36bd55892eaf27b` | `RV02.claim.EVANESCENT_STATE` | `AMENDMENT_REQUIRED` |
| ROOT-08 | `RV03.OUTPUT.PHYSICAL_COEFFICIENT = -g2^2*xi2/4 - 3*g2^2/4` | `58b608ce79bcaeccd3a216c280650d6d731161f9b2386f9053583fcd3f5f9d93` | `RV03.claim.PHYSICAL_COEFFICIENT` | `AMENDMENT_REQUIRED` |
| ROOT-09 | `RV03.OUTPUT.EVANESCENT_STATE = EVALUATED_ZERO` | `af9313261daa285b5907c78d50166aa122d021486712bcfbd36bd55892eaf27b` | `RV03.claim.EVANESCENT_STATE` | `AMENDMENT_REQUIRED` |
| ROOT-10 | `RV03.OUTPUT.SOURCE_CHANNEL = WEAK_TRIPLET_A_FLAVOR` | `741a3e65c299f5bff2701da5801427c0e9392036f7cc90ada8a3d24f16138861` | `RV03.claim.SOURCE_CHANNEL` | `AMENDMENT_REQUIRED` |
| ROOT-11 | `RV04.OUTPUT.PHYSICAL_COEFFICIENT = g1^2*xi1/12 + g1^2/4` | `fb095d802ad60ece9633bebb7df1fd25200aff6bdc762a6678b97e44ca2cb0e1` | `RV04.claim.PHYSICAL_COEFFICIENT` | `AMENDMENT_REQUIRED` |
| ROOT-12 | `RV04.OUTPUT.EVANESCENT_STATE = EVALUATED_ZERO` | `af9313261daa285b5907c78d50166aa122d021486712bcfbd36bd55892eaf27b` | `RV04.claim.EVANESCENT_STATE` | `AMENDMENT_REQUIRED` |
| ROOT-13 | `RV05.OUTPUT.PHYSICAL_COEFFICIENT = 2*g3^2*xi3/3 + 2*g3^2` | `7de34400005fa5b796b70553ac0131a580ed0830aa81b7f5a90a74c22586f4a6` | `RV05.claim.PHYSICAL_COEFFICIENT` | `AMENDMENT_REQUIRED` |
| ROOT-14 | `RV05.OUTPUT.EVANESCENT_STATE = EVALUATED_ZERO` | `af9313261daa285b5907c78d50166aa122d021486712bcfbd36bd55892eaf27b` | `RV05.claim.EVANESCENT_STATE` | `AMENDMENT_REQUIRED` |
| ROOT-15 | `RV06.OUTPUT.PHYSICAL_COEFFICIENT = g1^2*xi1/9 + g1^2/3` | `d61a7f6b97996fbe658dd37fa8472f3a02fc6c5064a705e14f804e88f7425cbe` | `RV06.claim.PHYSICAL_COEFFICIENT` | `AMENDMENT_REQUIRED` |
| ROOT-16 | `RV06.OUTPUT.EVANESCENT_STATE = EVALUATED_ZERO` | `af9313261daa285b5907c78d50166aa122d021486712bcfbd36bd55892eaf27b` | `RV06.claim.EVANESCENT_STATE` | `AMENDMENT_REQUIRED` |

Root totality: `0/16 SUPPORTED`, `16/16 AMENDMENT_REQUIRED`; Python/Julia exact values `16/16` agree, challenge coverage `16/16` complete, claims `16/16` bounded, Lean identity binding `0/16` established.

## E. Derived-node census: all 160

Each disposition below is for the exact frozen node at `G.nodes[node_id]`; positive evidence is its Python trace row and Julia recomputation, while negative evidence is its one result in `R.challenge_results[0:160]` and one result in `R.challenge_results[191:351]`. Thus every row has both single-node corruption and unknown-operation rejection evidence. These node dispositions concern the actual frozen lowering and values; D-02 separately prevents clean operation-contract qualification.

### C03 derived nodes: 40/40

| Node | Operation | Parents | Disposition |
| --- | --- | --- | --- |
| `C03.DERIVED.CHARGE_PRODUCT` | `PRODUCT` | `HYPERCHARGE_D`, `HYPERCHARGE_E` | `SUPPORTED` |
| `C03.DERIVED.COLOR_EXCHANGE_SIGN` | `TENSOR_EXCHANGE_EIGENVALUE` | `COLOR_TENSOR` | `SUPPORTED` |
| `C03.DERIVED.COMMON_NORMALIZED_COEFFICIENT` | `INVERTIBLE_NORMALIZATION` | `RAW_GRAPH`, `TARGET_NORMALIZATION_SCALE`, `REFERENCE_SCALAR` | `SUPPORTED` |
| `C03.DERIVED.COVARIANT_NUMERATOR` | `LINEAR_COMBINATION` | `PT_SUM`, `L_SUM`, `GAUGE_PARAMETER` | `SUPPORTED` |
| `C03.DERIVED.EXCHANGE_OCCURRENCE_WEIGHT` | `PRODUCT` | `GRASSMANN_EXCHANGE_SIGN`, `COLOR_EXCHANGE_SIGN` | `SUPPORTED` |
| `C03.DERIVED.GRASSMANN_EXCHANGE_SIGN` | `PERMUTATION_PARITY` | `ORDERED_FIELDS` | `SUPPORTED` |
| `C03.DERIVED.G_SUM` | `TENSOR_SUM` | `IDENTITY_OCCURRENCE_WEIGHT`, `EXCHANGE_OCCURRENCE_WEIGHT`, `G_X`, `G_Y` | `SUPPORTED` |
| `C03.DERIVED.G_X` | `EXACT_CLIFFORD_ACTION` | `SPINOR_X`, `SPINOR_Y`, `CLIFFORD_DOMAIN` | `SUPPORTED` |
| `C03.DERIVED.G_Y` | `EXACT_CLIFFORD_ACTION` | `SPINOR_Y`, `SPINOR_X`, `CLIFFORD_DOMAIN` | `SUPPORTED` |
| `C03.DERIVED.IDENTITY_OCCURRENCE_WEIGHT` | `PRODUCT` | `ORDERED_FIELDS` | `SUPPORTED` |
| `C03.DERIVED.L_SUM` | `TENSOR_SUM` | `IDENTITY_OCCURRENCE_WEIGHT`, `EXCHANGE_OCCURRENCE_WEIGHT`, `L_X`, `L_Y` | `SUPPORTED` |
| `C03.DERIVED.L_X` | `WARD_REDUCTION` | `SPINOR_X`, `SPINOR_Y`, `CLIFFORD_DOMAIN` | `SUPPORTED` |
| `C03.DERIVED.L_Y` | `WARD_REDUCTION` | `SPINOR_Y`, `SPINOR_X`, `CLIFFORD_DOMAIN` | `SUPPORTED` |
| `C03.DERIVED.PT_SUM` | `TENSOR_DIFFERENCE` | `G_SUM`, `L_SUM` | `SUPPORTED` |
| `C03.DERIVED.RAW_GRAPH` | `PRODUCT` | `COVARIANT_NUMERATOR`, `DIAGRAM_PHASE`, `CHARGE_PRODUCT` | `SUPPORTED` |
| `C03.DERIVED.REFERENCE_SCALAR` | `NORMALIZATION_REFERENCE_SCALAR` | `COMMON_PREFACTOR`, `REMOVED_MONOMIAL`, `NORMALIZATION_DOMAIN` | `SUPPORTED` |
| `C03.DERIVED.REMOVED_MONOMIAL` | `NORMALIZATION_MONOMIAL` | `COUPLING_MONOMIAL`, `WILSON_SYMBOL` | `SUPPORTED` |
| `C03.DERIVED.TARGET_NORMALIZATION_SCALE` | `NORMALIZATION_RECIPROCAL` | `REFERENCE_SCALAR` | `SUPPORTED` |
| `C03.NATIVE.AMBIENT` | `PRODUCT` | `JOIN`, `CLIFFORD`, `ANGULAR`, `CHANNEL`, `LEGACY`, `WEIGHTS`, `PHASE`, `CHARGE_PRODUCT` | `SUPPORTED` |
| `C03.NATIVE.ANGULAR` | `ANGULAR_AVERAGE` | `OCCURRENCES`, `JOIN`, `CLIFFORD_DOMAIN` | `SUPPORTED` |
| `C03.NATIVE.CHANNEL` | `LINEAR_COMBINATION` | `OCCURRENCES`, `GAUGE_PARAMETER`, `DIAGRAM_PHASE` | `SUPPORTED` |
| `C03.NATIVE.CLIFFORD` | `EXACT_CLIFFORD_ACTION` | `OCCURRENCES`, `JOIN`, `CLIFFORD_DOMAIN` | `SUPPORTED` |
| `C03.NATIVE.COORDINATES` | `EXACT_MATRIX_PROJECTION` | `DUAL`, `AMBIENT` | `SUPPORTED` |
| `C03.NATIVE.DUAL` | `RELATION_REDUCTION` | `RELATIONS`, `REPRESENTATIVE`, `DUAL_CACHE` | `SUPPORTED` |
| `C03.NATIVE.JOIN` | `DOMAIN_PREDICATE` | `OCCURRENCES`, `REQUESTS`, `DEFECTS`, `COLUMNS`, `ORDER`, `LEDGER` | `SUPPORTED` |
| `C03.NATIVE.LEAKAGE` | `EXACT_MATRIX_PROJECTION` | `LEAKAGE_ROW`, `PROJECTED` | `SUPPORTED` |
| `C03.NATIVE.LEAKAGE_ROW` | `LINEAR_COMBINATION` | `DEFECTS`, `JOIN`, `CLIFFORD_DOMAIN` | `SUPPORTED` |
| `C03.NATIVE.LEGACY` | `PRODUCT` | `OCCURRENCES`, `CLIFFORD`, `ANGULAR` | `SUPPORTED` |
| `C03.NATIVE.PHASE` | `PRODUCT` | `DIAGRAM_PHASE` | `SUPPORTED` |
| `C03.NATIVE.PROJECTED` | `EXACT_MATRIX_PROJECTION` | `REPRESENTATIVE`, `COORDINATES` | `SUPPORTED` |
| `C03.NATIVE.QUOTIENT` | `EXACT_MATRIX_PROJECTION` | `REPRESENTATIVE`, `DUAL`, `Q_CACHE` | `SUPPORTED` |
| `C03.NATIVE.RELATIONS` | `RELATION_REDUCTION` | source `RELATIONS`, `JOIN` | `SUPPORTED` |
| `C03.NATIVE.RELATION_CERTIFICATE` | `RELATION_REDUCTION` | `RELATIONS`, `DUAL`, `REPRESENTATIVE`, `QUOTIENT`, `REMAINDER` | `SUPPORTED` |
| `C03.NATIVE.RELATION_PART` | `EXACT_MATRIX_PROJECTION` | `REMAINDER`, `AMBIENT` | `SUPPORTED` |
| `C03.NATIVE.REMAINDER` | `TENSOR_DIFFERENCE` | `QUOTIENT`, `K_CACHE` | `SUPPORTED` |
| `C03.NATIVE.REPRESENTATIVE` | `EXACT_MATRIX_PROJECTION` | source `REPRESENTATIVES`, `REP_CACHE`, `JOIN` | `SUPPORTED` |
| `C03.NATIVE.RESIDUAL` | `TENSOR_DIFFERENCE` | `AMBIENT`, `PROJECTED`, `RELATION_PART`, `WITNESS`, `RELATIONS` | `SUPPORTED` |
| `C03.NATIVE.STATE` | `EPISTEMIC_CLASSIFICATION` | `COORDINATES`, `RESIDUAL`, `LEAKAGE`, `RELATION_CERTIFICATE` | `SUPPORTED` |
| `C03.NATIVE.WEIGHTS` | `PRODUCT` | `OCCURRENCES`, `IDENTITY_OCCURRENCE_WEIGHT`, `EXCHANGE_OCCURRENCE_WEIGHT` | `SUPPORTED` |
| `C03.NATIVE.WITNESS` | `RELATION_REDUCTION` | `RELATIONS`, `AMBIENT`, `PROJECTED` | `SUPPORTED` |

### RV derived nodes: explicit 120/120 template instantiations

For every row below, `R` is instantiated independently as `RV01`, `RV02`, `RV03`, `RV04`, `RV05`, and `RV06`. The six disposition cells explicitly cover the six distinct nodes `R.<suffix>` and total 120 nodes.

| Suffix | Operation | Parents relative to `R` | RV01 | RV02 | RV03 | RV04 | RV05 | RV06 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ABSENCE_DOMAIN` | `DOMAIN_PREDICATE` | `SOURCE.CONTEXT`, `DOMAIN`, `WORDS` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `CHANNEL` | `DOMAIN_PREDICATE` | `SOURCE.CONTEXT`, `DOMAIN`, `TENSOR` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `COVARIANT` | `LINEAR_COMBINATION` | `SOURCE.CONTEXT`, `SPINOR_PROJECTION` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `DOMAIN` | `DOMAIN_PREDICATE` | `SOURCE.CONTEXT` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `GROUP` | `EXACT_MATRIX_PROJECTION` | `TENSOR`, `GROUP_IMAGE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `GROUP_IMAGE` | `GAUGE_GENERATOR_ACTION` | `SOURCE.CONTEXT`, `TENSOR`, `CHANNEL` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `METRIC_IMAGE` | `EXACT_CLIFFORD_ACTION` | `SOURCE.CONTEXT`, `WORDS`, `TREE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `NORMALIZED` | `INVERTIBLE_NORMALIZATION` | `RAW`, `TREE_MAP` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `PHASE` | `PRODUCT` | `SOURCE.CONTEXT`, `WORDS` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `POLE` | `RELATION_REDUCTION` | `SOURCE.CONTEXT`, `WORD_REDUCTIONS`, `ABSENCE_DOMAIN` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `RAW` | `PRODUCT` | `SOURCE.CONTEXT`, `GROUP`, `COVARIANT`, `PHASE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `SPINOR_PROJECTION` | `EXACT_MATRIX_PROJECTION` | `TREE`, `METRIC_IMAGE`, `WARD_IMAGE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `STATE` | `EPISTEMIC_CLASSIFICATION` | `POLE`, `ABSENCE_DOMAIN`, `WORD_COVERAGE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `TENSOR` | `TENSOR_SUM` | `SOURCE.CONTEXT`, `DOMAIN` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `TREE` | `TENSOR_SUM` | `SOURCE.CONTEXT`, `DOMAIN` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `TREE_MAP` | `EXACT_MATRIX_PROJECTION` | `SOURCE.CONTEXT`, `TENSOR`, `TREE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `WARD_IMAGE` | `WARD_REDUCTION` | `SOURCE.CONTEXT`, `WORDS`, `TREE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `WORDS` | `PRODUCT` | `SOURCE.CONTEXT`, `DOMAIN`, `TREE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `WORD_COVERAGE` | `ANGULAR_AVERAGE` | `SOURCE.CONTEXT`, `ABSENCE_DOMAIN`, `WORDS` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |
| `WORD_REDUCTIONS` | `EXACT_CLIFFORD_ACTION` | `WORD_COVERAGE` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` | `SUPPORTED` |

Derived-node totality: `160/160 SUPPORTED` for the frozen graph/value reconstruction and both mandatory per-node challenges; no sampling.

## F. Graph and challenge dispositions

### Graph rows

| ID | Disposition | Evidence/finding |
| --- | --- | --- |
| DAG-01 | `SUPPORTED` | E06/E07; exactly 31 source + 160 derived + 16 output = 207 nodes; no hidden authoritative transcript node. |
| DAG-02 | `SUPPORTED` | The 160-node table above and operation-use counts close exactly over the permitted 19 identifiers. D-02 is separately recorded against operation contract enforcement. |
| DAG-03 | `SUPPORTED` | All 16 output nodes have operation `OUTPUT_BIND`, exactly one fixed parent, and the declared root set. |
| DAG-04 | `SUPPORTED` | E05-E07; every claimed derived value equals fresh trusted recomputation; Python trace has all 207 nodes and Julia reconstructs the roots without Python intermediates. |
| DAG-05 | `SUPPORTED` | E06/E08; all 160 individual derived corruptions rejected, zero survivors. |

### All 373 challenge results

The indices below are zero-based indices into `R.challenge_results`; they form the exact disjoint partition `0..372`. Every listed row has disposition `PASSED`, `mandatory = true`, `observed_consequence = VERIFIER_REJECTS`, packet/spec hashes bound to the unmodified baseline graph, and exactly the independently recomputed affected roots. This is a mechanically grouped totality proof, not sampling.

| ID | Challenge | Result indices | Count | Review disposition |
| --- | --- | --- | ---: | --- |
| CH-01 | `ALL_DERIVED_INTERMEDIATE_CORRUPTION` | `0..159` | 160 | `SUPPORTED` |
| CH-02 | `SOURCE_LOCATOR_MUST_RESOLVE` | `160..190` | 31 | `SUPPORTED` |
| CH-03 | `UNKNOWN_OPERATION_FAILS_CLOSED` | `191..350` | 160 | `SUPPORTED` |
| CH-04 | `OUTPUT_BINDING_CORRUPTION_REJECTED` | `353..368` | 16 | `SUPPORTED` |
| CH-05 | `C03_N7_SOURCE_BOUNDARY` | `370` | 1 | `SUPPORTED` |
| CH-06 | `C03_N8_SOURCE_BOUNDARY` | `371` | 1 | `SUPPORTED` |
| CH-07 | `EVALUATED_ZERO_IS_NOT_UNEVALUATED` | `372` | 1 | `SUPPORTED` |
| CH-08 | `PARENT_BYPASS_REJECTED` | `351` | 1 | `SUPPORTED` |
| CH-09 | `RV03_PHASE_SENSITIVITY` | `369` | 1 | `SUPPORTED` |
| CH-10 | `STALE_EDGE_REJECTED` | `352` | 1 | `SUPPORTED` |

Verifier-error-code totality: `RECOMPUTATION_MISMATCH = 163`, `UNTRUSTED_OR_UNKNOWN_OPERATION = 161`, `SOURCE_LOCATOR_NOT_FOUND = 31`, `EMITTED_ROOT_MISMATCH = 16`, `C03_RV_DERIVED_SIGNATURE = 1`, `PARENT_EDGE_DISAGREEMENT = 1`; total `373`. Unique challenge packets `373`; unique results `373`; unexpected survivors `0`.

Per-root applicable-result counts, independently rederived from descendants:

| Root | Count | Root | Count |
| --- | ---: | --- | ---: |
| `C03.OUTPUT.EVANESCENT_COORDINATES` | 53 | `C03.OUTPUT.EVANESCENT_STATE` | 76 |
| `C03.OUTPUT.PHYSICAL_COEFFICIENT` | 52 | `RV01.OUTPUT.EVANESCENT_STATE` | 18 |
| `RV01.OUTPUT.PHYSICAL_COEFFICIENT` | 32 | `RV02.OUTPUT.EVANESCENT_STATE` | 18 |
| `RV02.OUTPUT.PHYSICAL_COEFFICIENT` | 32 | `RV03.OUTPUT.EVANESCENT_STATE` | 18 |
| `RV03.OUTPUT.PHYSICAL_COEFFICIENT` | 33 | `RV03.OUTPUT.SOURCE_CHANNEL` | 8 |
| `RV04.OUTPUT.EVANESCENT_STATE` | 18 | `RV04.OUTPUT.PHYSICAL_COEFFICIENT` | 32 |
| `RV05.OUTPUT.EVANESCENT_STATE` | 18 | `RV05.OUTPUT.PHYSICAL_COEFFICIENT` | 32 |
| `RV06.OUTPUT.EVANESCENT_STATE` | 19 | `RV06.OUTPUT.PHYSICAL_COEFFICIENT` | 32 |

## G. Julia, Lean, replay, and closure dispositions

| ID | Disposition | Evidence/finding |
| --- | --- | --- |
| IND-01 | `SUPPORTED` | E05/E06/E09; Julia 1.12.6 independently reconstructs 16/16 exact root hashes from declared sources. |
| IND-02 | `SUPPORTED` | E09; no Python receipt, expected-output/oracle receipt, or candidate comparison answer participates in Julia computation. |
| IND-03 | `SUPPORTED` | Physics transformations are separately implemented. Common canonical vocabulary, source corpus, profile/policy and conventions are fully disclosed above; this is computational implementation independence, not independent physics provenance. |
| FRM-01 | `SUPPORTED` | E10; actual checker parsed the canonical embedded runtime certificate and independently verified its raw file SHA. This narrow parse/file-hash statement does not claim identity binding. |
| FRM-02 | `AMENDMENT_REQUIRED` | D-01; valid-hex contract/graph/source/output fields are not cryptographically related and reported identity is caller-supplied. |
| FRM-03 | `AMENDMENT_REQUIRED` | D-01; all required graph/value/source/contract/identity mutations tested above were accepted. |
| REP-01 | `SUPPORTED` | E03; two separate local replay processes returned the frozen identity and `MATCHED`. |
| REP-02 | `SUPPORTED` | E04; regenerated closure exact, `54 Python/5 Julia/4 Lean/9 fixed`, zero unresolved, zero exclusions. |
| REP-03 | `SUPPORTED` | E04/E09; closure contains source-derived trusted routes only; no historical oracle is a trusted runtime dependency. |
| REP-04 | `PENDING` | D-03; no actual Linux result/failure artifact exists, so no Linux pass is inferred. |

Dependency-closure semantic limitation: the bundle is content-addressed and hash-bound, not filesystem-immutable. Its declared state `CONTENT_ADDRESSED_HASH_BOUND_NOT_FILESYSTEM_IMMUTABLE` is accurate. Replay detects changed bytes; it does not prevent them from being changed.

## H. Authority and claim-limit dispositions

| ID | Disposition | Evidence/finding |
| --- | --- | --- |
| AUTH-01 | `SUPPORTED` | E13; all 16 bindings reproduce the exact historical authority labels/scope/ceilings/limitations from the three cited records (`6156ec...`, `682476...`, `614184...`). |
| AUTH-02 | `SUPPORTED` | Profile remains `SCIENTIFIC_REQUALIFICATION_NOT_EARNED`; neither bundle nor milestone silently advances it. |
| AUTH-03 | `SUPPORTED` | Receipt/certificate/bundle non-promotion flags are false; operations do not mutate authority. D-01 weakens certificate identity, but Lean does directly reject `scientific_promotion = true`. |
| AUTH-04 | `SUPPORTED` | All inspected summary surfaces retain false product and production flags. |
| AUTH-05 | `SUPPORTED` | All 16 entries say the statement is computational under frozen inputs/conventions/operations/policy and explicitly do not claim SU(5), CCFT, or global production-runner correctness. |

## Decision

The exact baseline values, source locators, lowering, Python/Julia reconstruction, dependency closure, bounded claims, and the complete 373-instance frozen challenge set are internally reproducible. They do not justify the clean disposition because the formal route does not independently bind the certificate identity and the trusted verifier does not enforce the frozen complete value-type metadata. These are material trust-architecture defects, not cosmetic documentation gaps. A Linux qualification result is also absent.

Therefore the one allowed overall disposition is:

`SUPPORTED_WITH_REQUIRED_AMENDMENTS`

This disposition does not endorse the 16 roots as clean `VERIFIED_EXACT` outputs under the full review-matrix definition. It supports the recorded exact Python/Julia computation within the frozen source assumptions while requiring a new versioned lineage to repair D-01 and D-02 and re-run all affected evidence. No repair may overwrite this packet.

scientific_promotion = false

product_v1_release = false

production_activation = false

## Review artifact hash binding

Hash convention: `review_artifact_sha256_zeroed_field` is SHA-256 of the complete UTF-8 bytes of this file after replacing only the 64 lowercase hexadecimal characters on the following field with 64 ASCII zero characters. This removes self-reference while binding every other byte and the field location.

review_artifact_sha256_zeroed_field: `d415ae3d690b4bcf87d6222f8618371af2d1a28b0c624843f95b8649cb816b15`
