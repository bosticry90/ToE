# External comparators, Astra workflow, and v6 decision draft

Status: `DOCUMENTATION_INTAKE_COMPLETE__NO_AUTHORITY_ADOPTION`.

This packet implements the requested six-topic review. It adds future benchmark
specifications, not executable or certified physics profiles. It does not change
the frozen C03/RV computation, the calculator kernel, the closed 25-entry baseline
registry, existing dirty-tree research, or current scientific authority.

| Requested action | Deliverable | Disposition |
| --- | --- | --- |
| Preserve the lapse family | [Q-exponential comparator](qexp_lapse.md) | Mathematical comparator; physical interpretation underdetermined |
| Add dark-photon comparator and seam | [Nonlinear plasma specification](dark_photon.md) | Future numerical benchmark; no detection claim |
| Add quantum free-fall benchmark and seam | [Free-fall specification](quantum_free_fall.md) | Extension seam to the existing recovery contract; not a duplicate recovery |
| Add chiral-phonon benchmark and emergence chain | [Phonon specification](chiral_phonons.md) | Future symmetry/measurement benchmark |
| Define Astra use and first native task | [Operating model](astra_operating_model.md) and [gated CCFT task](ccft_reentry_task.md) | Drafted, not launched; no hosted AI in trusted execution |
| Draft bounded requalification and exact scope | [Decision draft](v6_decision_draft.md) and [scope projection](v6_scope.json) | Positive recommendation; `DRAFT_NOT_ADOPTED` |

## Corrections and limits from the source review

1. A lapse is not a full metric. Even the deformation parameter depends on the
   chosen potential and coordinates. No novelty, horizon, or entropy mechanism
   is established by the q-exponential identity.
2. The dark-photon abstract supports the reported weakening, but the inspected
   author manuscript describes approximately **10^-14 to 10^-4 eV**, not the
   pasted 10^-15 to 10^-6 eV. Do not freeze either as a digitized exclusion curve
   without reconciling the version of record and figure definitions.
3. In the ideal free-fall phase, **T is half the 2T ballistic interval**. The
   reported 2.5% is a residual scale relative to the apparatus simulation, not
   a universal equivalence-principle bound or a stand-alone exponent error.
4. In the phonon example, polar-domain reversal is not restoration of inversion
   symmetry. Angular momentum, helicity, and RIXS contrast are distinct objects.
   The inspected table varies in-plane momentum with fixed positive q_z; do not
   describe those measurements as literal reversal of the entire momentum vector.
5. Official OpenAI documentation establishes Astra's 1,050,000-token API context
   and tool-workflow features. The pasted 98% FrontierMath and Critical-cyber
   assertions are not independently established by the documentation retrieved
   here and are not used as project evidence or acceptance criteria.
6. The frozen v6 sequence's existing proposed status is
   `C03_RV_EXACT_COMPUTATION_REQUALIFIED`. The draft uses that name with an
   explicitly bounded scope; it does not invent or adopt a global qualification.

Sources and exact limitations are adjacent to the relevant claims in each file.
Publisher full text for the Science Advances and Nature Materials papers was
not retrievable through the research tool. Author preprints were inspected;
their equation/figure labels are pinned as such, not silently attributed to the
final journal versions. No raw experimental dataset was downloaded or fitted.

## Common future-benchmark boundary

All four comparator entries are `SPEC_ONLY_NOT_IMPLEMENTED`, with verification
class `NONE`, no native-theory authority effect, and no theorem discharge. The
manifest is a documentation index, **not** a `PhysicsProfileV1` or an accepted
`VerificationPolicyV1`. Web citations are literature provenance, not hash-bound
trusted source-value locators.

Before any implementation, select one bounded question; acquire licensed local
sources/data with explicit versions and hash domains; define resolvable value
locators, units, branch conventions, applicability tests and observable roots;
then obtain separate scope approval. No additions to the C03/RV profile or its
19-operation vocabulary are authorized here. Unsupported transcendental,
simulation, metric or measurement operations cannot inherit `VERIFIED_EXACT`.

The common future recovery obligation is:

```text
native assumptions -> derived dynamics -> effective/collective model
  -> domain-checked environment map -> observable -> conditional data comparison
```

Every arrow must expose inherited assumptions, its approximation domain, error
model, and failure conditions. A mathematically exact result under an invalid
physical approximation is not a valid prediction for that regime.

## Preservation and validation

The original v1 and amended Windows v6 bundles, failed attempts, local 104-check
snapshot, Linux result and non-author review remain unchanged. A byte-for-byte
copy of the previously downloaded Linux evidence archive is retained in
`evidence/` because the GitHub copy expires on 2026-12-06. This is archival custody,
not a new Linux execution or a new review.

`validate_packet.py` checks this documentation packet, the two local frozen bundle
identities, the archived Linux identity, all declared archive-file hashes, and
the generated 16-root scope against the Windows evidence. It neither reruns
Python/Julia/Lean physics nor issues trusted receipts or an authority decision.

From the repository root:

```powershell
python formal/docs/release/TOE_EXTERNAL_COMPARATORS_AND_V6_DECISION_20260907_v1/validate_packet.py
```

The optional `test_packet.py` uses SymPy for scratch algebra and tests four
documentation/custody failure cases. Its results are not VPC certificates.

Preserved ceilings: Route C 2/4; strict historical/native exact equivalence 1/4;
production 76/1188; rows 77--96 closed; scientific promotion, product v1 release,
production activation, CCFT promotion and ToE promotion all false.
