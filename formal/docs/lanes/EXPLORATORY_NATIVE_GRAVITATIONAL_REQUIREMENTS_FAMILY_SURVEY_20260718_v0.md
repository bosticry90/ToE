# Exploratory Native Gravitational Requirements/Family Survey v0

Date: 2026-07-18  
Authority consumed: `conduct_exploratory_native_gravitational_requirements_family_survey_v0`  
Disposition: `COMPLETED_NONAUTHORITATIVE_OPPORTUNITY_MAP_PENDING_INDEPENDENT_REVIEW`  
Mode: `MANUAL_EXPLORATORY_NONAUTHORITATIVE`

## Claim boundary

This document records one provisional, human-readable survey. It is not an
authoritative requirements matrix, action selector, survivor computation, or
equivalence reduction. Its labels do not map to V2 statuses. In particular:

```text
surveyed provisional cells: 22 / 70
NOT_SURVEYED cells:          48 / 70
authoritative V2 cells:       0 / 70
authoritative family judgments: NONE
native gravitational principle: NOT IDENTIFIED
gravitational action: NOT SELECTED
```

The family envelope is a bounded comparison instrument, not an exhaustive
taxonomy of gravity. Every family-level statement below is limited to the
stated domain; a special representative is never silently generalized to its
whole family.

## Source and reasoning register

Project sources:

- `P1_MINIMAL_CONTRACT`: [minimal native continuum gravitational-sector contract](../release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json).
- `P2_CK_STATUS`: [Ck-family status synthesis](../release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json).
- `P3_STRESS_POLICY`: [native stress-energy definition policy result review](../release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json).
- `P4_MATTER_PACKET`: [QFT/GR matter-field candidate packet](../release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json).
- `P5_DISCRETE_POISSON`: [discrete weak-field Poisson theorem](../../toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean).
- `P6_0I_BLOCK`: [gravitomagnetic recovery packet review](../release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json).
- `P7_STABILITY_OBLIGATION`: [native gravitational-principle response selection](../release/NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0.json).

Primary external sources used for limited comparator statements:

- `E1_IYER_WALD_1994`: Iyer and Wald, [Some Properties of Noether Charge and a Proposal for Dynamical Black Hole Entropy](https://arxiv.org/abs/gr-qc/9403028). Used only for the general diffeomorphism/Noether structure of covariant Lagrangians.
- `E2_BERRY_GAIR_2011`: Berry and Gair, [Linearized f(R) Gravity: Gravitational Radiation and Solar System Tests](https://arxiv.org/abs/1104.0819). Used for analytic weak-field f(R) representatives and their extra scalar response.
- `E3_CHIBA_2003`: Chiba, [1/R Gravity and Scalar-Tensor Gravity](https://arxiv.org/abs/astro-ph/0307338). Used for the scalar-tensor representation of metric f(R), not for every model's phenomenology.
- `E4_FARAONI_2006`: Faraoni, [Matter instability in modified gravity](https://arxiv.org/abs/astro-ph/0610734). Used to establish model-dependent f(R) stability conditions.
- `E5_DOLGOV_KAWASAKI_2003`: Dolgov and Kawasaki, [Can modified gravity explain accelerated cosmic expansion?](https://arxiv.org/abs/astro-ph/0307285). Used as a concrete instability counterexample, not a whole-family verdict.
- `E6_STELLE_1978`: Stelle, [Classical Gravity with Higher Derivatives](https://doi.org/10.1007/BF00760427). Used for the generic quadratic spectrum, Yukawa-corrected weak field, and the negative-energy massive spin-2 issue.
- `E7_LINDBLAD_RODNIANSKI_2004`: Lindblad and Rodnianski, [Global Existence for the Einstein Vacuum Equations in Wave Coordinates](https://arxiv.org/abs/math/0411109). Used only for small-data stability near Minkowski in its stated domain.
- `E8_LOVELOCK_1971`: Lovelock, [The Einstein Tensor and Its Generalizations](https://doi.org/10.1063/1.1665613). Used to locate the leverage of an additional second-order assumption; that assumption is not promoted to a native project principle here.
- `E9_CAPOZZIELLO_STABILE_TROISI_2007`: Capozziello, Stabile, and Troisi, [Newtonian limit of f(R) gravity](https://arxiv.org/abs/0708.0723). Used for the parameter- and regime-dependent Newtonian behavior of analytic f(R) representatives.

`DIRECT_MATHEMATICAL_REASONING`, `KNOWN_COMPARATOR_BEHAVIOR`, and
`EXPERT_JUDGMENT` are also used below. These basis types are not evidentially
equivalent, and confidence labels do not upgrade their authority.

## Phase 1: eight decision-critical questions

### DQ1 — Does diffeomorphism covariance discriminate?

- **Issue:** Whether `R4_DIFF_COVARIANCE` distinguishes `F_EH`, `F_FR`, and `F_QUADRATIC`.
- **Provisional answer:** No obvious discrimination. Each frozen family can be written as an integral of a scalar density constructed from the metric and curvature. R4 is therefore an admissibility condition common to these families, not an apparent selector among them.
- **Assumptions/domain:** Local, four-dimensional, metric actions with constant scalar couplings; explicitly noncovariant additions are outside the stated representatives.
- **Basis:** `DIRECT_MATHEMATICAL_REASONING`, `E1_IYER_WALD_1994`.
- **Uncertainty:** This says nothing about source coupling, degrees of freedom, stability, or boundary observables.
- **Resolving work:** No further whole-family survey is needed for R4 alone. If R7 is pursued, derive the generalized Noether identity for the bounded shared representative.
- **Supporting cells:** `R4 x {F_EH,F_FR,F_QUADRATIC}`.

### DQ2 — Does the Ck firewall constrain action form?

- **Issue:** Whether `R5_CK_FIREWALL` chooses curvature dependence or only controls project architecture.
- **Provisional answer:** It presently controls architecture only. `P2_CK_STATUS` makes Ck families admissibility-only and supplies no Ck action embedding, multiplier, or variation. The three primary metric families can be written without Ck, so the firewall does not distinguish their curvature terms.
- **Assumptions/domain:** The frozen comparison actions contain no hidden Ck-dependent coefficient or multiplier.
- **Basis:** `P2_CK_STATUS`, `DIRECT_MATHEMATICAL_REASONING`.
- **Uncertainty:** A future native seam law could link Ck admissibility to a gravitational coefficient or mode constraint, but no accepted source currently does so.
- **Resolving work:** Produce an explicit accepted seam-to-Lagrangian map or a counterexample showing that two admissible actions receive different Ck status.
- **Supporting cells:** `R5 x {F_EH,F_FR,F_QUADRATIC}`.

### DQ3 — Does source compatibility discriminate?

- **Issue:** Whether `R7_SOURCE_COMPATIBILITY` distinguishes the primary metric families.
- **Provisional answer:** Probably not by itself. With a diffeomorphism-invariant matter action and the stated variational definition of `T_mu_nu`, generalized Noether identities provide the relevant on-shell conservation structure for all three covariant metric families. The gravitational differential order and spectrum still differ, but R7 does not by itself select them.
- **Assumptions/domain:** Minimal or otherwise explicitly covariant matter coupling; matter equations hold; no anomalous or externally prescribed nonconserved source.
- **Basis:** `P1_MINIMAL_CONTRACT`, `P3_STRESS_POLICY`, `P4_MATTER_PACKET`, `E1_IYER_WALD_1994`, `DIRECT_MATHEMATICAL_REASONING`.
- **Uncertainty:** The project has a stress-energy policy, not a native continuum matter variation tied to a selected gravitational action. Nonminimal coupling can alter the bookkeeping.
- **Resolving work:** Derive one shared diffeomorphism Ward identity for a bounded metric action plus a frozen matter representative, keeping gravitational and matter equations explicit.
- **Supporting cells:** `R7 x {F_EH,F_FR,F_QUADRATIC}`.

### DQ4 — Does Newton–Poisson recovery discriminate?

- **Issue:** Whether `R8_NEWTON_POISSON` separates nonlinear or quadratic curvature families from Einstein–Hilbert without a special limit.
- **Provisional answer:** Mere existence of a Newtonian regime probably does not select a family. The zero-cosmological-constant Einstein–Hilbert comparator has the standard limit, while analytic f(R) and generic quadratic representatives can produce Newtonian plus Yukawa terms whose range and amplitude depend on coefficients. An exact unmodified Poisson equation with no fitted limiting regime could discriminate, but that stronger reading has not been derived for whole families.
- **Assumptions/domain:** Stationary weak fields about Minkowski, specified source normalization, and no extrapolation from a special parameter value to a complete family.
- **Basis:** `P5_DISCRETE_POISSON`, `E2_BERRY_GAIR_2011`, `E6_STELLE_1978`, `E9_CAPOZZIELLO_STABILE_TROISI_2007`, `KNOWN_COMPARATOR_BEHAVIOR`.
- **Uncertainty:** The local project theorem is discrete and structural; it is not a continuum tensor derivation. Whole-family f(R) and quadratic conclusions depend on analytic form, masses, boundary conditions, and coefficient choices.
- **Resolving work:** Derive the source-normalized linearized 00 Green function for `R + alpha R^2 + beta R_{mu nu}R^{mu nu}` under one convention, with the Einstein–Hilbert and f(R) subcases shown explicitly.
- **Supporting cells:** `R8 x {F_EH,F_FR,F_QUADRATIC}`.

### DQ5 — Is the stationary momentum-current sector independent?

- **Issue:** Whether `R9_MOMENTUM_CURRENT` adds information beyond R8.
- **Provisional answer:** Yes, provisionally. The 00 sector probes scalar/static response, whereas the stationary 0i sector probes momentum-current transport and is sensitive to the spin content of the propagator. A simple analytic f(R) representative adds a scalar, while generic quadratic curvature also adds a massive spin-2 sector; their 0i responses therefore need not track their 00 limits.
- **Assumptions/domain:** Linear perturbations about Minkowski with a conserved stationary source; claims about f(R) are restricted to analytic representatives covered by the cited work.
- **Basis:** `P6_0I_BLOCK`, `E2_BERRY_GAIR_2011`, `E3_CHIBA_2003`, `E6_STELLE_1978`, `DIRECT_MATHEMATICAL_REASONING`.
- **Uncertainty:** The project has no native continuum tensor equation or common 0i calculation. Scalar/vector decomposition and gauge conventions must be shared before comparison.
- **Resolving work:** In the same bounded representative used for DQ4, derive the stationary 0i Green function and identify which poles couple to conserved `T_0i`.
- **Supporting cells:** `R8,R9 x {F_EH,F_FR,F_QUADRATIC}`.

### DQ6 — Where does stability/no-fitting discriminate?

- **Issue:** Which `R10_STABILITY_NO_FIT` calculation has the highest selection leverage.
- **Provisional answer:** Spectrum and stability are the strongest visible discriminators. Einstein gravity has rigorous small-data stability results near Minkowski in a limited domain. Metric f(R) contains stable and unstable model sectors. Generic quadratic gravity contains an additional massive spin-2 excitation with the standard negative-energy/residue problem, although special coefficient choices and interpretive frameworks prevent a blanket whole-family theorem here.
- **Assumptions/domain:** Local metric theories linearized around Minkowski; ordinary sign conventions and propagator interpretation; no claim about every background or UV completion.
- **Basis:** `P7_STABILITY_OBLIGATION`, `E4_FARAONI_2006`, `E5_DOLGOV_KAWASAKI_2003`, `E6_STELLE_1978`, `E7_LINDBLAD_RODNIANSKI_2004`.
- **Uncertainty:** R10 combines several notions—linear spectrum, nonlinear stability, phenomenological recovery, and coefficient fitting—that must be separated in a rigorous target.
- **Resolving work:** Compute poles, residues, source response, and tachyon/ghost conditions for the bounded `(alpha,beta)` representative before any observational fitting.
- **Supporting cells:** `R10 x {F_EH,F_FR,F_QUADRATIC}`.

### DQ7 — Is there an accepted ToE-specific Lagrangian constraint?

- **Issue:** Whether an existing seam or admissibility principle fixes gravitational dynamics.
- **Provisional answer:** None was found in the frozen sources. R5 prevents an impermissible Ck embedding but supplies no curvature functional. R7 requires a source definition and compatibility structure but is likely shared by covariant metric families. The existing discrete Poisson surface and the blocked 0i lane do not supply a continuum native action.
- **Assumptions/domain:** Only accepted, source-bound project commitments count; methodological rules and desired recovery behavior are not promoted into physical postulates.
- **Basis:** `P1_MINIMAL_CONTRACT`, `P2_CK_STATUS`, `P3_STRESS_POLICY`, `P5_DISCRETE_POISSON`, `P6_0I_BLOCK`, `EXPERT_JUDGMENT`.
- **Uncertainty:** This is an absence finding within the reviewed authority surface, not proof that no native principle can be formulated.
- **Resolving work:** After the shared linearized comparison, ask whether an accepted cross-pillar law fixes derivative order, pole content, or source coupling. If not, formulate only a targeted exploratory postulate candidate under fresh authority.
- **Supporting cells:** `R5,R7 x {F_EH,F_FR,F_QUADRATIC}`.

### DQ8 — What survives equivalence operations?

- **Issue:** Which properties may be transported across `F_EQUIVALENCE_PROBE`.
- **Provisional answer:** Only the proved property. Algebraic identities preserve the same integrand. A locally irrelevant boundary term, or a four-dimensional topological term with vanishing local bulk variation, can preserve compact-support local bulk equations. That does not automatically preserve boundary observables, global charges, admissible boundary data, matter coupling, mode content under noninvertible redefinitions, stability, or empirical predictions.
- **Assumptions/domain:** Smooth fields and the frozen compact-support local-bulk variation domain; exact identities or explicitly proved boundary/topological relations only.
- **Basis:** `P1_MINIMAL_CONTRACT`, `E1_IYER_WALD_1994`, `DIRECT_MATHEMATICAL_REASONING`.
- **Uncertainty:** No real family merge is asserted, and no property-transport proof has been supplied for the real survey families.
- **Resolving work:** For any future claimed equivalence, state the transformation, domain, inverse where relevant, boundary conditions, and an exact property-by-property preservation proof.
- **Supporting cells:** `R6 x F_EQUIVALENCE_PROBE` plus the question-level property map above.

## Phase 2: supporting cells only

All entries have workflow state `SURVEYED_PROVISIONAL` and review state
`PENDING_INDEPENDENT_RESULT_REVIEW`. The basis column names the register entries
or reasoning types; the full structured assumptions, basis roles, uncertainty,
and resolving work are retained in the companion JSON artifact.

| Requirement | Family | Provisional label | Limited rationale | Main uncertainty / resolving work |
|---|---|---|---|---|
| R4 | F_EH | CLEARLY COMPATIBLE | The Einstein–Hilbert density is a diffeomorphism scalar density. | Symmetry alone says nothing about spectrum or recovery; no further R4-only work. |
| R4 | F_FR | CLEARLY COMPATIBLE | A metric f(R) density is covariant when f is a scalar function of R. | Limited to the frozen metric construction; do not infer viability. |
| R4 | F_QUADRATIC | CLEARLY COMPATIBLE | Curvature-invariant quadratic densities are covariant scalars. | Limited to covariant invariant combinations; do not infer stability. |
| R5 | F_EH | LIKELY COMPATIBLE | The comparator can be written without a Ck multiplier or variation. | Check any future project embedding for hidden Ck-dependent coefficients. |
| R5 | F_FR | LIKELY COMPATIBLE | Curvature nonlinearity does not itself require Ck action embedding. | Same future-embedding caveat. |
| R5 | F_QUADRATIC | LIKELY COMPATIBLE | Quadratic invariants do not themselves require Ck action embedding. | Same future-embedding caveat. |
| R7 | F_EH | LIKELY COMPATIBLE | Covariant matter variation and the Noether identity support on-shell source conservation. | Requires an explicit project matter action and shared Ward identity. |
| R7 | F_FR | LIKELY COMPATIBLE | The same source definition can be used in covariant metric f(R). | Nonminimal coupling and whole-family matter choices remain open. |
| R7 | F_QUADRATIC | LIKELY COMPATIBLE | Covariance supplies a generalized identity despite higher derivatives. | Exact matter coupling and boundary terms remain open. |
| R8 | F_EH | CLEARLY COMPATIBLE | The zero-Lambda standard comparator has the Newton–Poisson limit. | This is supplied comparator behavior, not native ToE recovery. |
| R8 | F_FR | UNRESOLVED | Analytic representatives yield Newtonian plus scalar/Yukawa response; some regimes approximate GR. | Derive a shared 00 response; no representative stands for all f(R). |
| R8 | F_QUADRATIC | UNRESOLVED | Generic representatives yield Newtonian plus massive-mode corrections. | Exact no-fit recovery depends on coefficients and source/boundary conventions. |
| R9 | F_EH | CLEARLY COMPATIBLE | Standard linearized GR has a stationary momentum-current response. | This is a supplied comparator and has not been derived natively. |
| R9 | F_FR | UNRESOLVED | Simple analytic representatives add a scalar, but a whole-family 0i result was not established. | Derive the conserved-source 0i Green function under shared gauge conventions. |
| R9 | F_QUADRATIC | UNRESOLVED | The massive spin-2 sector can modify momentum-current response. | Derive which propagator poles couple to T_0i. |
| R10 | F_EH | LIKELY COMPATIBLE | Small-data stability near Minkowski is established in a limited Einstein domain. | Not a claim about every background, Lambda choice, or observational obligation. |
| R10 | F_FR | UNRESOLVED | Stable and unstable subclasses both occur. | Separate tachyon, matter-instability, nonlinear, and no-fit conditions. |
| R10 | F_QUADRATIC | LIKELY INCOMPATIBLE | Generic standard-sign quadratic gravity carries a negative-energy/residue massive spin-2 mode. | Special coefficients and nonstandard interpretations require a scoped proof. |
| R2 | F_EXTRA_FIELD | OUTSIDE FROZEN SCOPE | The family has additional fundamental gravitational fields. | Outside scope is not physical rejection; revisit only under new authority. |
| R2 | F_CONNECTION_TORSION | OUTSIDE FROZEN SCOPE | The family uses an independent connection or torsion. | Outside scope is not physical rejection. |
| R3 | F_NONLOCAL | OUTSIDE FROZEN SCOPE | The family is explicitly nonlocal. | Outside scope is not physical rejection. |
| R6 | F_EQUIVALENCE_PROBE | CLEARLY COMPATIBLE | Exact boundary/topological variants can preserve compact-support local bulk variation. | No transport beyond the exact proved local-bulk property. |

Label tally (descriptive only):

```text
CLEARLY COMPATIBLE:     6
LIKELY COMPATIBLE:      7
LIKELY INCOMPATIBLE:    1
CLEARLY INCOMPATIBLE:   0
UNRESOLVED:             5
OUTSIDE FROZEN SCOPE:   3
NOT_SURVEYED:          48
```

Explicit `NOT_SURVEYED` inventory:

- All seven R1 cells.
- R2 with `F_EH`, `F_FR`, `F_QUADRATIC`, `F_NONLOCAL`, and `F_EQUIVALENCE_PROBE`.
- R3 with every family except `F_NONLOCAL`.
- R4 with `F_EXTRA_FIELD`, `F_NONLOCAL`, `F_CONNECTION_TORSION`, and `F_EQUIVALENCE_PROBE`.
- R5 with `F_EXTRA_FIELD`, `F_NONLOCAL`, `F_CONNECTION_TORSION`, and `F_EQUIVALENCE_PROBE`.
- R6 with every family except `F_EQUIVALENCE_PROBE`.
- R7, R8, R9, and R10 with each of `F_EXTRA_FIELD`, `F_NONLOCAL`, `F_CONNECTION_TORSION`, and `F_EQUIVALENCE_PROBE`.

These 48 blanks mean no exploratory assessment was made. They do not mean
`UNRESOLVED` and do not contribute to any result.

## Phase 3: scientific opportunity map

### Provisional requirement map

- **Broadly nonselective in the primary envelope:** R4; R5 as currently written; R7 under ordinary covariant matter coupling; and R8 if read only as existence of some Newtonian regime.
- **Scope filters, not dynamics selectors:** R1, R2, R3, and R6.
- **Highest apparent discriminator:** R10, once split into precise spectrum and stability obligations.
- **Independent recovery leverage:** R9, because the 0i momentum-current sector probes propagating structure not fixed by a 00 limit alone.
- **Supplied-assumption dependence:** A separate demand for second-order metric equations or no extra gravitational modes would strongly narrow the primary envelope (compare `E8_LOVELOCK_1971`, `E2_BERRY_GAIR_2011`, and `E6_STELLE_1978`), but this survey does not reclassify either demand as a native ToE principle.

### Dependency and redundancy hypotheses

- R4 and R7 are related through diffeomorphism Noether identities, but R7 is not redundant because it also fixes how a matter source is defined and coupled.
- R8 and R9 remain independent until a common tensor equation and source convention derive both sectors.
- R5 currently filters impermissible project architecture rather than gravitational dynamics; it becomes selective only if a future accepted seam law maps admissibility to an action property.
- R10 is too composite for one theorem. Spectrum, tachyon/ghost stability, nonlinear background stability, empirical recovery, and coefficient fitting should be separated in the next rigorous target.

### Family-difference map without asserted merges

- `F_EH`: supplied standard weak-field comparator; limited Minkowski stability support; no native selection implied.
- `F_FR`: typically adds a scalar response in analytic nonlinear representatives; weak-field and stability behavior are model- and parameter-dependent.
- `F_QUADRATIC`: generically adds scalar and massive spin-2 structure; its massive spin-2 sector is the sharpest visible stability concern.
- `F_EXTRA_FIELD`, `F_CONNECTION_TORSION`, `F_NONLOCAL`: outside the frozen envelope, not scientifically eliminated.
- `F_EQUIVALENCE_PROBE`: a property-scoped control only; no real-family equivalence or merge is asserted.

### Highest-value next bounded derivation

Use the bounded comparison representative

```text
S = integral sqrt(-g) [R + alpha R^2 + beta R_{mu nu} R^{mu nu}] + S_m
```

solely as a comparison instrument. Under one signature, gauge, source
normalization, and boundary convention:

1. derive its linearized conserved-source propagator or equivalent field equations;
2. obtain stationary 00 and 0i Green functions;
3. list poles, residues, and propagating modes;
4. display the `alpha=beta=0`, `beta=0`, and generic `beta != 0` cases;
5. state exactly which recovery requires a limit or coefficient choice.

This single calculation addresses DQ4–DQ6 and does not propose the displayed
representative as the project's action.

### Best bounded no-go/counterexample test

Within the same linearized domain, prove or refute the following scoped
conjecture in the project's conventions:

> With `beta != 0`, ordinary local metric kinetic assumptions, and a conserved
> source, the generic quadratic representative cannot remove the
> negative-residue massive spin-2 pole while retaining the intended local
> source response, except by a degeneracy, limit, or assumption change that is
> stated explicitly.

This is a proposed test, not a no-go theorem.

### Where a future postulate would have leverage

If the bounded derivation confirms that R4, R5, R7, and weak R8 are
nonselective, a useful project-specific postulate would need to constrain an
actual physical freedom: derivative order, propagating pole content,
gravitational source coupling, or an accepted cross-sector relation. Adding an
arbitrary curvature term would not answer the identified selection problem.

### Deferred without loss of present leverage

The 48 blank cells, detailed physics of out-of-envelope families, global and
boundary equivalence observables, observational fitting, matter-sector choice,
metric variation of a selected action, and frame-dragging recovery can all wait
until the shared linearized comparison has been independently reviewed.

## Stop and nonclaims

All eight questions have been answered provisionally, the 22 required support
cells have been exposed, and one next derivation plus one counterexample test
have been identified. The authorized survey therefore stops here.

This survey does not establish a survivor set, a family equivalence, a
standard-GR collapse, an underdetermination verdict, a minimal-envelope no-go,
a distinctive gravitational postulate requirement, a native principle, or a
gravitational action. It does not populate V2 and does not authorize metric
variation or frame-dragging.

```text
selected next authority:
review_exploratory_native_gravitational_requirements_family_survey_v0_result
```
