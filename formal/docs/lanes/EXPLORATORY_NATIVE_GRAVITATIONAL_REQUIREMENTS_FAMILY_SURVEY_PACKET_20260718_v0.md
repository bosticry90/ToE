# Exploratory Native Gravitational Requirements/Family Survey Packet v0

Status: `PREPARED_PENDING_INDEPENDENT_REVIEW`

Consumed target:
`prepare_exploratory_native_gravitational_requirements_family_survey_v0`

Next target:
`review_exploratory_native_gravitational_requirements_family_survey_packet_v0_result`

Mode:
`NONAUTHORITATIVE_MANUALLY_ADJUDICATED_EXPLORATION`

## Preparation answer

This packet prepares a transparent manual survey of the frozen ten requirements
and seven comparison families. It does not perform the survey.

The preparation contains a 70-entry blank form, but every entry remains:

```text
workflow state: NOT_SURVEYED
provisional classification: NONE
rationale: NONE
scientific family judgment: NONE
```

The form is deliberately not compatible with the closed V2 evidence-provider
or matrix interfaces. It has no survivor reducer, equivalence reducer, terminal
classifier, or path by which a provisional label can become an authoritative
project result.

```text
exploration:
human-readable / provisional / hypothesis-generating

validation:
closed automated lane / no authoritative verdict
```

## Frozen input envelope

The survey retains exactly these requirements:

1. `R1_DIMENSION` — four-dimensional evaluation envelope.
2. `R2_METRIC_ONLY` — gravitational field restricted to the metric in the
   frozen minimal scope.
3. `R3_LOCALITY` — local scalar-density action in the frozen minimal scope.
4. `R4_DIFF_COVARIANCE` — coordinate-independent scalar action.
5. `R5_CK_FIREWALL` — no `C_k` embedding multiplier penalty or variation.
6. `R6_LOCAL_VARIATION` — compactly supported local bulk metric variation.
7. `R7_SOURCE_COMPATIBILITY` — compatibility with the retained metric source
   definition and conservation question.
8. `R8_NEWTON_POISSON` — stationary weak-field `00` recovery obligation.
9. `R9_MOMENTUM_CURRENT` — stationary momentum-current response obligation.
10. `R10_STABILITY_NO_FIT` — stability and no-fit recovery comparison.

It retains exactly these comparison families:

1. `F_EH` — local metric action linear in curvature, with optional
   cosmological term.
2. `F_FR` — local metric `f(R)` family excluding the purely linear
   representative.
3. `F_QUADRATIC` — local metric actions with independent quadratic Ricci or
   Riemann invariants.
4. `F_EXTRA_FIELD` — metric plus additional fundamental scalar, vector, or
   tensor; outside the frozen metric-only scope.
5. `F_NONLOCAL` — explicitly nonlocal metric action; outside the frozen local
   scope.
6. `F_CONNECTION_TORSION` — independent-connection, Palatini, or torsion
   family; outside the frozen metric-only scope.
7. `F_EQUIVALENCE_PROBE` — boundary, algebraic, or four-dimensional
   topological variants; an equivalence probe rather than a separate candidate.

The envelope is unchanged from V2 and is comparison-only. Inclusion does not
endorse a family, while a frozen-scope exclusion is not a physical no-go.

## Provisional classification vocabulary

Only a human adjudicator may assign one of the following labels after review:

```text
CLEARLY COMPATIBLE
LIKELY COMPATIBLE
LIKELY INCOMPATIBLE
CLEARLY INCOMPATIBLE
UNRESOLVED
OUTSIDE FROZEN SCOPE
```

These labels are not aliases for V2 cell statuses. In particular:

- `CLEARLY COMPATIBLE` is not authoritative `SATISFIES`;
- `CLEARLY INCOMPATIBLE` is not authoritative `ELIMINATED`;
- `UNRESOLVED` is not V2 `NOT_DECIDABLE_FROM_REQUIREMENT`;
- `OUTSIDE FROZEN SCOPE` is a survey boundary, not a physical impossibility;
- no label contributes to a survivor or terminal outcome.

`NOT_SURVEYED` is a preparation/workflow sentinel and is not a scientific
classification.

## Required cell record

Each surveyed requirement/family entry must record:

```text
cell ID
requirement ID
family ID
workflow state
provisional classification
concise physical or mathematical rationale
explicit assumptions and domain
source or derivation pointers
main uncertainty
calculation or theorem that would resolve the uncertainty
priority role
manual adjudicator identity
manual review status
```

The rationale must be specific to the exact family and requirement. Repeating
a label is not a rationale. A statement about one parameter value, recovery
limit, or special representative may not be generalized to the complete family
without saying so explicitly.

## Source and derivation policy

The future manual survey may use:

- frozen project-authority sources to state the requirement;
- primary mathematical or theoretical sources for family properties;
- an explicit direct derivation with its assumptions and domain;
- a review source only as a provisional orientation pointer;
- supplied standard physics only as a clearly marked comparator.

Every surveyed cell must either contain at least one source or derivation
pointer or explicitly state `NO_SOURCE_POINTER_IDENTIFIED`. A stable citation
does not make the interpretation correct; the human rationale must explain why
the source bears on the exact cell.

For a `CLEARLY` label, the preferred support is an explicit derivation, theorem,
or primary source whose domain covers the claim. A `LIKELY` label must state the
gap that prevents the stronger classification. `UNRESOLVED` must name the
missing calculation, theorem, source, or definitional clarification.

No evidence producer may certify its own interpretation as authoritative. The
survey is manual and provisional precisely because scientific relevance cannot
be reduced to a custody check.

## Decision-critical question register

The survey should triage questions before trying to complete all seventy cells.
This packet registers eight questions without answering them:

1. Does `R4_DIFF_COVARIANCE` discriminate among `F_EH`, `F_FR`, and
   `F_QUADRATIC`, or does it impose only a symmetry common to them?
2. Does `R5_CK_FIREWALL` constrain gravitational action form, or only the
   project architecture surrounding any action?
3. Does `R7_SOURCE_COMPATIBILITY` distinguish primary metric families once
   matter coupling, conservation, and field-equation order are stated exactly?
4. Can `R8_NEWTON_POISSON` distinguish nonlinear or quadratic curvature
   families from `F_EH` without tuning a special parameter limit?
5. Does `R9_MOMENTUM_CURRENT` add a discriminator independent of `R8`, and
   which explicit linearized derivations would establish that?
6. What stability and no-fit calculation under `R10_STABILITY_NO_FIT` would
   materially distinguish `F_FR` and `F_QUADRATIC` from `F_EH`?
7. Does any accepted ToE-specific seam or admissibility principle constrain the
   gravitational Lagrangian rather than merely constrain its evaluation?
8. For `F_EQUIVALENCE_PROBE`, which exact properties survive each boundary,
   algebraic, or topological equivalence and which do not?

The supplied no-extra-mode or second-order assumptions may be discussed only as
comparator questions. They cannot be relabeled as native selection power.

## Survey execution order after acceptance

If independent review accepts this preparation, one bounded manual survey may:

1. restate each requirement and family from the frozen catalogs;
2. work the eight decision-critical questions first;
3. classify only cells for which a readable rationale can be written;
4. leave other cells `NOT_SURVEYED` rather than manufacture completeness;
5. identify dependency and redundancy hypotheses without proving them;
6. produce a priority map of candidate derivations and literature disputes;
7. stop for independent review of the exploratory result.

The survey is not required to classify all seventy cells. Its success criterion
is identifying the smallest high-information set of calculations, theorems, or
source reviews that would materially change the exploratory landscape.

## Required survey outputs

The later survey result must provide:

- a human-readable table of every entry actually surveyed;
- an explicit list of entries left `NOT_SURVEYED`;
- requirement-dependency and redundancy hypotheses;
- a family-difference map that does not merge families by assertion;
- a ranked list of decision-critical calculations or theorems;
- literature-dispute and domain-restriction notes;
- a clear statement of whether any ToE-native discriminator was even found as
  an exploratory hypothesis;
- all nonclaims and the stopping boundary.

It must not compute a survivor set or select one of the six V2 outcomes.

## Acceptance boundary

Acceptance of this packet would authorize exactly one bounded, manual,
nonauthoritative survey followed by independent result review.

Acceptance would not authorize:

- reopening or repairing V2;
- creating V3;
- populating the V2 scientific matrix;
- translating survey labels into V2 statuses;
- automated scientific relevance adjudication;
- an authoritative survivor or equivalence set;
- selecting Einstein–Hilbert gravity or any other family;
- proposing or adopting a gravitational action;
- authorizing a new postulate;
- metric variation, stress-energy derivation, or frame-dragging recovery;
- expanding the seven-family envelope during the survey.

## Preparation controls

The deterministic preparation checks:

- exactly ten frozen requirement IDs;
- exactly seven frozen family IDs;
- exactly seventy blank survey forms;
- zero provisional classifications;
- zero rationales, assumptions, source pointers, or resolving-work claims;
- exactly six permitted provisional labels;
- exactly eight unanswered decision-critical questions;
- no import or call of `evaluate_analysis_v2`;
- no survivor, equivalence-reduction, or terminal-classification fields;
- the automated tooling lane remains closed and V3 remains unauthorized.

These controls validate only the preparation boundary. They do not validate a
scientific judgment.

## Current posture

```text
minimal gravitational-sector contract:
ACCEPTED

native gravitational principle:
NOT IDENTIFIED

requirements/action-selection V2:
BLOCKED — PROJECT EVIDENCE SEMANTICS UNSOUND

automated action-selection tooling:
CLOSED

exploratory survey packet V0:
PREPARED_PENDING_INDEPENDENT_REVIEW

survey forms:
70 BLANK

provisional survey classifications:
0

real scientific matrix:
0 / 70

real family judgments:
NONE

automatic V3:
NOT AUTHORIZED

gravitational action:
NOT SELECTED

metric variation:
NOT EXECUTED

frame-dragging:
BLOCKED UPSTREAM

current authority:
review_exploratory_native_gravitational_requirements_family_survey_packet_v0_result
```
