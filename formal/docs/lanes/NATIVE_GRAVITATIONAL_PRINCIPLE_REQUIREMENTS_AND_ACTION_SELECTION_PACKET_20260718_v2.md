# Native Gravitational Principle Requirements and Action-Selection Packet v2

Status: `PREPARED_PENDING_INDEPENDENT_REVIEW`

Consumed target:
`prepare_native_gravitational_principle_requirements_and_action_selection_packet_v2`

Next target:
`review_native_gravitational_principle_requirements_and_action_selection_packet_v2_result`

## Objective and final automatic-repair boundary

V2 repairs exactly the five production-semantic defects found by the
independent V1 review:

1. derive immutable requirement authority internally;
2. bind every decision-bearing cell to validated evidence;
3. derive equivalence classes only from typed validated proofs;
4. preserve uncertainty unless an exact property-transport proof applies;
5. make all six frozen scientific outcomes reachable and exclusive.

This is the final automatically authorized tooling repair attempt. It does not
execute the scientific matrix. A foundational V2 review failure does not
automatically authorize V3; the allowed responses are to close this automated
lane, conduct a smaller manually adjudicated requirements analysis, or return
to the full scientific priority map.

```text
real matrix cells supplied:
0 / 70

real family judgments:
NONE

native principle:
NOT IDENTIFIED

postulate or action:
NOT AUTHORIZED OR SELECTED
```

## One production evaluator

The shared entry point is:

```text
evaluate_analysis(value, catalog_provider=...)
```

with identity:

```text
evaluate_analysis_v2
```

Synthetic controls use the frozen internal control provider. A future real run
must use the exact project profile and a separately custody-validated
`AnalysisCatalogProvider`. The provider is a dependency of the same evaluator,
not a caller-authored field inside the analysis input. Its manifest path and
SHA-256 are checked before any proof, cell, or outcome evaluation. The manifest
must parse as the closed V2 provider schema and bind the provider identity,
profile, exact catalog SHA-256, and all three record counts. Each project
evidence source must also be repository-relative, byte-hash exact, and assigned
to a frozen allowed validator ID. The referenced validator attestation is a
closed JSON object binding the exact record ID, record kind, normalized claim
hash, underlying evidence-source path, and underlying source SHA-256. Thus a
provider status label or a matching manifest hash is not sufficient by itself.

Packet preparation supplies no real project provider and no real evidence
record. Consequently the project profile cannot execute during preparation.

## Repair 1: authority-derived `BoundRequirement`

The public analysis input contains requirement IDs, not writable requirement
objects. Each ID resolves through a read-only internal catalog to a frozen
`BoundRequirement` containing:

- exact source identities;
- statement class;
- authority subtype;
- mathematical scope;
- native elimination and distinctiveness eligibility;
- requirement types;
- dependency information;
- the exact property tested.

The ten project requirements and three supplied assumptions retain their V1
bindings. The supplied assumptions remain:

```text
S1_SECOND_ORDER_FIELD_EQUATIONS
S2_LEVI_CIVITA_UNIQUENESS
S3_NO_EXTRA_GRAVITATIONAL_MODES
```

and always resolve to:

```text
SUPPLIED_STANDARD_PHYSICS_ASSUMPTION
native_elimination_allowed = false
native_distinctiveness_allowed = false
```

Caller-authored requirement objects, authority sources, statement classes, and
eligibility flags are rejected as public decision objects. A separately labeled
`caller_requirement_claims` field may be retained for audit, but it is ignored
when authority is resolved.

The false-class adversarial probe relabels
`S3_NO_EXTRA_GRAVITATIONAL_MODES` as native. The evaluator retains the canonical
supplied class, excludes its elimination from native reduction, and returns the
same native underdetermination result.

## Repair 2: evidence-bound cells

Every matrix cell has the effective schema:

```text
requirement_id
family_id
status
evidence_id
claim_scope
```

Every status except `NOT_EVALUATED` requires an evidence ID. The provider's
frozen evidence record must match all of:

```text
analysis profile
requirement ID
family ID
supported status
claim scope
evidence class
source role
support reference
validation status
```

The evaluator fails closed on a missing, unknown, rejected, profile-mismatched,
or differently bound record. A cell's expected outcome is not evidence and is
not a field of `EvidenceRecord`.

The status rules are:

| Cell status | Required evidence class |
| --- | --- |
| `AFFIRMATIVELY_SATISFIES_REQUIREMENT` | exact compatibility evidence |
| `ELIMINATED` | exact incompatibility evidence and native eligibility |
| `NOT_DECIDABLE_FROM_REQUIREMENT` | explicit limitation or nonselection evidence |
| `OUTSIDE_FROZEN_ENVELOPE` | exact scope-classification evidence |
| `EQUIVALENT_UNDER_LOCAL_BULK_RULE` | typed equivalence evidence plus an included validated proof |
| `REQUIRES_SUPPLIED_ASSUMPTION` | explicit conditional-dependence evidence |
| `NOT_EVALUATED` | no evidence and no scientific judgment |

The atomic `SATISFIES`-without-evidence probe changes only one `evidence_id` to
null and receives `EVIDENCE_ID_REQUIRED` before matrix reduction.

## Repair 3: proof-derived equivalence

The analysis input may reference equivalence proof IDs. It may not supply an
equivalence map, group labels, or raw proof objects. The selected
`AnalysisCatalogProvider` resolves IDs to frozen `EquivalenceProof` objects.

Accepted proof types are limited to:

```text
ALGEBRAIC_IDENTITY
LOCAL_BULK_BOUNDARY_TERM
TOPOLOGICAL_LOCAL_BULK_NULL_VARIATION
INVERTIBLE_LOCAL_FIELD_REDEFINITION
NONZERO_OVERALL_NORMALIZATION
```

Each proof binds:

- two exact families;
- one typed equivalence relation;
- a domain;
- preserved property keys;
- nonpreserved property keys;
- forbidden physical changes;
- an evidence source;
- local-bulk sufficiency;
- validation status;
- a canonical representative.

The reducer rejects proof claims involving changed propagating degrees of
freedom, differential order, scalar content, source coupling, stability, local
bulk equations, physical predictions, locality, or connection content.

The pair `F_FR` / `F_EH` is also a closed forbidden family-equivalence pair.
This pair-level rejection is independent of the submitted proof-type label, so
calling the relationship an `ALGEBRAIC_IDENTITY` cannot bypass the rule.

The internal negative proof:

```text
CP_INVALID_FR_EH_PARAMETER_LIMIT
```

records the attempted `F_FR -> F_EH` merge as a parameter-limit or subfamily
inclusion. Its validation status is `REJECTED`, it changes mode and derivative
content, and production returns `EQUIVALENCE_PROOF_REJECTED` before reduction.

An `EQUIVALENT_UNDER_LOCAL_BULK_RULE` cell whose proof ID is omitted likewise
fails with `EQUIVALENCE_CELL_PROOF_MISSING`.

## Repair 4: property-scoped uncertainty preservation

Member-level cell states remain in the result after class construction. For
each requirement, the reducer records:

```text
class representative
class members
exact property key
member status map
class status
whether exact-property transport was proved
```

All-member agreement remains decisive. A mixed satisfied/undecidable class
defaults to:

```text
EQUIVALENCE_CLASS_STATUS_UNRESOLVED
```

It becomes satisfied only if accepted proof edges connect every class member
and every required edge explicitly preserves the exact property tested by that
requirement.

The accepted boundary proof preserves `LOCAL_BULK_EQUATIONS` but explicitly
does not preserve `GLOBAL_STABILITY`, boundary observables, or global charges.
Therefore:

```text
F_EH = SATISFIES GLOBAL_STABILITY
F_EH_BOUNDARY = NOT_DECIDABLE FOR GLOBAL_STABILITY
local-bulk boundary proof present
```

produces:

```text
EQUIVALENCE_CLASS_STATUS_UNRESOLVED
```

The same proof may transport a local-bulk-equation property because that exact
property is present in its preserved-property set.

## Repair 5: reachable exclusive six-way classifier

Raw caller booleans no longer select terminal results. The evaluator accepts at
most one typed terminal-evidence ID from the custody-validated provider. It
then computes all six disjoint predicates and requires exactly one match.

Full-path synthetic states reach:

1. `REQUIREMENT_SET_INCONSISTENT` from an empty possible set plus a bound
   inconsistent-subset proof;
2. `NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS` from an internally consistent
   state with an affirmative viable gravity class plus a bound proof that no
   distinctive native gravity exists in the frozen envelope;
3. `NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY` from a unique complete class,
   an eligible native elimination trace, and bound distinctiveness evidence;
4. `CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR` from one complete `F_EH`
   class with no native-distinctiveness or no-go evidence;
5. `ACTION_FAMILY_UNDERDETERMINED` from multiple possible classes without
   exhaustion evidence;
6. `DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED` from multiple possible
   classes plus accepted-inventory exhaustion and a bound no-refinement
   countermodel.

The no-go fixture records:

```text
requirements internally consistent: YES
ordinary viable gravity: YES
distinctive native gravity in frozen envelope: NO
result: NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS
```

It is therefore reachable and is not an inconsistency alias.

## Production controls

### Retained V1 semantics

```text
retained controls:
8 / 8 PASSED
```

The controls retain supplied-assumption isolation, internal class resolution,
duplicate-ID rejection, shared Newtonian-limit underdetermination, simple
undecidable-family handling, valid boundary equivalence, unique
nondistinctive-EH collapse, and unique native-distinctive selection.

### Retained terminal boundary

```text
boundary probes:
2 / 2 PASSED
```

The postulate-required probe differs from its underdetermined baseline only at:

```text
$.terminal_evidence_ids
```

### Required adversarial controls

```text
adversarial controls:
6 / 6 PASSED
```

They demonstrate:

1. false caller statement class ignored;
2. `SATISFIES` without evidence rejected;
3. `EQUIVALENT` without an included validated proof rejected;
4. invalid `F_FR -> F_EH` proof rejected;
5. satisfied plus undecidable without property transport remains unresolved;
6. Einstein-Hilbert oracle evidence rejected from the native matrix.

Every declared single-field mutation has its changed path computed from the
baseline and mutation; atomicity is not a hard-coded mutation count.

### Six outcome controls

```text
terminal outcome controls:
6 / 6 PASSED

distinct outcomes reached:
6 / 6

matching outcome count per fixture:
1
```

All retained controls, boundary probes, adversarial controls, and outcome
controls report `evaluate_analysis_v2` as their production entry point.

## Frozen real envelope

The project profile requires the exact ordered identities:

```text
10 frozen project requirements
7 frozen comparison families
70 evidence-bound cells
```

No family has been added to or removed from the real envelope. Synthetic
families exist only in the profile-isolated control catalog and cannot appear
in the project profile.

Packet preparation supplies:

```text
real matrix cells:
0 / 70

real evidence records:
0

real equivalence proofs:
0

real survivor set:
NOT COMPUTED

real scientific outcome:
NOT SELECTED
```

## Standard-GR isolation

`F_EH` remains a comparison oracle only. Evidence whose source role is
`STANDARD_GR_ORACLE` fails with:

```text
STANDARD_GR_ORACLE_NATIVE_EVIDENCE
```

Supplied assumptions are separately resolved and may be recorded in a
conditional exclusion trace, but they cannot alter native family or class
sets. The comparator label is considered only after native evidence validation,
proof-derived reduction, and uncertainty aggregation.

## Independent V2 review requirements

The next review must independently reproduce at least:

1. canonical authority retention under a false caller class;
2. missing-evidence failure for `SATISFIES`;
3. missing-proof failure for `EQUIVALENT`;
4. rejection of `CP_INVALID_FR_EH_PARAMETER_LIMIT`;
5. unresolved class status without exact property transport;
6. standard-GR oracle rejection in the native pass;
7. one exclusive full-path state for each scientific outcome;
8. shared entry-point identity for every control family.

It must also inspect the project-provider custody interface. Acceptance may
authorize one bounded 70-cell analysis with a separately frozen evidence
provider, but it must not treat the synthetic provider as scientific evidence.

## Nonclaims and stopping rule

V2 does not:

- populate a real matrix cell;
- judge a real family;
- compute a real survivor set;
- identify a native gravitational principle;
- authorize a new postulate;
- select Einstein-Hilbert gravity or any other action;
- propose a gravitational action;
- choose matter content;
- execute metric variation or derive stress-energy;
- resume frame-dragging;
- expand the seven-family envelope;
- authorize automatic V3;
- create an automation.

Stopping rule:

> Repair the five contracts, execute only profile-isolated synthetic controls
> through `evaluate_analysis_v2`, prove all six outcomes reachable and
> exclusive, retain the real matrix at 0 / 70, and stop for independent V2
> review.

## Prepared posture

```text
requirements/action-selection v2:
PREPARED_PENDING_INDEPENDENT_REVIEW

retained controls:
8 / 8 PASSED

boundary probes:
2 / 2 PASSED

adversarial controls:
6 / 6 PASSED

six-way outcome controls:
6 / 6 PASSED

real matrix:
0 / 70

family judgments:
NONE

native principle:
NONE IDENTIFIED

postulate:
NONE AUTHORIZED

gravitational action:
NONE PROPOSED

automatic V3:
NOT AUTHORIZED

current authority:
review_native_gravitational_principle_requirements_and_action_selection_packet_v2_result
```
