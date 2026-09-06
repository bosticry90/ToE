# Eöt-Wash 2020 Yukawa primary-evidence custody acquisition packet v0

## Preparation result

```text
target:
prepare_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0

verdict:
PREPARED_PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_PENDING_INDEPENDENT_REVIEW

acquisition execution:
NOT AUTHORIZED

supplement acquisition:
NOT STARTED

author or custodian contact:
NOT AUTHORIZED

likelihood:
NOT EXECUTED
```

This packet prepares a finite, legitimate protocol for determining whether the
complete Eöt-Wash 2020 reproducibility package can enter verified project
custody. It does not acquire evidence or compute a constraint.

## Frozen experiment boundary

```text
experiment:
2020 EÖT-WASH SHORT-RANGE ISL TORSION BALANCE

DOI:
10.1103/PhysRevLett.124.101101

fixed scalar signal:
A_Y = 1/3

experiment scientifically suitable:
YES

independent project likelihood executable now:
NO
```

The acquisition objective is narrow:

> Place the exact observation data, uncertainty and nuisance contract,
> apparatus-to-torque model, and boundary-coverage procedure into verified
> custody—or establish precisely which components remain unavailable.

## Six-item evidence inventory

### 1. Observation torque vector

Required:

- all 95 setting identifiers;
- `18 omega`, `54 omega`, and `120 omega` torque values at every setting;
- 285 numerical measurements in total;
- units, row identifiers, ordering, and selection or exclusion flags.

The target is the full physically indexed vector, not merely 285 numbers.

### 2. Displacement and configuration metadata

Required:

- `x`, `y`, and `s` metadata for every setting;
- detector and attractor configuration identifiers;
- alignment and rotation-phase conventions;
- an ordering key matching the torque vector; and
- all data-cut or configuration-exclusion flags.

### 3. Uncertainty and covariance model

Required:

- pointwise statistical uncertainties;
- correlated systematics;
- a covariance matrix or equivalent generative error model;
- block structure across harmonics or settings;
- regularization or conditioning rules; and
- units and ordering matching the observation vector.

### 4. Five nuisance-prior contracts

For `x0`, `y0`, `s0`, surface roughness, and `gamma`, each record must supply:

- identity and physical meaning;
- prior or constraint form;
- central value and width;
- covariance or declared independence;
- profiling, marginalization, or fixing rule;
- parameter bounds; and
- the exact point at which it enters the forward model.

### 5. Extended-source torque forward model

Required material must independently support:

\[
\lambda_0
\rightarrow V_Y
\rightarrow U_Y(\phi,d)
\rightarrow N_Y(\phi,d)
\rightarrow
\{N_{18\omega},N_{54\omega},N_{120\omega}\}.
\]

It must include the patterned densities and geometry, material properties,
alignment conventions, harmonic definitions, numerical integration or
Fourier-Bessel procedure, calibration, Newtonian implementation, and Yukawa
implementation for arbitrary tested `lambda0` at fixed `A_Y=1/3`.

### 6. Boundary-coverage procedure

Required:

- test statistic;
- null and alternative parameterization;
- nuisance profiling;
- pseudoexperiment or Monte Carlo design, if used;
- simulation count and critical-value construction, if used;
- treatment of `lambda0 -> 0`;
- interpolation rule; and
- reproducibility or random-seed policy.

A confidence curve is an output, not this procedure.

## Source hierarchy

The acquisition order is finite and provenance-first.

| Priority | Source | Present status |
| ---: | --- | --- |
| 1 | Official APS supplemental deposit derived from the article DOI | Expected URL identified; contents not acquired |
| 2 | Official APS article attachments and data links | Metadata identified only |
| 3 | Author-maintained Eöt-Wash or UW institutional archive | Not yet identified |
| 4 | UW ResearchWorks record | Supporting methods only, not a numerical substitute |
| 5 | Authenticated publisher or laboratory archive mirror | Not yet identified |
| 6 | Author or data-custodian contact | Separate authority required; terminal outcome only |

The expected official APS identifier is recorded as:

```text
https://link.aps.org/supplemental/10.1103/PhysRevLett.124.101101
```

Recording the expected canonical identifier is not a download or a finding
about its contents.

Forbidden substitutions include plot digitization, screenshots, secondary
reviews, values inferred from dissertation prose, generic apparatus
reconstruction, and unverified file-sharing mirrors.

## Custody contract

Every acquired object must record exactly:

```text
source_location
acquisition_method
acquisition_timestamp_utc
original_filename
file_type
file_size_bytes
sha256
publisher_or_custodian_identity
license_or_access_conditions
content_description
ingestion_result
completeness_status
```

Custody states are ordered and cannot substitute for one another:

```text
IDENTIFIED
→ ACQUIRED
→ INGESTED
→ VERIFIED
→ COMPLETE
```

- `IDENTIFIED`: an object is known or expected at a canonical identifier.
- `ACQUIRED`: legitimate bytes were obtained and recorded.
- `INGESTED`: the contents were opened and parsed.
- `VERIFIED`: content matches one exact evidence requirement.
- `COMPLETE`: every required field for that evidence item is available.

```text
file acquired:
DOES NOT IMPLY COMPLETE

supplement acquired:
DOES NOT IMPLY LIKELIHOOD EXECUTABLE
```

## Forward-model sufficiency test

The model is executable only if the acquired material permits independent
computation of all six obligations:

1. the authors' Newtonian prediction;
2. all three torque harmonics at all 95 settings;
3. the effects of all five nuisance parameters;
4. the fixed `A_Y=1/3` contribution for arbitrary tested `lambda0`;
5. the exact observation ordering; and
6. the complete residual vector.

Before scalar use, a later executable model must reproduce the published
Newtonian baseline:

```text
chi_squared = 275.0
nu = 285
P = 0.654
```

The numerical reproduction tolerance must be frozen in a later likelihood
packet. It is not selected here.

## Statistical sufficiency test

Acquisition is statistically complete only if the project can specify without
guessing:

\[
\mathcal L(\text{data}\mid\lambda_0,\theta_{\rm nuisance})
\]

or its exact equivalent, reproduce the baseline and five-nuisance procedure,
validate boundary-aware coverage, and reproduce the authors' standard-physics
result within a frozen tolerance.

Having files present cannot substitute for baseline reproduction.

## Bounded acquisition protocol

The future acquisition, if independently authorized, is capped at:

```text
non-contact source tiers:
5

total retrieval attempts:
8

attempts per concrete URL:
2

alternative authenticated mirrors:
2

interactive/manual download sessions:
1
```

Interactive download requires accepted packet review and explicit execution
authority. Access-control circumvention is prohibited.

Failed ingestion means the bytes cannot be opened or parsed according to their
declared type after two documented, non-destructive attempts.

The acquisition must stop after eight total retrieval attempts, exhaustion of
the five non-contact source tiers, or the first principal terminal outcome.

Author or custodian contact remains:

```text
NOT AUTHORIZED
TERMINAL OUTCOME ONLY
```

## Acquisition terminal outcomes

The future acquisition contract supports:

```text
SUPPLEMENT_ACQUIRED_AND_COMPLETE
SUPPLEMENT_ACQUIRED_BUT_OBSERVATION_VECTOR_INCOMPLETE
SUPPLEMENT_ACQUIRED_BUT_COVARIANCE_INCOMPLETE
SUPPLEMENT_ACQUIRED_BUT_NUISANCE_PRIORS_INCOMPLETE
SUPPLEMENT_ACQUIRED_BUT_FORWARD_MODEL_INCOMPLETE
SUPPLEMENT_ACQUIRED_BUT_COVERAGE_PROCEDURE_INCOMPLETE
SUPPLEMENT_IDENTIFIED_BUT_NOT_INGESTIBLE
AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED
PRIMARY_EVIDENCE_NOT_OBTAINABLE_WITHIN_BOUNDED_ROUTE
```

One principal outcome controls the next authority. Up to six subordinate
component findings may coexist.

## Independent packet-review outcomes

The next review may issue:

```text
PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_READY
BLOCKED_EVIDENCE_INVENTORY_UNDERINCLUSIVE
BLOCKED_SOURCE_HIERARCHY_OR_PROVENANCE_UNSAFE
BLOCKED_CUSTODY_COMPLETENESS_CONFLATION
BLOCKED_ACQUISITION_SCOPE_OPEN_ENDED
BLOCKED_CONTACT_OR_DOWNLOAD_PREAUTHORIZED
```

No acquisition outcome is available during packet preparation.

## Parallel computational work

The user-proposed computational lanes are scientifically valuable and remain
explicitly separated:

```text
synthetic forward model and sensitivity forecast:
FRESH AUTHORITY REQUIRED

supplied published-constraint reinterpretation:
FRESH AUTHORITY REQUIRED

independent real-data reanalysis:
REMAINS BLOCKED

new measurement program:
NOT AUTHORIZED
```

The claim classes remain distinct:

- synthetic injection recovery validates a simulated-data pipeline;
- idealized apparatus forecasts are theoretical computational results;
- published-limit translation is supplied empirical evidence; and
- independent reproduction requires real primary evidence and an executable
  apparatus and statistical model.

This packet does not activate a parallel lane.

## Preparation controls

```text
preparation controls:
24 / 24 PASSED

required evidence items complete:
0 / 6

objects acquired:
0

objects ingested:
0

items verified:
0
```

## What preparation did not do

The packet did not:

- download or acquire the supplement;
- bypass access controls;
- contact authors or custodians;
- infer values from plots or the dissertation;
- reconstruct an approximate apparatus;
- execute a likelihood;
- read a bound from a published curve;
- authorize a synthetic forecast or supplied reinterpretation;
- select `lambda0` or `alpha`;
- adopt the scalar branch; or
- select a native principle or gravitational action.

## Current posture

```text
acquisition packet:
PREPARED_PENDING_INDEPENDENT_REVIEW

required evidence items:
0 / 6 COMPLETE

supplement acquisition:
NOT STARTED

author contact:
NOT AUTHORIZED

forward model:
NOT EXECUTABLE

coverage procedure:
NOT EXECUTABLE

likelihood:
NOT EXECUTED

scalar-range bound:
NONE

alpha:
NOT SELECTED

scalar branch:
NOT ADOPTED

native gravitational principle:
NOT IDENTIFIED

gravitational action:
NOT SELECTED

current authority:
review_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0_result
```

The packet prepares evidence acquisition. It does not turn “file obtained”
into “constraint reproduced.”
