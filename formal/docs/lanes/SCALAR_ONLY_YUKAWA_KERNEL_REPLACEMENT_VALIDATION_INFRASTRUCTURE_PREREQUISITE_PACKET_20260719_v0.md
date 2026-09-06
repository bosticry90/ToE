# Kernel-replacement validation-infrastructure prerequisite packet V0

## Preparation result

```text
verdict:
PREPARED_SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE_PACKET_V0

status:
PREPARED_PENDING_ONE_TERMINAL_INDEPENDENT_REVIEW_NO_EXECUTION
```

This packet is kernel-agnostic. It contains no Newtonian or Yukawa evaluator,
does not edit replacement packet V1, and does not create replacement packet V2.

## Terminal governance rule

This prerequisite is V0 only. No repair version, prerequisite-to-the-
prerequisite, or new governance abstraction may follow a failed review.

The independent review has two outcomes:

```text
VALIDATION_INFRASTRUCTURE_PREREQUISITE_READY
VALIDATION_INFRASTRUCTURE_PREREQUISITE_FAILED_RETIRE_OR_DEFER
```

A ready review leads to a fresh selector with two choices only: isolated,
non-decision-bearing sandbox implementation or retirement/deferment. A failed
review leads only to retirement or deferment.

## Capability protocol

The future harness uses a 32-byte per-process secret delivered once through an
anonymous pipe. HMAC-SHA256 capabilities bind the run, PID, review hash,
fixture, mutation, nonce, issue time, and expiry time. Tokens expire after 30
seconds and are single-use.

The public fixture call exposes neither a mutation ID nor a capability. The
private call requires both. Authentication has an exact eleven-step order and
eleven exact `PermissionError` codes. Ambient environment variables and global
validation modes are forbidden.

## Typed adjudication

Five recursive schemas define numeric, exception, relational, dependency, and
result records. Numeric comparisons use exact Decimal conversion from
binary64 hexadecimal strings. JSON pointers, comparator algorithms, errors,
and enum values are frozen.

## Synthetic fixture and mutation routes

The packet freezes eight synthetic fixtures and eight complete routes. Every
route binds one input, public baseline, private mutated call, injection point,
single-use capability, predicate, adjudicator, execution order, and failure
consequence. No fixture contains scientific physics.

## Dependency scanning

The scanner contract fixes two virtual source roots, forbidden imports and
calls, AST nodes, alias handling, dynamic-import rejection, deterministic
ordering, parse failure, and expected violations for the bad source.

## Recursive canonical custody

The result root and seven nested record types have exact fields and reject
unknown fields. Six enum families are frozen. The strict parser rejects a
duplicate key before dictionary construction, rejects nonfinite constants, and
then validates fields recursively. Canonical JSON, binary64, Decimal, integer,
array-order, UTF-8, and SHA-256 rules are exact.

## Future synthetic controls

twelve mandatory controls cover public/private separation, forged and replayed
capabilities, typed predicate behavior, every mutation route, dependency
scanning, recursive validation, duplicate keys, and canonical round trips.
Their future envelope is 60 seconds and 256 MiB. They were not executed during
packet preparation.

## Exploratory sandbox distinction

If later selected after a ready review, an isolated candidate may use the
labels:

```text
EXPLORATORY_IMPLEMENTATION_RESULT
NON_PRODUCTION
NON_ADJUDICATIVE
NO_SCIENTIFIC_CLAIM
```

That tier cannot change production, adjudicate cubature, validate Stage A, or
issue a physical conclusion. This packet does not authorize the tier.

No infrastructure or kernel code was created or executed. No real regression,
boundary probe, mutation, cubature, torque, DFT, Stage A, identifiability, or
Stage B work occurred.

```text
current authority:
review_scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_v0_result
```
