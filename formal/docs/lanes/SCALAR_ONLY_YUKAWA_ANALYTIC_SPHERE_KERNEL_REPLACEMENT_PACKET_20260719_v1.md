# Scalar-only Yukawa analytic sphere-kernel replacement packet V1

## Preparation result

```text
verdict:
PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V1

status:
PREPARED_PENDING_INDEPENDENT_FINAL_V1_REVIEW_NO_IMPLEMENTATION
```

V1 repairs exactly the 11 failed gates from the independent V0 review. The 51 accepted gates remain frozen by hash and may not be redesigned.

No candidate kernel was created, executed, installed, or connected to
production. The historical cubature was neither called nor adjudicated.

## Exact replacement identity

The future shadow candidate is bound to these three internal surfaces:

```text
uniform_sphere_form_factor
scaled_uniform_sphere_form_factor
pair_energy_and_radial_derivative
```

The future dispatch symbol is `SPHERE_PAIR_KERNEL_ID`. Apparatus energy,
analytic torque, force-lever torque, and five-point energy-derivative callers
must remain unchanged. The fixed-tensor cubature helper remains read-only and
excluded from the candidate.

## Component, scalar, and array behavior

V1 freezes a twelve-row matrix covering `newtonian`, `yukawa`, and `total`
against positive, zero, negative, and nonfinite range inputs.

The Newtonian component alone retains the historical `lambda=0` sentinel.
Yukawa and total components require positive finite range. Negative or
nonfinite ranges fail with `ValueError`.

Distance inputs are normalized to float64 arrays. Empty arrays fail. If any
element is nonfinite, touching, overlapping, or otherwise outside the domain,
the whole call fails before producing output. Invalid flat indices are reported
in ascending C order. Scalar input returns zero-dimensional float64 arrays.

Public nondefault amplitude, sign, or form-factor-removal hooks fail with
`PermissionError`. Qualification mutations use a private capability tied to
the launch identity and accepted V1-review hash. Ambient environment or global
validation modes are forbidden.

## Eight complete regression rows

Every accepted oracle case now includes exact binary64 hexadecimal inputs for:

- radii, densities, and masses;
- surface gap and center distance;
- scalar range and amplitude;
- component execution order.

Each row retains the accepted high-precision Newtonian and Yukawa energies and
adds independent derivative references:

```text
dU_N/dD = -U_N/D
dU_Y/dD = -U_Y*(1/D + 1/lambda)
```

The derivative values are constructed in 100-digit decimal arithmetic from
the already accepted 120-digit radial-energy references and frozen inputs. The
candidate energy and derivative are never called while constructing the
reference.

Energy acceptance is

```text
|delta U| <= 1e-38 J + 5e-12*|U_reference|.
```

Derivative acceptance is

```text
|delta dU/dD| <= 1e-34 N + 5e-12*|dU/dD_reference|.
```

## Domain and limit probes

Thirteen exact probes cover point-particle behavior, the Newtonian zero-range
sentinel, a resolved near-contact case, touching and overlap rejection,
`x=1000`, rejection above `x=1000`, zero and half coupling, the long-range
limit, representable large separation, explicit underflow failure, and an empty
array.

Every probe freezes inputs, expected behavior, and absolute/relative tolerance
or required exception. They run in the exact `P01` through `P13` order.

## Twelve routed mutations

Each mutation now freezes:

- case IDs and components;
- an internal injection point;
- baseline-then-mutation execution order;
- a numeric discrepancy or required exception;
- the same candidate and adjudicator path;
- a fail-closed consequence.

The routes cover distance semantics, missing form factors, amplitude, energy
and derivative signs, unstable evaluator branches, domain guards, output
schema, and forbidden oracle sharing. One mutation runs per process and no
mutated result may become scientific evidence.

## Exact 10,000-call runtime workload

The runtime probe uses the eight regression cases in frozen order and cycles
components as `newtonian`, `yukawa`, `total`. Call `i` uses case `i mod 8` and
component `(i//8) mod 3`.

After 24 untimed warmup calls, five single-threaded trials each execute 10,000
scalar calls. The median measured with `time.perf_counter_ns` must not exceed
five seconds. Result-dependent workload changes and parallelism are forbidden.

## canonical serialization and comparison

Qualification results use one exact eleven-key JSON object. All binary64
scientific values are lowercase `float.hex` strings; high-precision references
and tolerances are uppercase decimal strings; durations are integer
nanoseconds.

Canonical bytes are produced with recursively sorted keys, ASCII JSON, no
NaN/Infinity, compact separators, UTF-8 without BOM, and exactly one trailing
line feed. The SHA-256 of those bytes is stored in a separate custody record.

Missing, duplicate, unknown, nonfinite, out-of-order, or unhashable evidence
fails closed. Candidate hex values are converted with `Decimal.from_float`
before applying the frozen absolute-plus-relative comparison envelope.

## Review and final-attempt boundary

Independent V1 review may return only:

```text
ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_READY
BLOCKED_REPLACEMENT_INTERFACE_IDENTITY
BLOCKED_REPLACEMENT_DOMAIN_COVERAGE
BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE
BLOCKED_REPLACEMENT_FIREWALL
```

Only the ready outcome may authorize one isolated shadow implementation and
qualification. It cannot authorize production adoption. V1 is the final
automatic repair; any block requires a fresh selector and no automatic V2.

## Scope firewall

V1 preparation derived reference metadata from accepted evidence but executed
no candidate. It changed no production source or dispatch, called no cubature,
computed no torque or DFT, produced no real-150 vector, constructed no Jacobian
or SVD, decided no identifiability question, reran no Stage A execution, and
authorized no Stage B work.

```text
current authority:
review_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_result
```
