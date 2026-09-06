# Scalar-only Yukawa analytic sphere-kernel replacement packet V0

## Preparation result

```text
verdict:
PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V0

status:
PREPARED_PENDING_INDEPENDENT_REVIEW_NO_IMPLEMENTATION

kernel implementation or adoption:
NOT AUTHORIZED / NOT PERFORMED
```

This is a pre-implementation replacement contract. It consumes only
`prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0` and
rotates authority to independent packet review.

No candidate kernel was created, executed, installed, or wired into Stage A.

## Historical-path custody

The historical Stage A source contains two distinct paths:

```text
live energy entry point:
pair_energy_and_radial_derivative

fixed-tensor cubature helper:
reduced_four_dimensional_density_integral_yukawa_energy
```

The live entry point already contains a related sphere-form-factor
implementation. The cubature helper was used by the failed validation
benchmark. This packet does not relabel the helper as the live production
energy path.

The retired comparison never adjudicated the helper. It remains neither validated nor invalidated.
Its source and evidence are retained read-only and are not called by this
preparation.

Accordingly, a future “replacement” means a versioned, oracle-qualified
hardening of the live sphere-energy evaluator and its validation basis. It does
not mean that the project has discovered a cubature defect.

## Frozen analytic kernel

For center distance `D`, radii `R1,R2`, surface gap
`g=D-R1-R2`, masses `M1,M2`, positive range `lambda`, and
`x_i=R_i/lambda`, the proposed energy contract is

```text
U_N = -G*M1*M2/D
dU_N/dD = G*M1*M2/D^2

F(x) = 3*(x*cosh(x)-sinh(x))/x^3

U_Y = -(1/3)*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)/D

dU_Y/dD = (1/3)*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)
           *(1/D^2 + 1/(lambda*D)).
```

The total component is the componentwise sum. Energies are joules; radial
derivatives are joules per metre. For positive coupling, both energies are
negative and both derivatives are positive. Equal and unequal radii must use
the same exchange-symmetric path.

The production amplitude remains exactly `A_Y=1/3`. Nondefault amplitudes,
sign reversal, or removal of one form factor are validation controls only.

## Stable numerical representation

The evaluator uses `H(x)=exp(-x)F(x)` and

```text
F(x1)F(x2)exp(-D/lambda)
  = H(x1)H(x2)exp(-g/lambda).
```

The preregistered regimes are:

| Regime | Domain | Required evaluation |
|---|---:|---|
| Point boundary | `x=0` | `H(0)=1` exactly |
| Small | `0<x<=0.1` | Series through `x^8` |
| Moderate | `0.1<x<=40` | Scaled direct expression |
| Large | `40<x<=1000` | `3*((x-1)+(x+1)e^-2x)/(2x^3)` |

Direct `sinh` or `cosh` evaluation is forbidden in the large branch. Inputs
above `x=1000` are outside the accepted numerical domain and must fail closed.
The six accepted overlap probes and their existing tolerances remain frozen.

The pair evaluator must preflight the logarithmic magnitude. A nonzero result
that would overflow or underflow binary64 raises a deterministic
`FloatingPointError` carrying the log magnitude; it may not silently become
zero or infinity.

## Domain and limiting behavior

The physical domain is strictly non-overlapping:

```text
D > R1 + R2
g > 0
lambda > 0 for Yukawa and total components
M1,M2 > 0
R1,R2 >= 0
```

Binary64 evaluation also requires

```text
g >= 16*ulp(max(D,R1+R2)).
```

A smaller positive gap is rejected as numerically unresolved. Touching and
overlapping spheres are rejected. The exact `R=0` boundary is retained only as
the point-particle compatibility limit with an explicit mass and `H(0)=1`.

The only allowed zero-range compatibility case is the historical Newtonian
benchmark with `component="newtonian"`; it bypasses the Yukawa core. Yukawa and
total requests require strictly positive range.

The future implementation must reproduce:

- the finite `g->0+` limit;
- decay to zero at large separation;
- the point-particle Yukawa kernel as both radii approach zero;
- the long-range limit `U_Y -> -(1/3)GM1M2/D`;
- exact linearity in the Yukawa amplitude and exact zero at zero coupling.

## Caller-interface correspondence

The compatibility entry point remains
`pair_energy_and_radial_derivative`. It accepts scalar or NumPy-array center
distances and scalar masses, radii, range, and amplitude. It returns

```text
(energy_J, dU_dD_J_per_m)
```

as float64 NumPy arrays with exactly the input distance shape, including a
zero-dimensional array for scalar input. Component routing remains exactly
`newtonian`, `yukawa`, or `total`.

This packet freezes the interface; it does not approve the current internals
or install new ones. Torque and angular semantics are outside this contract.

## Independent qualification obligations

A ready packet review may authorize one isolated shadow implementation and
qualification only. The candidate must live in a new versioned module and may
not import or call:

- the accepted oracle evaluator;
- the old cubature helper;
- the production dispatch path.

Validation must use the frozen 120-digit radial values from the accepted oracle
execution as read-only references. All eight accepted cases, all six overlap
probes, limits, exchange symmetry, equal/unequal radii, near-contact guards,
`x=1000`, output schema, and exception behavior must pass.

Twelve live-path mutations cover distance semantics, missing form factors,
normalization, signs, derivative signs, unstable small/large branches, domain
guards, output schema, and reference-sharing. Metadata-only mutation rejection
is insufficient.

The future shadow run is capped at 300 seconds and 1024 MiB. It requires raw
logs, stage-atomic evidence, process-group cleanup, and zero surviving
processes. Its deterministic runtime probe is 10,000 fixed scalar pair
evaluations, with a median-of-five limit of five seconds and no parallelism.

## Implementation, adoption, and rollback separation

The lifecycle is frozen as:

```text
pre-implementation packet review
-> isolated shadow implementation and qualification
-> independent qualification-result review
-> fresh production-adoption selector and packet
-> versioned adoption with a tested rollback seam
```

No earlier stage authorizes a later stage automatically. Shadow qualification
cannot alter production imports or dispatch.

A future adoption must retain the hash-pinned historical source and use an
explicit kernel identifier and dispatch seam. Every scientific result must
record the kernel ID, kernel source hash, and oracle reference hash. Mixing
outputs from different kernels in one scientific record is forbidden.

Rollback restores the historical dispatch only. This operational rollback is not scientific validation:
Stage A remains blocked, and the old cubature remains unadjudicated. Automatic
fallback after candidate failure is forbidden.

## Independent review outcomes

```text
ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_READY
BLOCKED_REPLACEMENT_INTERFACE_IDENTITY
BLOCKED_REPLACEMENT_DOMAIN_COVERAGE
BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE
BLOCKED_REPLACEMENT_FIREWALL
```

Only the ready outcome may authorize one isolated shadow implementation and
qualification. It does not authorize production adoption. Any block requires a
fresh scientific-response selector; there is no automatic packet V1 or
comparison V2.

## Scope firewall

Preparation copied accepted oracle evidence without recomputing it. It did not
call the old cubature, calculate new interaction values, implement a kernel,
change production code, compute torque or DFTs, produce the real-150 vector,
construct a Jacobian or SVD, decide identifiability, rerun Stage A, or authorize
Stage B.

```text
current authority:
review_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_result
```
