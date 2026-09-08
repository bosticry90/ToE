# Post-V1-comparison-review scientific-response selection V0

Date: 2026-07-19  
Status: `SELECTED`

## Selection

```text
verdict:
SELECTED_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_PREPARATION

selected route:
RETIRE_OLD_CUBATURE_COMPARISON_AND_PREPARE_ANALYTIC_KERNEL_REPLACEMENT

selected next target:
prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0
```

The selector compared the four responses authorized after the final V1
comparison-contract block. Direct analytic-kernel replacement scores 211,
ahead of lane closure at 154, and ranks first in 30 / 30 sensitivity variants.

This authorizes packet preparation only. No kernel implementation, replacement,
or execution occurs now.

## Why this route wins

The old-cubature comparison path exhausted its final automatic contract repair
without becoming executable. Continuing with identity-only or mirror-only
diagnosis would spend more effort on a method already dominated by a qualified,
fast analytic representation.

The homogeneous-sphere oracle is independently derived, numerically stable,
accepted across the required nonoverlap domain, and cross-checked to near
machine precision. It supplies a stronger foundation for forward-model recovery
than another attempt to classify the old cubature.

Lane closure remains the runner-up. It is not selected because the accepted
analytic oracle makes one bounded replacement contract scientifically and
computationally proportionate.

## Authorized replacement-packet scope

The future packet must cover the nonoverlapping homogeneous-sphere energy
kernel only. It must freeze:

- Newtonian `-G M1 M2/D` normalization;
- Yukawa strength `A_Y=1/3` and both sphere form factors;
- center-distance and surface-gap semantics;
- strict nonoverlap and positive-range domain guards;
- SI units and attractive sign;
- stable small-, moderate-, and large-argument evaluators;
- the accepted eight oracle cases and independent radial-check custody;
- the existing energy-caller input/output interface;
- deterministic serialization, failure behavior, and runtime limits.

The replacement packet must validate point-particle and long-range limits,
sphere-exchange symmetry, evaluator-overlap regions, the `x=1000` no-overflow
case, exact regression to accepted oracle values, and domain rejection.

The energy kernel only is in scope. Torque, DFT, harmonic vectors, nuisance
derivatives, and identifiability remain separate downstream validation burdens.

## Old cubature disposition

The old-cubature comparison path is retired from automatic repair and execution.
Its source and prior evidence remain read-only historical material. The selector
does not declare the cubature correct, incorrect, convergent, or inadequate.

No comparison V2 is authorized. Failure of the replacement packet requires a
fresh selector; immediate lane closure remains available.

## Firewalls

This selector does not:

- prepare or review the replacement packet;
- implement or execute the analytic kernel in production;
- adjudicate or rerun the old cubature;
- alter torque or DFT code;
- produce the real-150 vector;
- compute a Jacobian, SVD, or identifiability result;
- rerun Stage A;
- authorize Stage B.

```text
current authority:
prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0
```
