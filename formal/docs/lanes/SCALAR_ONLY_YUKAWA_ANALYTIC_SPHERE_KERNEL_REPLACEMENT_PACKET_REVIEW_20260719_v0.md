# Independent review: analytic sphere-kernel replacement packet V0

## Review outcome

```text
verdict:
BLOCKED_ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_INCOMPLETE

review gates:
51 PASS / 11 FAIL

principal outcome:
BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE

secondary outcomes:
BLOCKED_REPLACEMENT_INTERFACE_IDENTITY
BLOCKED_REPLACEMENT_DOMAIN_COVERAGE
```

The packet is mathematically well directed and preserves the correct
architecture and authority boundaries. It is not yet executable as an
independent shadow-qualification contract. No candidate implementation is authorized.

## Accepted surfaces

The review accepts:

- the Newtonian and two-factor Yukawa energy formulas;
- the corresponding analytic radial-derivative formulas;
- `A_Y=1/3`, SI units, signs, and sphere-exchange symmetry;
- the small, moderate, and large `x` evaluator regimes through `x=1000`;
- the strict non-overlap and machine-resolvable-gap rules;
- the distinction between `pair_energy_and_radial_derivative` and the separate
  fixed-tensor cubature helper;
- custody of the accepted oracle and historical Stage A sources;
- separation of shadow qualification, independent review, adoption, and
  operational rollback;
- all downstream firewalls.

The historical cubature remains unadjudicated.

## Principal block: validation independence

The proposed replacement returns both energy and `dU/dD`, but the eight frozen
oracle rows contain independent energy values only. The radial derivative has no independent frozen reference,
finite-difference cross-check, or numerical tolerance. A candidate could
therefore reproduce every energy row while returning an incorrect derivative.

The twelve mutations are identities, not executable routes. Each row contains
only a mutation ID and a generic required result. It does not freeze:

- cases or components;
- the injection point;
- execution order;
- numeric tolerances or required exceptions;
- the adjudicator path;
- the exact failure consequence.

The import bans and reference-parser separation are accepted, but they cannot
make an incompletely routed test reproducible.

## Secondary block: interface identity

The public entry-point name and output shape are frozen, but the replacement
boundary does not identify the exact internal functions to replace, the future
dispatch symbol, or the callers that must remain unchanged.

The current function treats nonpositive `lambda` differently by component. The
packet introduces stricter semantics without a complete current-versus-proposed
compatibility matrix. It also does not say whether one invalid element in a
distance array rejects the whole call atomically, and it labels three public
arguments “validation only” without freezing an enforcement mechanism.

These omissions prevent an independent reviewer from deciding interface parity
without inventing behavior.

## Secondary block: domain and regression coverage

The eight regression rows preserve outputs but not their executable inputs.
They omit the radii, masses, gap, center distance, range, and amplitude needed
to reproduce the calls directly from this packet.

The point, long-range, near-contact, small-coupling, and boundary checks are
named but have no exact input ladders, expected values, or tolerances. Likewise,
the 10,000-call runtime test has no frozen workload vector or component order.

The packet requires three provenance fields but does not freeze a canonical
serialization object, float encoding, key order, or serialization-failure
consequence.

## Disposition

The review performed no repair. In particular, it did not add regression
inputs, derivative references, mutation routes, interface semantics, runtime
vectors, or a serialization schema.

Because the packet itself prohibits automatic repair after a block, the next
step is a fresh scientific-response selector. It may compare a narrowly
authorized contract repair, splitting energy and derivative qualification, or
deferring or closing the synthetic torsion-balance lane.

No automatic packet V1, shadow implementation, kernel installation, comparison
V2, torque/DFT work, Stage A rerun, identifiability analysis, or Stage B activity
is authorized.

```text
current authority:
select_post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_review_scientific_response_v0
```
