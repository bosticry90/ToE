# Scalar-only Yukawa production-cubature versus analytic-oracle comparison packet V1

Date: 2026-07-19  
Status: `PREPARED_PENDING_INDEPENDENT_REVIEW_NO_EXECUTION`

## Verdict

```text
PREPARED_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_V1
```

V1 repairs only the seven failed comparison-contract gates. The other 33
review gates, qualified oracle, eight cases, six orders, two components, 96
scientific records, base accuracy rules, resource envelope, and downstream
firewalls remain frozen. No comparison value was calculated during preparation.

## Exact production-source map

The 96 records now have unambiguous sources and evidence scopes:

- 18 historical Stage A Yukawa cells call the exact historical function for
  the three legacy cases at all six orders.
- 48 Newtonian companion cells use the parameterized mirror and can never be
  reported as historical Stage A output.
- 30 mirror-extension Yukawa cells cover the five nonlegacy cases and cannot
  support historical claims.

The order is frozen as case, ascending cubature order, then Newtonian before
Yukawa. Every result and eventual label must serialize its evidence scope.

## Historical-path preflight

Before mutations or scientific cells, the historical Yukawa function and
`_fixed_density_integral(summation='ORDINARY')` are compared on all three
legacy cases at orders 8, 16, and 24, historical first and mirror second.

Every pair must satisfy:

```text
abs(H-M) <= 1e-36 J + 5e-14 * max(abs(H), abs(M))
```

Failure yields `BLOCKED_PRODUCTION_PATH_IDENTITY` and stops. Higher-order
historical records still call the historical function directly.

## Slow convergence and economic inferiority

A slow-fit candidate must fail at order 48 and have positive finite errors that
decrease strictly over orders 16, 24, 32, 40, and 48, with each successive
ratio below 0.95.

V1 freezes ordinary least-squares fits of `log(error)=a-p log(order)` on the
full five orders and tail four orders. Both require `R² >= 0.98`, positive
exponents, and at most 20% relative exponent disagreement. Required order must
be 49 through 192.

Per-case runtime fits `log(seconds)=b+s log(order)` with `R² >= 0.95` and a
positive exponent. Components from one case execution are not double counted.
Economic inferiority requires a projected case above 60 seconds or the eight-
case total above 1,200 seconds. Invalid or unstable extrapolations cannot be
rounded into the slow-convergence label.

## Bias and Yukawa fingerprint

Systematic ratios are grouped separately by component. At least four cases in
one component must fail at all of orders 32, 40, and 48. The frozen ratio vector
must have relative max-to-min spread at most 0.005, absolute median bias at
least 0.001, and one common sign.

The Yukawa fingerprint has 24 entries: eight cases by orders 32, 40, and 48,
with entry `U_production/U_oracle-1`. It is compared only with the live missing-
one-third control. Matching requires relative L2 distance at most 0.05,
entrywise difference at most 0.10, and at least 23 of 24 signs agreeing.

## Mandatory controls and completion

V1 has one path-identity preflight plus the ten frozen V0 controls. Every route
now specifies cases, orders, components, sequence, injection point, acceptance
rule, required detection, and failure consequence.

Scientific classification is permitted only after all 96 scientific cells are
unique, complete, finite, and source-valid, all eleven mandatory controls pass,
and every custody gate passes.

Precedence is exclusive:

1. Custody, oracle, or identity failure: identity/custody block only.
2. Timeout, cap, missing, duplicate, or nonfinite cell: timeout only.
3. Mutation-control failure: control block only.
4. All prerequisites pass: evaluate the exact nine frozen scientific labels.

Partial cells may remain custody evidence but cannot support scientific labels.

## Boundary

V1 is the final automatic comparison-contract repair. No automatic V2 is
authorized. This packet does not authorize comparison execution, cubature
adjudication, kernel changes, torque/DFT work, the real-150 vector,
identifiability, a Stage A rerun, or Stage B.

```text
current authority:
review_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1_result
```
