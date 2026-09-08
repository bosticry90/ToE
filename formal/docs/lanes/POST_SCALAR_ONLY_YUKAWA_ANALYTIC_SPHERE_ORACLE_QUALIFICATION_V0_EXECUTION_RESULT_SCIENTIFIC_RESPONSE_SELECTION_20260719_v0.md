# Post-oracle scalar-only Yukawa scientific-response selection V0

Date: 2026-07-19  
Status: `SELECTED`

## Selection

```text
selected route:
COMPARE_FAILED_PRODUCTION_CUBATURE_AGAINST_QUALIFIED_ANALYTIC_ORACLE

selected next target:
prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0

comparison packet prepared now:
NO

comparison executed now:
NO
```

The selector compared six bounded responses to the accepted
`ANALYTIC_SPHERE_ORACLE_QUALIFIED` result:

1. Compare the failed production cubature with the qualified oracle.
2. Replace production cubature immediately with the analytic kernel.
3. Skip to torque and DFT validation.
4. Redesign the apparatus.
5. Close the synthetic torsion-balance lane.
6. Pause this lane and return to the native-gravity priority.

The bounded production comparison is the unique baseline winner. It scores
220, ahead of direct analytic-kernel replacement at 160, and remains first in
all 30 leave-one-criterion-out and weight-perturbation variants. The baseline
margin is 60 points and the minimum sensitivity margin is 45 points.

## Why this route wins

The accepted oracle supplies the missing independent reference, but it does not
explain the failed production calculation. A small energy-level comparison can
now distinguish slow convergence, fixed-order inadequacy, a consistent
normalization or geometry mismatch, and a localized implementation defect.

Immediate replacement ranks second because the analytic kernel is already an
excellent candidate, but replacement would discard the chance to determine why
the frozen production path failed. That diagnosis is inexpensive and useful for
future numerical-method governance. Torque and DFT remain premature because the
energy-level production failure has not been adjudicated.

## Authorized packet-preparation scope

The future packet must freeze a small comparison containing:

- six to eight strictly non-overlapping cases;
- all three failed Stage A sphere configurations;
- wide-separation, small-positive-gap, and Yukawa-transition strata;
- the exact failed production implementation, hash-pinned and unchanged;
- the accepted analytic oracle, hash-pinned and unchanged;
- the production order ladder `8, 16, 24, 32, 40, 48`;
- Newtonian and Yukawa components reported separately;
- absolute error, relative error, error ratios, runtime, and work by order;
- rules for near-zero denominators, convergence, plateaus, and near-threshold
  unresolved results;
- normalization, geometry-distance, and unrefined-dimension probes;
- process-group termination, raw logs, and atomic per-case/per-order records.

The packet must freeze a total target ceiling no greater than 1,200 seconds and
4,096 MiB, with smaller per-case and per-order work caps. Budget exhaustion
fails closed.

## Legitimate future outcomes

```text
PRODUCTION_CUBATURE_VALIDATED_AGAINST_ORACLE
PRODUCTION_CUBATURE_SLOW_BUT_CONVERGENT
FIXED_ORDER_CUBATURE_INADEQUATE
PRODUCTION_IMPLEMENTATION_DEFECT_LOCALIZED
NORMALIZATION_OR_GEOMETRY_MISMATCH
PRODUCTION_COMPARISON_NUMERICALLY_UNRESOLVED
PRODUCTION_COMPARISON_TIMEOUT
```

The future packet must define exact numerical predicates and whether compatible
root-cause labels may coexist. No label may be selected from visual inspection
or after-the-fact tolerance changes.

## Exclusions and firewalls

This selector does not prepare or execute the comparison. It does not authorize:

- repair or replacement of the production kernel;
- another analytic-oracle execution;
- torque or angular DFT calculation;
- apparatus harmonics or the final real-150 vector;
- a Jacobian, SVD, or identifiability decision;
- a Stage A rerun;
- Stage B.

The next action is preparation of the bounded comparison packet, followed by
independent packet review before any comparison execution.

```text
current authority:
prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0
```
