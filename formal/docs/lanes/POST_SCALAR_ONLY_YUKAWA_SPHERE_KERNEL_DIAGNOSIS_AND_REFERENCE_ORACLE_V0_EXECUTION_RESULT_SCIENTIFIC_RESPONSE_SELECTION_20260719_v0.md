# Post-diagnosis scalar-only Yukawa scientific-response selection v0

Date: 2026-07-19  
Status: `SELECTED`

## Selection

```text
selected route:
QUALIFY_ANALYTIC_HOMOGENEOUS_SPHERE_YUKAWA_ORACLE

selected next target:
prepare_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0

packet prepared now:
NO

oracle execution performed:
NO
```

The selector compared five bounded responses to the accepted
`REFERENCE_ORACLE_INADEQUATE_WITHIN_FROZEN_BUDGET` result:

1. Qualify the analytic homogeneous-sphere oracle.
2. Diagnose performance of the failed four-path execution.
3. Replace the production integration method directly.
4. Redesign the apparatus around simpler geometries.
5. Close the synthetic torsion-balance lane.

The analytic-oracle route is the unique baseline winner. It leads the
performance-diagnosis runner-up by 67 weighted points and remains first in all
30 leave-one-criterion-out and weight-perturbation variants; the smallest
winning margin is 47 points.

## Why this route wins

The accepted result left both the analytic oracle and production cubature
unadjudicated. Qualifying one inexpensive sphere formula directly addresses the
missing reference without pretending that the failed 39-case execution judged
the production method.

If qualified, the oracle could later validate fixed-order cubature, a reduced
integral, an adaptive replacement, torque derivatives, and harmonic extraction.
Direct method replacement ranks lower because there is currently no accepted
reference against which to validate it. A performance-only study could explain
runtime but would not establish the correct sphere interaction.

## Authorized packet-preparation scope

The future packet must be small and self-contained:

- six to nine preregistered non-overlapping sphere cases;
- exact Newtonian shell-theorem normalization;
- independent derivation of the homogeneous-sphere Yukawa form factor;
- `A_Y=1/3`, units, sign, center-distance, gap, and domain checks;
- frozen small-, moderate-, and large-`x` evaluation regimes;
- overlap and continuity tests between evaluation regimes;
- one low-dimensional high-precision cross-check;
- a target total wall-clock ceiling no greater than 600 seconds;
- a target memory ceiling no greater than 2048 MiB;
- per-stage work caps and fail-closed timeout rules.

Future execution custody must require:

```text
process-group termination:
MANDATORY

raw launcher log:
PRESERVED

timeout initiation timestamp:
PRESERVED

child termination timestamps:
PRESERVED

stage-level atomic status:
PRESERVED
```

The independently admissible stages must be declared before execution.
Completed-stage values may become decision-bearing only when the packet
explicitly preregisters that boundary.

## Legitimate future outcomes

```text
ANALYTIC_SPHERE_ORACLE_QUALIFIED
ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE
ANALYTIC_ORACLE_CROSS_CHECK_FAILED
ANALYTIC_ORACLE_QUALIFICATION_TIMEOUT
SPHERE_ORACLE_NOT_VALID_OVER_REQUIRED_DOMAIN
```

Only `ANALYTIC_SPHERE_ORACLE_QUALIFIED` may make a later production-method
comparison eligible for a fresh selector.

## Exclusions and firewalls

This selection does not authorize or perform:

- the old 39-case diagnosis;
- production cubature orders 8 through 48;
- a production integration replacement;
- near-contact profiling across the full domain;
- torque or DFT work;
- apparatus harmonics or the final real-150 vector;
- a Jacobian, SVD, `eta_lambda`, or identifiability decision;
- a diagnosis or Stage A rerun;
- Stage B.

The next action is packet preparation followed by independent review. No oracle
calculation is authorized until that review accepts an executable contract.

