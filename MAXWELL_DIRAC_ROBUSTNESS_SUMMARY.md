# Maxwell–Dirac and Robustness Summary

**Evidence snapshot:** 2026-07-16  
**Scope:** bounded classical c-number zero-mode work and its descendant-robustness study

This document is an explanatory index. The versioned JSON reviews named below
remain the evidence-bearing records.

## Bottom line

The repository contains an accepted bounded numerical result for a classical
Maxwell–Dirac zero-mode reduction. It does **not** contain an accepted broad
robustness result for that model.

The canonical model result supports reproducible matter–field energy exchange
and total-energy conservation within frozen assumptions and tolerances. The
later robustness matrix is authoritatively classified as
`NUMERICALLY_BLOCKED`: one loose-tolerance solver-verification run in the
strong/low corner exceeded four pre-frozen residual ceilings. Under the frozen
all-role rule, that single blocked member prevents conditional or broad
robustness and leaves descendant materiality unevaluated.

## Model route

### 1. Foundation

The accepted foundation is a unit-complete, two-species, c-number
Maxwell–Dirac object. “C-number” is important: this is a classical field model,
not a quantized Maxwell–Dirac or QED calculation.

Evidence: [foundation result review](formal/docs/release/MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_RESULT_REVIEW_20260713_v0.json).

### 2. Why the simplest (1+1) truncation was rejected

An attempted strict reduction that removed the transverse gauge components was
independently blocked. Generic retained matter data produce transverse currents
`J2` or `J3`, so setting `A2 = A3 = 0` is not generally an invariant truncation.
This is retained as a structural negative result, not worked around silently.

Evidence: [strict-reduction consistency result review](formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0.json).

### 3. Full zero-mode reduction

The accepted analytic route keeps the (1+1) gauge field and retains `A2` and
`A3` as transverse gauge descendants, commonly recorded as `phi2` and `phi3`.
It also retains two opposite-charge species and both reduced spin sectors.

Evidence: [full zero-mode analytic result review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0.json).

## Accepted canonical numerical result

The independent canonical review accepted this maximum claim: under the frozen
dimensional, boundary, gauge, and discretization assumptions, the bounded model
exhibits reproducible matter–field energy exchange and total conservation within
the frozen convergent numerical tolerance.

Selected reviewed metrics:

| Metric | Reviewed value |
| --- | ---: |
| Maximum total-energy drift | `1.990000178531126e-12` |
| Matter–field exchange ratio | `352.6967159703898` |
| Maximum transverse descendant change | `6.826809919994493e-08` |
| Temporal `phi2` convergence order | `1.9996050420957903` |
| Spatial `phi2` convergence order | `1.9689720461647104` |
| Temporal energy convergence order | `2.0750213758270375` |
| Wilson continuum recovery order | `0.9355092887458452` |
| Positive controls | `12` |
| Negative controls | `27` |

Evidence: [canonical simulation result review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json).

These are numerical diagnostics in the frozen model. They are not measurements
of nature and do not imply empirical adequacy, QFT completion, seam closure, or
new physics.

## Descendant necessity and robustness study

### Frozen design

After an engineering pilot and calibration reviews, the repository froze a
fourteen-row scientific study. Each row had thirteen records, giving 182
scientific records; 8 positive and 13 negative controls brought the exact
canonical execution to 203 records. The one-time execution completed with no
excluded records and preserved raw outputs for independent review.

Key evidence:

- [guardrail v1 result review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260714_v1.json)
- [calibration and parameter-freeze v3 result review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v3.json)
- [canonical execution record](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXECUTION_20260714_v2.json)

### Independent result

The independent review accepted the execution custody and reconstructed the
classifier, but its scientific verdict was `ACCEPT_NUMERICALLY_BLOCKED_CANONICAL_RESULT`.
All four threshold failures occurred in:

`R13_CORNER_STRONG_LOW:SOLVER_TOL1eM08`

| Residual ceiling | Observed | Frozen limit | Observed / limit |
| --- | ---: | ---: | ---: |
| Gauss residual | `5.68643754154526e-14` | `5e-14` | `1.137287508309052` |
| Continuity residual | `4.991664308458266e-11` | `4e-11` | `1.2479160771145665` |
| Longitudinal exchange residual | `3.4243223273183233e-20` | `8e-21` | `4.280402909147905` |
| Longitudinal Maxwell residual | `8.324331825593695e-15` | `6e-15` | `1.387388637598949` |

The failed record used solver tolerance `1e-8`, grid size `16`, time step
`0.003125`, duration `0.05`, and an iteration cap of `80`. The corresponding
`1e-10` and `1e-12` solver members passed the same four ceilings. The primary
run, deterministic duplicates, and spatial and temporal refinements also
passed them.

The review therefore identifies a tolerance-dependent numerical-admissibility
block under the frozen all-role rule. It does not authorize interpreting the
failure as a physical instability or a model-domain boundary. The thirteen
passing scientific rows remain descriptive only.

Primary evidence: [canonical robustness result review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json).

## Current follow-up

The subsequent diagnostic review retained the numerical block and reported the
root numerical mechanism as unresolved. A route-selection review chose a
bounded instrumented R13 mechanism experiment. Its design was independently
accepted. Numerical-freeze v0 was blocked on contract defects; a versioned v1
freeze packet is now prepared and pending independent review in the current
working-tree snapshot.

That follow-up may produce numerical-mechanism evidence only. It does not reopen
the frozen robustness classification and does not authorize execution,
threshold relaxation, row exclusion, descendant materiality, a new `E-REPRO`
claim, or a pillar/seam promotion.

Current follow-up evidence:

- [R13 diagnostic result review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PACKET_REVIEW_20260715_v0.json)
- [R13 route-selection result review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_PACKET_REVIEW_20260715_v0.json)
- [instrumented experiment design v1 review](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_20260715_v1.json)
- [instrumented experiment numerical-freeze v1 packet](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_20260715_v1.json)

## Claim boundary

Supported at this snapshot:

- an accepted analytic full zero-mode reduction with transverse descendants;
- a reproducible bounded canonical simulation result under frozen assumptions;
- preserved positive and negative controls;
- a complete 203-record robustness execution with independently checked custody;
- an authoritative `NUMERICALLY_BLOCKED` robustness classification; and
- a focused mechanism-diagnostic route still under preparation/review.

Not supported:

- broad or conditional robustness;
- a descendant-materiality classification;
- a demonstrated model-domain boundary or physical instability;
- empirical validation;
- quantum Maxwell–Dirac/QED completion;
- electromagnetic or QFT pillar completion;
- seam closure, `C_k` dynamics, CCFT validation, or master-action promotion;
- a complete Theory of Everything; or
- a repository-wide green claim.

## Reproduction entry points

Discover the exact validators and tests without relying on this summary’s
snapshot-specific filenames:

```powershell
rg --files formal/python/tools | rg -i "dirac_maxwell.*robustness|dirac_maxwell.*canonical"
rg --files formal/python/tests | rg -i "dirac_maxwell.*robustness|dirac_maxwell.*canonical"
```

Then run the focused test or a validator’s read-only `--check` mode through
`py.ps1`. For environment setup and higher validation tiers, see
[TECHNICAL_REPOSITORY_GUIDE.md](TECHNICAL_REPOSITORY_GUIDE.md).
