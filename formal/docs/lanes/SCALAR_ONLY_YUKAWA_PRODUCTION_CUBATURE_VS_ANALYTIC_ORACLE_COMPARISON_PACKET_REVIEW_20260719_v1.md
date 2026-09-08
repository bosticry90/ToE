# Independent review: production-cubature versus analytic-oracle comparison packet V1

Date: 2026-07-19  
Status: `INDEPENDENT_V1_PACKET_REVIEW_COMPLETE_BLOCKED_FINAL_AUTOMATIC_REPAIR`

## Verdict

```text
verdict:
BLOCKED_PRODUCTION_COMPARISON_CONTRACT_INCOMPLETE

principal outcome:
BLOCKED_MUTATION_ROUTING

secondary outcome:
BLOCKED_INCOMPLETE_RECORD_PRECEDENCE
```

Review gates:

```text
43 PASS
5 FAIL
```

The review accepts V1 custody, preservation of all 33 frozen gates, the
18/48/30 source partition, direct use of the historical Yukawa function, the
historical-equivalence preflight, the slow-fit contract, and the numeric bias
and fingerprint metrics. It does not accept the overall comparison contract.

No comparison was executed.

## Unreachable mutation classifications

The repaired systematic-bias predicate requires at least four cases in one
component, each failing orders 32, 40, and 48.

`C03_GAP_FOR_CENTER_DISTANCE` routes only two cases at orders 24 and 48.
`C04_RADIUS_AS_DIAMETER` routes only two cases at orders 16 and 32. Both demand
`IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED` from the production
classifier. Neither control supplies the minimum four cases or the complete
final-order triple, so the demanded label is unreachable by construction.

## Missing C02 prerequisite

The Yukawa-specific classifier requires Newtonian to pass all eight cases at
orders 32, 40, and 48. C02 routes all eight Yukawa cases at those orders but no
Newtonian component. Its required control-fixture label therefore lacks a
mandatory input. The packet does not define a separate preregistered Newtonian
fixture or a lawful reuse point.

## Baseline-dependent C06 and C10 controls

C06 and C10 multiply production values by 1.01 and 1.02. If the unmutated
signed ratio is `r`, the mutated ratio is `c*r`. Positive multiplication leaves
the classifier's relative spread unchanged:

```text
relative_spread(c*r) = relative_spread(r)
```

Therefore, if the unknown production baseline has spread above 0.005, neither
mutation can trigger its required systematic-bias label even when the injection
and classifier are correct. These controls depend on the scientific result
they are supposed to validate and can block the very defective production
behavior the comparison is intended to diagnose.

## Completion-precedence contradictions

Duplicate records receive two incompatible outcomes:

```text
duplicate_cell_behavior:
BLOCKED_INCOMPLETE_RECORD_PRECEDENCE

priority-2 duplicate outcome:
PRODUCTION_COMPARISON_TIMEOUT
```

The timeout token is also listed among the exact nine scientific labels while
priority 2 requires an empty scientific-label list. The packet does not define
whether the token belongs in an administrative outcome field, a scientific
label field, or both. Serialization and precedence are therefore not unique.

The rule suppressing classifications from completed subsets is otherwise
accepted.

## Final-attempt disposition

V1 was the final automatic comparison-contract repair. No automatic V2 is
authorized, and this review may not silently repair the packet.

A fresh selector must choose among the already bounded options:

- historical-path identity isolation only;
- mirror-only comparison with historical claims withdrawn;
- direct analytic-kernel replacement;
- closure of the synthetic torsion-balance lane.

This review authorizes none of those actions directly. It also does not
authorize comparison execution, cubature adjudication, kernel changes,
torque/DFT work, a Stage A rerun, identifiability analysis, or Stage B.

```text
current authority:
select_post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1_review_scientific_response_v0
```
