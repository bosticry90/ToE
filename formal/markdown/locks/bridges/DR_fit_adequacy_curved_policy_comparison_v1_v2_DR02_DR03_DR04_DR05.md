# DQ-01 policy comparison (v1 vs v2) — DR-02/03/04/05 (curved)

Date: 2026-01-17

This report compares DQ-01 curved-fit adequacy decisions under two explicit policies:

- **DQ-01_v1 (strict)**: requires $N\ge 5$ and requires β identifiability.
- **DQ-01_v2 (tiered)**: if $N=4$, allows conditional pass under stricter RMSE and stderr(c0) thresholds and **ignores β identifiability** (records `beta_ignored_low_n`).

The reporting surface is unchanged; only the policy parameter differs.

## Summary table

| Window | v1 pass | v1 reason codes | v2 pass | v2 reason codes |
|---|:---:|---|:---:|---|
| DR-02 curved (k≤3.2) | yes |  | yes |  |
| DR-03 curved (k≤2.1) | yes |  | yes |  |
| DR-04 curved (k≤1.6) | no | n_points_lt_min; beta_not_identifiable | yes | beta_ignored_low_n |
| DR-05 curved (k≤1.8) | yes |  | yes |  |

## Notes

- Under DQ-01_v2, DR-04 is treated as “low-N admissible” without implying curvature is well identified; β is explicitly ignored for inference at $N=4$.
- The next discriminative loop item should eliminate reliance on the tiered exception by increasing the point count in the smallest-window family (e.g., a new DR window artifact with $N\ge 5$ near k≤1.6).
