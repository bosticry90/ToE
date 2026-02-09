# DR low-k window point counts — Steinhauer Fig. 3a digitization

Date: 2026-01-18

## Purpose

This lock documents (from the frozen digitization CSV) how many Fig. 3a dispersion points exist below various $k_{\max}$ thresholds.

This is included to make the feasibility (or infeasibility) of constructing a **higher-N** “smallest-window” DR artifact auditable without guessing or inventing points.

## Source

- `formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv` (rows with `figure=Fig3a`)

The Fig. 3a digitization contains 13 points with the following $k$ values (µm$^{-1}$):

0.418478, 0.703805, 1.065218, 1.407608, 1.750000, 2.092392, 2.453804, 2.777175, 3.138588, 4.184784, 6.809783, 10.347826, 14.589675

## Counts by $k_{\max}$

| $k_{\max}$ (µm$^{-1}$) | N points with $k \le k_{\max}$ |
|---:|---:|
| 1.60 | 4 |
| 1.65 | 4 |
| 1.70 | 4 |
| 1.75 | 4 |
| 1.80 | 5 |
| 2.10 | 6 |
| 2.50 | 7 |
| 3.20 | 9 |

## Implication for DR-04′

- Under the currently frozen digitization, **there are only 4 points with $k\le 1.6$ µm$^{-1}$**.
- The **smallest available** $k_{\max}$ that yields **$N\ge 5$** is the 5th point at:
  - $k_{\max}=1.75000027210818$ µm$^{-1}$ (so any rule using $k\le 1.8$ µm$^{-1}$ yields the same 5-point sample).

Therefore, constructing a distinct “near-$k\le 1.6$ but $N\ge 5$” DR window artifact requires **either**:

- extending the digitization with additional points below $k\le 1.6$ µm$^{-1}$ (new evidence), **or**
- changing the window rule away from a simple $k\le k_{\max}$ threshold in a way that is explicitly justified.
