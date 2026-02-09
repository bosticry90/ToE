# OV-01g Fit-family robustness gate (linear vs curved) — DR-02/03/04/05 (Variant A)

Date: 2026-01-18

## Purpose

This report reruns the OV-01g fit-family robustness gate over the frozen DR-02/03/04/05 window family, but with curved-fit admissibility evaluated under:

- `adequacy_policy = DQ-01_variantA`

Variant A is a **scoped rehabilitation attempt**: it admits **DR-04 at N=4 only**, with strict error bounds and β explicitly not used for inference.

## Frozen envelope values (g = 0.3)

(Envelope numbers are unchanged from the prior locked report; only the adequacy policy differs.)

Linear (OV-01d):

- $R_{\max}^{(\mathrm{lin})} = 0.29003318302945985$
- $R_{\mathrm{rms}}^{(\mathrm{lin})} = 0.18477504796266590$

Curved (OV-01e):

- $R_{\max}^{(\mathrm{curv})} = 0.22969472619504086$
- $R_{\mathrm{rms}}^{(\mathrm{curv})} = 0.15288066430819110$

Ratio:

- $Q = R_{\max}^{(\mathrm{curv})}/R_{\max}^{(\mathrm{lin})} = 0.7919540125501154$

## Curved-fit adequacy under DQ-01_variantA

- DR-04 curved fit is admitted **only** under Variant A’s DR-04@N=4 clause.
- β is explicitly recorded as **not used for inference** at N=4 (`beta_ignored_low_n`).

See delta evidence:
- `formal/markdown/locks/bridges/DR_fit_adequacy_curved_variantA_DR04.md`

## Gate decision

Since $Q \le 0.9$ and curved adequacy passes under `DQ-01_variantA` → **PREFER CURVED**.

## Notes

- This is a policy-tagged decision: the curved preference is conditional on `adequacy_policy = DQ-01_variantA`.
- Variant A does not upgrade β into an interpretable curvature claim at N=4; it only restores the curved family as a predictive proxy over the frozen window set.
