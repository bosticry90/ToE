# EA-01a EA-01 evaluation — OV-01g (robustness-only)

Date: 2026-01-18

This note applies the EA-01 Empirical Anchor Adequacy Policy to the OV-01g result.

## Claim

OV-01g (fit-family robustness preference: curved proxy selected for robustness-only evaluation) meets EA-01’s acceptance criteria and may be promoted to **Empirically Anchored**, explicitly **without** any inference that β differs from 0.

## Checklist (EA-01)

1. Frozen external data

- Uses frozen, fingerprinted Steinhauer Fig. 3a digitization artifacts (DR-02/03/04d/05) and their curved companions.

2. Model-independent robustness

- OV-01g compares multiple admissible windows/fits (multi-window envelope) and prefers the curved proxy only when it reduces cross-window brittleness under declared thresholds.

3. No parameter over-interpretation

- DR-β-01 records that β is compatible with 0 across windows and is not decision-grade; OV-01g/POL-01 language is robustness-only.

4. Deterministic reproduction

- OV-01g has deterministic code paths and locked reports/tests.

5. Negative result admissible

- The EA-01 gate explicitly allows null conclusions (e.g., no evidence that β differs from 0) to qualify.

## Sources

- `State_of_the_Theory.md` entries: EA-01, DR-β-01, OV-01g, POL-01
- Locks: `formal/markdown/locks/observables/OV-01_fit_family_robustness_DR02_DR03_DR04d_DR05.md`
- Locks: `formal/markdown/locks/bridges/DR_beta_relevance_verdict_DR02_DR03_DR04d_DR05.md`
- External: `formal/external_evidence/bec_bragg_steinhauer_2001/0111438v1.pdf`
