# EA-02a — Evaluation note for OV-02x (digitization invariance)

This is an **evidence-only** application record of the EA-02 adequacy gate to OV-02x.

Summary
- OV-02x is scoped as an **instrument/digitization invariance** claim: modest, pre-registered perturbations to the frozen digitization do not flip the OV-01g robustness preference.
- This is a robustness/stability anchor, **not** a physics-parameter inference claim.
- **β is not inferred**; language must remain compatible with $\beta=0$ (see DR-β-01).

Checklist alignment (EA-02)
- Frozen data: uses the already frozen Steinhauer Fig. 3a digitization artifact set.
- Pre-registered perturbations: deterministic, bounded relative perturbation patterns.
- Robustness discriminator: uses OV-01g as the downstream decision-grade selector.
- Determinism: locked test asserts repeatable fingerprints.
- Null admissible: a failure to maintain invariance would be recorded as a negative result.

Evidence
- `formal/python/tests/test_ov02_digitization_invariance_gate.py`
- `formal/markdown/locks/observables/OV-02x_digitization_invariance.md`
