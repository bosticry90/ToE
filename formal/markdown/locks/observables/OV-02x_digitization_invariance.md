# OV-02x — Digitization invariance (metamorphic robustness)

This lock documents the **instrument/digitization invariance** anchor candidate OV-02x.

Claim (robustness-only)
- Under a bounded, pre-registered perturbation model applied to the frozen Steinhauer Fig. 3a digitization, the **OV-01g fit-family robustness preference** (linear vs curved DR family) **does not flip**.

Scope / limits
- This is a stability check of the *robustness selector behavior* under modest digitization perturbations.
- It is **not** a parameter inference claim and must not be used to imply $\beta\neq 0$.
- Perturbations are deterministic and bounded by a declared relative tolerance (see test evidence).

Evidence
- Computation + determinism: `formal/python/toe/observables/ov02_digitization_invariance.py`
- Locked regression test: `formal/python/tests/test_ov02_digitization_invariance_gate.py`

External anchor
- Same external source as the frozen digitization used in OV-01g / DR-02 family (Steinhauer PRL 88, 120407 (2002), Fig. 3a).
