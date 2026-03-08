# Derivation Target: SR M5 Theory-Parity Link v0

Spec ID:
- `DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0`

Target ID:
- `TARGET-SR-M5-THEORY-PARITY-LINK-v0`

Classification:
- `P-POLICY`

Purpose:
- Pin the SR lane M5 theory-parity-link tranche under bounded non-claim controls.
- Require hash-pinned cross-surface parity for SR M5 control tokens before any follow-on promotion.

Non-claim boundary:
- bounded theory-parity-link control surface.
- no external truth claim.
- no automatic adjudication promotion.

Tranche bundle (bounded non-claim):
- `SR_M5_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `SR_M5_THEORY_PARITY_ARTIFACT_v0: sr_m5_theory_parity_link_cycle35_v0`
- `SR_M5_THEORY_PARITY_SHA256_v0: 51a538147a70dc0d308cb46f5672c0acfcd0d792d762cca72b8693079f1b92ce`
- `SR_M5_THEORY_PARITY_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/sr_m5_theory_parity_link_cycle35_v0.json`
- coupling gate path: `formal/python/tests/test_sr_m5_theory_parity_link_cycle35_gate.py`

Tranche semantics:
- `SR_M5_READINESS_v0: THEORY_PARITY_LINK_PINNED_v0`
- tranche state is bounded and non-claim; it does not by itself discharge or promote beyond pinned parity-link posture.

Canonical pointers:
- target policy pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md`
- authority lane pointer:
  - `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- deep maturity registry pointer:
  - `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json`

Scope statement:
- this target pins SR M5 theory-parity-link as a bounded governance transition.
- it does not assert inevitability completion or adjudication promotion.








