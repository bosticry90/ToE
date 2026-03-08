# Derivation Target: GR M4 Seam-Closure Promotion v0

Spec ID:
- `DERIVATION_TARGET_GR_M4_SEAM_CLOSURE_PROMOTION_v0`

Target ID:
- `TARGET-GR-M4-SEAM-CLOSURE-PROMOTION-v0`

Classification:
- `P-POLICY`

Purpose:
- Promote the GR lane from bounded M3 completion to bounded M4 seam-closure posture.
- Pin a machine-checkable seam-closure artifact and gate under explicit non-claim boundaries.

Non-claim boundary:
- bounded seam-closure promotion control surface.
- no external truth claim.
- no automatic adjudication promotion.

Completion bundle (bounded non-claim):
- `GR_M4_STATUS_v0: COMPLETE_BOUNDED_v0`
- `GR_M4_SEAM_CLOSURE_ARTIFACT_v0: gr_m4_seam_closure_promotion_cycle01_v0`
- `GR_M4_SEAM_CLOSURE_SHA256_v0: 6c8640b3ace4aed1e9b5f13fe77d7b227a28eae7a7430728ccb98e407fb55857`
- `GR_M4_SEAM_CLOSURE_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- artifact path: `formal/output/gr_m4_seam_closure_promotion_cycle01_v0.json`
- coupling gate path: `formal/python/tests/test_gr_m4_seam_closure_promotion_cycle01_gate.py`

Promotion semantics:
- `GR_M4_PROMOTION_READINESS_v0: CROSS_PILLAR_SEAM_BUNDLE_PINNED_v0`
- promotion is bounded to seam-closure posture and does not by itself assert global inevitability completion.

Canonical pointers:
- target policy pointer:
  - `formal/docs/paper/DERIVATION_TARGET_GR_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- authority lane pointer:
  - `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md`
- deep maturity registry pointer:
  - `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json`

Scope statement:
- this target pins GR M4 seam-closure promotion as a bounded governance state transition.
- it does not assert phase-wide M4 completion.
