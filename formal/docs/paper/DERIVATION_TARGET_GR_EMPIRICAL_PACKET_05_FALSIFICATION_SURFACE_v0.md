# Derivation Target: GR Empirical Packet 05 Falsification Surface v0

Spec ID:
- `DERIVATION_TARGET_GR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0`

Classification:
- `P-POLICY`

Purpose:
- Pin one explicit bounded falsification surface for the GR packet-05 lane.
- Define invalidation hooks without authorizing external-truth adjudication.

Non-claim boundary:
- falsification-surface only.
- no falsification claim by itself.
- no pillar promotion.

Falsification bundle:
- `GR_EMPIRICAL_PACKET_05_FALSIFICATION_STATUS_v0: HOOKS_PINNED_v0_NONCLAIM`
- `GR_EMPIRICAL_PACKET_05_INVALIDATION_HOOK_v0: WEAK_FIELD_POISSON_RESIDUAL_SIGN_OR_SCALE_FAILURE`
- `GR_EMPIRICAL_PACKET_05_INVALIDATION_TRIGGER_v0: RESIDUAL_MISMATCH_BEYOND_BOUNDED_WINDOW`
- `GR_EMPIRICAL_PACKET_05_FAILURE_MODE_v0: SHADOW_NUMERICS_AND_DISCRIMINATOR_DIVERGENCE`