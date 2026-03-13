# Derivation Target: SR Empirical Packet 05 Falsification Surface v0

Spec ID:
- `DERIVATION_TARGET_SR_EMPIRICAL_PACKET_05_FALSIFICATION_SURFACE_v0`

Classification:
- `P-POLICY`

Purpose:
- Pin one explicit bounded falsification surface for the SR packet-05 lane.
- Define invalidation hooks without authorizing external-truth adjudication.

Non-claim boundary:
- falsification-surface only.
- no falsification claim by itself.
- no pillar promotion.

Falsification bundle:
- `SR_EMPIRICAL_PACKET_05_FALSIFICATION_STATUS_v0: HOOKS_PINNED_v0_NONCLAIM`
- `SR_EMPIRICAL_PACKET_05_INVALIDATION_HOOK_v0: COVARIANCE_DISCRIMINATOR_DRIFT_EXCEEDS_BOUNDED_TOLERANCE`
- `SR_EMPIRICAL_PACKET_05_INVALIDATION_TRIGGER_v0: REGIME_COMPATIBILITY_FAILURE_WITHIN_BOUNDED_WINDOW`
- `SR_EMPIRICAL_PACKET_05_FAILURE_MODE_v0: SHADOW_NUMERICS_AND_DISCRIMINATOR_DIVERGENCE`