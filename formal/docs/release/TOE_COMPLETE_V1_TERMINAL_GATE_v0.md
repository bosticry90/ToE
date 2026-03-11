# ToE Complete-v1 Terminal Gate v0

Spec ID:
- `TOE_COMPLETE_V1_TERMINAL_GATE_v0`

Classification:
- `P-POLICY`

Purpose:
- Define terminal closure gate conditions for `TOE_COMPLETE_v1`.
- Make completion terminality machine-auditable and regression-reopen bounded.

Non-claim boundary:
- gate-definition surface only.
- no theorem promotion.
- no matrix-status promotion.

Terminal gate thresholds:
- `TOE_COMPLETE_V1_TERMINAL_REQUIRED_CONSECUTIVE_GOVERNANCE_GREEN_v0: 3`
- `TOE_COMPLETE_V1_TERMINAL_CRITICAL_PENDING_TOKENS_ALLOWED_v0: 0`
- `TOE_COMPLETE_V1_TERMINAL_REOPEN_POLICY_MODE_v0: REGRESSION_ONLY`

Terminal gate conditions:
1. At least `3` consecutive tranche checkpoints are governance-green.
2. No unresolved critical pending tokens remain in active lanes.
3. Active-lane policies are in frozen-watch regression-only reopen posture.
4. Complete-v1 checkpoint bindings remain matrix/state/roadmap parity-synchronized.

Terminal gate artifact:
- `formal/output/toe_complete_v1_terminal_gate_checkpoint_v0.json`
