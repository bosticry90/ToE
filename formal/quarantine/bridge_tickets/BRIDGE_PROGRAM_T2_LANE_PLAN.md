# BRIDGE_PROGRAM_T2_LANE_PLAN (design-only)

Opened: 2026-02-05

## Scope

Plan minimal implementation lanes to restore `v5_t2` closure for `mismatch_phase_and_pair` without loosening `v5_t2` tolerances.

Pinned `v5_t2` tolerances:
- `toyh_tolerance = 1e-15`
- `phase_anchor_tolerance = 2e-08`
- `current_anchor_tolerance = 2e-08`
- `current_anchor_min_response = 1.25e-08`

## Selected design path

Selected from causal classifier result: **S1 (single-root)**.

Rationale:
- Current frontier shows phase + pair mismatch with uniform `FAIL_PHASE_INVARIANCE_TOL` and downstream `FAIL_PAIR_PHASE_MISMATCH`.
- No independent pair-only failures are currently observed.

## Candidate implementation lanes

### Lane L1 (primary): stabilized phase bridge for tight tolerances

Target:
- New phase bridge observable implementation for `v5_t2` that preserves conceptual phase invariant while improving floating-point conditioning.

Potential techniques (bounded and deterministic):
- evaluate phase-equivalence on normalized complex unit phasors instead of angle subtraction
- use deterministic unwrap/branch handling for phase comparison
- avoid cancellation-sensitive subtraction in invariance residual

Expected effect:
- recover phase pass on currently flipped baseline probes under `v5_t2`
- automatically recover pair pass where pair failure is phase-driven

### Lane L2 (conditional fallback): pair comparator normalization under v5 profile

Trigger:
- only if L1 does not remove pair failures when phase lanes pass under `v5_t2`.

Target:
- keep pair semantics fixed, but compute pair comparator margins in normalized form consistent with profile thresholds.

## Tests to add (implementation-ticket targets)

1. `test_bridge_program_v5_t2_phase_stabilized_restores_baseline_all_pass`
2. `test_bridge_program_v5_t2_phase_stabilized_restores_theta_and_grid_expansion_samples`
3. `test_bridge_program_v5_t2_negative_controls_preserved_phase_wrong_sign`
4. `test_bridge_program_v5_t2_negative_controls_preserved_amplitude_scaling`
5. `test_bridge_program_v5_t2_frontier_lock_after_l1` (expects `n_mismatch == 0` for `v5_t2` artifacts)

## Gating and stop conditions

Proceed L1 only if:
- design ticket accepted,
- reproduction capsule unchanged,
- no tolerance profile changes.

Stop and reopen design if:
- pair-only failures appear under `v5_t2`,
- any negative control starts passing unexpectedly,
- restoring closure requires tolerance relaxation.

## Proposed follow-on ticket namespace

- Preferred implementation ticket: `BRIDGE_TICKET_TOYH_0005_c6_phase_stabilized_t2`
- Conditional fallback ticket: `BRIDGE_TICKET_TOYHG_0002_c6_pair_profile_normalized_t2`

