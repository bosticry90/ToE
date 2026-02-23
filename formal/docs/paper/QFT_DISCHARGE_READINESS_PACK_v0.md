# QFT Discharge Readiness Pack v0

Spec ID:
- `QFT_DISCHARGE_READINESS_PACK_v0`

Target linkage:
- `TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0`
- canonical discharge source: `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md`

Classification:
- `P-POLICY`

Purpose:
- Provide a bounded, matrix-governed closure-consumer checklist for QFT discharge status maintenance.
- Map each discharge criterion to enforcing tests and concrete artifact pointers.
- Prevent semantic drift by requiring criterion-to-gate-to-artifact traceability.

Canonical matrix binding:
- `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`
- `PILLAR-QFT.matrix_status: CLOSED`
- `QFT_FULL_DERIVATION_ADJUDICATION: DISCHARGED_v0`
- `QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0`

## DISCHARGE_CRITERIA_MAP

### QFT-CRIT-01 Matrix and discharge surface closure
- Description: QFT discharge and inevitability tokens are closed and synchronized on active authority surfaces.
- Enforcing tests: `formal/python/tests/test_qft_full_derivation_discharge_gate.py`; `formal/python/tests/test_qft_full_derivation_adjudication_consistency_gate.py`
- Artifact pointers: `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md`; `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json`; `formal/docs/paper/PHYSICS_ROADMAP_v0.md`; `State_of_the_Theory.md`
- Status: CLOSED

### QFT-CRIT-02 Transition bundle closure chain (cycles 27-31)
- Description: Pre-discharge rollover, exit-row criteria, transition readiness, and adjudication criteria gates remain closed.
- Enforcing tests: `formal/python/tests/test_qft_full_derivation_tranche_rollover_cycle27_gate.py`; `formal/python/tests/test_qft_full_derivation_exit_row_criteria_cycle28_gate.py`; `formal/python/tests/test_qft_full_derivation_predischarge_transition_cycle29_gate.py`; `formal/python/tests/test_qft_full_derivation_discharge_transition_readiness_cycle30_gate.py`; `formal/python/tests/test_qft_full_derivation_adjudication_criteria_cycle31_gate.py`
- Artifact pointers: `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md`; `formal/docs/paper/PHYSICS_ROADMAP_v0.md`; `State_of_the_Theory.md`
- Status: CLOSED

### QFT-CRIT-03 Two-key revalidation and nonflip readiness (cycles 51-55)
- Description: Two-key revalidation transitions and nonflip readiness packet gates remain closed under discharged posture.
- Enforcing tests: `formal/python/tests/test_qft_full_derivation_two_key_auth_revalidation_transition_cycle51_gate.py`; `formal/python/tests/test_qft_full_derivation_keya_auth_revalidation_replay_cycle52_gate.py`; `formal/python/tests/test_qft_full_derivation_keyb_auth_revalidation_replay_cycle53_gate.py`; `formal/python/tests/test_qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_gate.py`; `formal/python/tests/test_qft_full_derivation_nonflip_execution_readiness_packet_cycle55_gate.py`
- Artifact pointers: `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md`; `formal/docs/paper/PHYSICS_ROADMAP_v0.md`; `State_of_the_Theory.md`
- Status: CLOSED

### QFT-CRIT-04 Late-cycle custody closure witness continuity
- Description: Extended cycle-chain closure witnesses remain pinned for the discharged, nonflip execution path.
- Enforcing tests: `formal/python/tests/test_qft_full_derivation_cycle74_gate.py`; `formal/python/tests/test_qft_full_derivation_cycle90_gate.py`
- Artifact pointers: `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md`; `formal/docs/paper/PHYSICS_ROADMAP_v0.md`; `State_of_the_Theory.md`
- Status: CLOSED

## ADJUDICATION_FLIP_POLICY

- Policy lock: `FLIP_REQUIRES_READINESS_PACK_AND_POLICY_GATE_CLOSURE`
- Flip is governance-only and must not be inferred from narrative text.
- Required governance gates before any adjudication-token transition edit:
  - `formal/python/tests/test_qft_discharge_readiness_pack_gate.py`
  - `formal/python/tests/test_qft_full_derivation_discharge_gate.py`
  - `formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py`
  - `formal/python/tests/test_qft_full_derivation_legacy_retirement_gate.py`
  - `formal/python/tests/test_token_migration_window_gate.py`
  - `formal/python/tests/test_state_claim_traceability_audit_gate.py`

## EVOL_EXPANSION_POLICY

- Expansion rule token: `QFT_EVOL_MICRO_EXPANSION_ALIGNMENT_v0: BEYOND_52_REQUIRES_DISCHARGE_ALIGNMENT_OR_EXPANSION_NONCLOSURE_TAG`
- Any `DERIVATION_TARGET_QFT_EVOL_MICRO_XX` with `XX > 52` must either:
  - map to a listed discharge criterion in this pack, or
  - be explicitly marked `EXPANSION_NONCLOSURE` and excluded from closure accounting.
