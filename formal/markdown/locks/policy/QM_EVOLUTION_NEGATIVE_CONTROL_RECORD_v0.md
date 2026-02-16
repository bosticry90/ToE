# QM Evolution Negative Control Record v0

Record ID:
- `QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0`

Classification:
- `P-POLICY`

Status token:
- `QM_EVOLUTION_NEGATIVE_CONTROL_STATUS_v0: TEMPLATE_PINNED`
- `QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_STEP_CONTRACT_POPULATED`
- `QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_INVALID_EVOLUTION_CONTEXT_POPULATED`
- `QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_INCOMPATIBLE_STATE_CARRIER_POPULATED`
- `QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ALL_REQUIRED_NEGATIVE_ROWS_POPULATED`

Required negative controls:
- `NEGCTRL_INVALID_EVOLUTION_CONTEXT_v0`
- `NEGCTRL_BROKEN_STEP_CONTRACT_v0`
- `NEGCTRL_INCOMPATIBLE_STATE_CARRIER_v0`

Expected global outcome:
- `OUTCOME_FAILS_INFORMATIVE`

Execution schema:

| Negative ID | Injected violation | Expected failure token | Observed failure token | Reason code | Artifact pointer |
|---|---|---|---|---|---|
| `NEGCTRL_INVALID_EVOLUTION_CONTEXT_v0` | `construct an evolution context with mismatched time/state wiring` | `EvolutionContext` | `EvolutionContext` | `FAIL_INVALID_EVOLUTION_CONTEXT_DETECTED_v0` | `formal/output/qm_evolution_negative_control_invalid_context_v0.json` |
| `NEGCTRL_BROKEN_STEP_CONTRACT_v0` | `replace step-contract witness with a mismatched final-state relation` | `QMStateEvolvesUnderContract` | `QMStateEvolvesUnderContract` | `FAIL_STEP_CONTRACT_MISMATCH_DETECTED_v0` | `formal/output/qm_evolution_negative_control_broken_step_contract_v0.json` |
| `NEGCTRL_INCOMPATIBLE_STATE_CARRIER_v0` | `inject incompatible state carrier witness that violates typed state relation` | `QMState` | `QMState` | `FAIL_INCOMPATIBLE_STATE_CARRIER_DETECTED_v0` | `formal/output/qm_evolution_negative_control_incompatible_state_carrier_v0.json` |

Synchronization pointers:
- `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0.md`
- `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
