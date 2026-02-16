# QM Evolution Robustness Record v0

Record ID:
- `QM_EVOLUTION_ROBUSTNESS_RECORD_v0`

Classification:
- `P-POLICY`

Status token:
- `QM_EVOLUTION_ROBUSTNESS_STATUS_v0: TEMPLATE_PINNED`
- `QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_TIME_PARAMETER_SMALL_POPULATED`
- `QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_STATE_CARRIER_SMALL_POPULATED`
- `QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_OPERATOR_STEP_SMALL_POPULATED`
- `QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_PERTURBATION_ROWS_POPULATED`

Required perturbation families:
- `PERTURB_TIME_PARAMETER_SMALL_v0`
- `PERTURB_STATE_CARRIER_SMALL_v0`
- `PERTURB_OPERATOR_STEP_SMALL_v0`

Outcome tokens:
- `OUTCOME_STILL_SATISFIES_CONTRACT`
- `OUTCOME_FAILS_INFORMATIVE`

Execution schema:

| Perturbation ID | Input delta | Expected outcome | Observed outcome | Reason code | Artifact pointer |
|---|---|---|---|---|---|
| `PERTURB_TIME_PARAMETER_SMALL_v0` | `delta_t is perturbed by +1e-3 under the same typed Time carrier and context` | `OUTCOME_STILL_SATISFIES_CONTRACT` | `OUTCOME_STILL_SATISFIES_CONTRACT` | `PASS_CONTRACT_STABLE_UNDER_SMALL_TIME_PERTURBATION_v0` | `formal/output/qm_evolution_robustness_perturb_time_parameter_small_v0.json` |
| `PERTURB_STATE_CARRIER_SMALL_v0` | `apply an epsilon-level normalization-preserving perturbation to the state carrier` | `OUTCOME_STILL_SATISFIES_CONTRACT` | `OUTCOME_STILL_SATISFIES_CONTRACT` | `PASS_CONTRACT_STABLE_UNDER_SMALL_STATE_CARRIER_PERTURBATION_v0` | `formal/output/qm_evolution_robustness_perturb_state_carrier_small_v0.json` |
| `PERTURB_OPERATOR_STEP_SMALL_v0` | `apply a bounded operator-step coefficient perturbation while preserving typed interface` | `OUTCOME_STILL_SATISFIES_CONTRACT` | `OUTCOME_STILL_SATISFIES_CONTRACT` | `PASS_CONTRACT_STABLE_UNDER_SMALL_OPERATOR_STEP_PERTURBATION_v0` | `formal/output/qm_evolution_robustness_perturb_operator_step_small_v0.json` |

Synchronization pointers:
- `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0.md`
- `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean`
