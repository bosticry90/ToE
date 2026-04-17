RL10 bridge policy standard approval-recording procedure note

Status: ACTIVE_NONLIVE_NONCLAIM
Scope: Repository-local governance object only. No scientific adequacy claim.

Purpose
- Define one bounded repository-local procedure by which RL10 bridge policy standard approval could be recorded.
- Keep approval recordation distinct from restart authorization and QM-STAT execution opening.
- Preserve fail-closed semantics until an explicit valid approval record exists.

Tokens
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_SCOPE_v0: ONE_DECLARED_REPOSITORY_LOCAL_APPROVAL_RECORDATION_PATH_ONLY
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_PRECONDITION_v0: BRIDGE_POLICY_STANDARD_FORMALIZATION_DEFINED_PLUS_APPROVAL_RECORD_OBJECT_DECLARED_PLUS_RESTART_STOP_STATE_ACTIVE
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_REQUIRED_FIELDS_v0: APPROVAL_DECISION_ID_PLUS_APPROVAL_DECISION_TIMESTAMP_UTC_PLUS_APPROVAL_AUTHORITY_ID_PLUS_APPROVAL_ATTESTATION_REFERENCE
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_NON_EQUIVALENCE_RULE_v0: RECORDING_APPROVAL_DOES_NOT_ITSELF_AUTHORIZE_RESTART_OR_OPEN_QM_STAT_EXECUTION
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_FAIL_CLOSED_RULE_v0: IF_ANY_REQUIRED_FIELD_OR_ATTESTATION_IS_MISSING_APPROVAL_REMAINS_UNRECORDED_AND_RESTART_STAYS_CLOSED
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDING_PROCEDURE_STATUS_v0: PROCEDURE_DEFINED_BUT_NOT_EXECUTED

Required approval-record fields
- `approval_decision_id`
- `approval_decision_timestamp_utc`
- `approval_authority_id`
- `approval_attestation_reference`

Ready-to-record checklist
- Confirm the approval-record object remains declared at `formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_v0.md`.
- Confirm the canonical restart no-go endpoint remains active at `formal/docs/release/RESTART_GOVERNANCE_STOP_STATE_SUMMARY_20260414_v0.md`.
- Confirm the current blocker remains `policy_standard_approval_not_recorded` in `formal/output/reports/qm_stat_seam_authorization_readiness_dossier_20260414_v0.json`.
- Wait for a real higher-level approval decision before writing any approval record fields.
- Write all four required fields together with a repository-local attestation reference or leave the record unrecorded.
- Rerun the downstream restart-governance chain immediately after any valid recordation.

Explicitly not authorized
- Do not treat approval eligibility as equivalent to recorded approval.
- Do not treat approval-record object declaration as equivalent to recorded approval.
- Do not write placeholder approval fields or speculative attestations.
- Do not treat this procedure as sufficient to authorize restart.
- Do not open QM-STAT execution before downstream rerun confirms the blocker moved.