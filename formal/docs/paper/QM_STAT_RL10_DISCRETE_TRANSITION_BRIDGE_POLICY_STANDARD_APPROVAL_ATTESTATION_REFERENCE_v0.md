RL10 bridge policy standard approval attestation reference note

Status: ACTIVE_NONLIVE_NONCLAIM
Scope: Repository-local approval attestation witness only. No scientific adequacy claim.

Purpose
- Capture user-provided approval authorization text as an explicit repository-local attestation reference eligible for later use on the declared RL10 approval-recordation surface.
- Preserve fail-closed QM-STAT posture until the remaining required approval fields are provided and written together.
- Keep approval attestation capture explicitly non-equivalent to approval recordation, restart authorization, or QM-STAT execution opening.

Tokens
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_ID_v0: RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_SCOPE_v0: ONE_REPOSITORY_LOCAL_ATTESTATION_WITNESS_ONLY
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_STATUS_v0: USER_APPROVAL_TEXT_CAPTURED_REFERENCE_ONLY_NOT_RECORDED
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_NON_EQUIVALENCE_RULE_v0: ATTESTATION_REFERENCE_ALONE_DOES_NOT_RECORD_APPROVAL_OR_AUTHORIZE_RESTART
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_REMAINING_FIELDS_v0: APPROVAL_DECISION_ID_PLUS_APPROVAL_DECISION_TIMESTAMP_UTC_PLUS_APPROVAL_AUTHORITY_ID
- RL10_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_PATH_v0: formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_v0.md

Captured approval text
> Let this text serve as my approval authorization:
> I approve
>
> Please review the following and execute the prescribed actions:
>
> Under current repo truth, QM-STAT is blocked.
>
> What is established:
>
> * there is now a valid **QM-STAT approval-recordation execution surface**
> * it is correctly in a **ready-but-unrecorded** state
> * a broader workspace search found **no real approval tuple** and **no real attestation document**
> * so nothing lawful can be written into the canonical record yet
>
> What is missing:
>
> * `approval_decision_id`
> * `approval_decision_timestamp_utc`
> * `approval_authority_id`
> * `approval_attestation_reference`
>
> So the branch should remain fail-closed exactly as it is.
>
> The only meaningful next moves are:
>
> * provide the four real approval facts so the record can be written and the QM-STAT governance chain rerun, or
> * leave QM-STAT blocked and shift attention to monitor-only work such as QFT-GR
>
> No repo change is warranted until one of those happens.

Interpretation
- This note now satisfies the repository-local attestation-reference document requirement, but it has not been written onto the declared approval-recordation execution surface.
- Under current repo truth, QM-STAT remains `RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_READY_BUT_UNRECORDED` and the blocker remains `policy_standard_approval_not_recorded`.
- Recordation still requires all four declared fields to be written together; this note only resolves the attestation-reference document itself.

Remaining missing fields before lawful recordation
- `approval_decision_id`
- `approval_decision_timestamp_utc`
- `approval_authority_id`

Prepared tuple format
```json
{
  "approval_decision_id": "<real approval decision id>",
  "approval_decision_timestamp_utc": "<YYYY-MM-DDTHH:MM:SSZ>",
  "approval_authority_id": "<real approval authority id>",
  "approval_attestation_reference": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_ATTESTATION_REFERENCE_v0.md"
}
```

Non-claim boundary
- Repository-local approval attestation witness only; no approval recordation, no restart authorization, and no scientific adequacy claim.