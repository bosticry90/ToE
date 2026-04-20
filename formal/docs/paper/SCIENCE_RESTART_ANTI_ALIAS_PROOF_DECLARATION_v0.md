Science restart anti-alias proof declaration note

Status: ACTIVE_NONLIVE_NONCLAIM
Scope: Repository-local anti-alias proof declaration surface only. No scientific adequacy claim.

Purpose
- Declare one bounded anti-alias proof surface for the next new candidate after higher-level policy revision is authorized.
- Preserve fail-closed restart behavior until anti-alias proof is explicitly declared on this surface.
- Keep anti-alias proof declaration explicitly non-equivalent to direct execution authorization.

Tokens
- SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_ID_v0: SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION
- SCIENCE_RESTART_ANTI_ALIAS_PROOF_SCOPE_v0: ONE_NEXT_NEW_CANDIDATE_ONLY_NO_DIRECT_EXECUTION_AUTHORIZATION
- SCIENCE_RESTART_ANTI_ALIAS_PROOF_REQUIRED_FIELDS_v0: ANTI_ALIAS_PROOF_DECLARATION_ID_PLUS_ANTI_ALIAS_PROOF_SUMMARY_REFERENCE
- SCIENCE_RESTART_ANTI_ALIAS_PROOF_NON_EQUIVALENCE_RULE_v0: ANTI_ALIAS_PROOF_DECLARATION_DOES_NOT_ITSELF_AUTHORIZE_DIRECT_EXECUTION
- SCIENCE_RESTART_ANTI_ALIAS_PROOF_FAIL_CLOSED_RULE_v0: IF_PROOF_IS_NOT_EXPLICITLY_DECLARED_PRE_SCREENING_GATE_REMAINS_CLOSED
- SCIENCE_RESTART_ANTI_ALIAS_PROOF_STATUS_v0: DECLARATION_SURFACE_DEFINED_DEFAULT_UNDECLARED

Interpretation
- This note declares the canonical repository-local surface on which anti-alias proof can later be declared.
- Under current repo truth, the proof remains undeclared and the pre-screening restart gate remains closed.
- Any future proof declaration must remain bounded to one next new candidate and must not itself authorize direct execution.

Prepared declaration shape
```json
{
  "anti_alias_proof_declaration_id": "<proof declaration id>",
  "anti_alias_proof_summary_reference": "<repository-local proof summary reference>"
}
```

Non-claim boundary
- Repository-local anti-alias proof declaration surface only; no scientific adequacy claim.