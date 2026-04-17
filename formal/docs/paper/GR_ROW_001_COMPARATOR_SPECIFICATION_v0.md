# GR Row 001 Comparator Specification v0

Status:
- ACTIVE_NONLIVE_NONCLAIM

Scope:
- bounded non-executing comparator-spec declaration only
- no lane reopen
- no packet authorization
- no blocker-movement claim
- no threshold claim
- no scientific adequacy claim

Comparator-spec packet:
- `GR_ROW_001_COMPARATOR_SPEC_STATUS_v0: DECLARED_NONEXECUTING_COMPARATOR_SPEC`
- `GR_ROW_001_COMPARATOR_SPEC_TARGET_ROW_v0: ROW-PILLAR-GR-001`
- `GR_ROW_001_COMPARATOR_SPEC_INTERFACE_OBJECT_v0: XI_GR_TRANSPORT_ALIGNMENT_INTERFACE`
- `GR_ROW_001_COMPARATOR_SPEC_COMPARATOR_ID_v0: XI_GR_SINGLE_SURFACE_SIGNED_RESIDUAL_COMPARATOR`
- `GR_ROW_001_COMPARATOR_SPEC_INPUT_OBSERVABLE_v0: DELTA_XI_GR_INTERFACE_SIGNED_RESIDUAL`
- `GR_ROW_001_COMPARATOR_SPEC_COMPARISON_SURFACE_v0: SINGLE_SHARED_SCALAR_RESIDUAL_SURFACE`
- `GR_ROW_001_COMPARATOR_SPEC_ORIENTATION_RULE_v0: HOLD_ONE_SIGN_AND_ORDERING_CONVENTION_ACROSS_BOTH_VIEWS`
- `GR_ROW_001_COMPARATOR_SPEC_CLASS_A_v0: SIGN_COHERENT_SHARED_SURFACE`
- `GR_ROW_001_COMPARATOR_SPEC_CLASS_B_v0: SCALE_UNDERDECLARED_BUT_SURFACE_PRESERVED`
- `GR_ROW_001_COMPARATOR_SPEC_CLASS_C_v0: SURFACE_INCOHERENT_FAIL`
- `GR_ROW_001_COMPARATOR_SPEC_FAILURE_RULE_v0: FAIL_IF_MAP_OR_SIGN_CONVENTION_CANNOT_BE_KEPT_SINGLE_VALUED`
- `GR_ROW_001_COMPARATOR_SPEC_EXECUTION_POLICY_v0: NONEXECUTING_SPECIFICATION_ONLY_UNTIL_P75_AND_P77_CLEAR`

Comparator interpretation:
- Start from `Delta_Xi_GR = r_a - M(r_t)` on one bounded surface only.
- Keep one orientation convention fixed across transport-residual and alignment-defect views.
- Use the comparator to classify interpretation shape only, not to declare success, restart, or blocker movement.

Comparator classes:
- `SIGN_COHERENT_SHARED_SURFACE`: both views admit one shared residual with one stable sign or ordering convention on the declared surface.
- `SCALE_UNDERDECLARED_BUT_SURFACE_PRESERVED`: one shared residual and one sign convention exist, but normalization or magnitude interpretation is still underdeclared.
- `SURFACE_INCOHERENT_FAIL`: the declared map or sign convention becomes multivalued, unstable, or requires more than one surface.

Dormancy rule:
- This specification is classificatory only.
- It does not authorize numerical thresholds, packet execution, blocker movement claims, or lane reopen.

Capstone status:
- The concept packet, shared-interface declaration, and comparator specification form the canonical dormant GR design package for ROW-PILLAR-GR-001.
- This comparator specification is the final dormant GR design checkpoint under current dormancy rules.
- Do not add further dormant GR packets unless P75 and P77 clear or a genuinely new distinct ambiguity is identified.

Handoff rule:
- If GR later resumes legitimately, resume from the concept packet, shared-interface declaration, and comparator specification package rather than returning to abstract review layers.
- Treat the current comparator-spec report as the canonical dormant GR design handoff report under present dormancy standards.

Interpretation boundary:
- This package records GR preparation and handoff hardening only.
- It must not be summarized as live GR execution progress, blocker movement, or restart readiness.

Fail-closed rule:
- If the comparator cannot remain single-surface and single-convention, route the GR concept to rework or falsification instead of adding more dormant GR layers.

Non-claim boundary:
- repository-local comparator specification only; no external scientific adequacy claim.