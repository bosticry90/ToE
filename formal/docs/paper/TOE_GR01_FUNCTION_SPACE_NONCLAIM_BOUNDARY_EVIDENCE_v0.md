# TOE GR01 Function-Space Non-Claim Boundary Evidence v0

Spec ID:
- `TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0`

Classification:
- `T-CONDITIONAL`

Purpose:
- Provide concrete evidence that Sobolev and uniqueness boundaries are explicit non-claims at current GR01 function-space scope.
- Discharge the non-claim boundary row without claiming continuum closure.

Non-claim boundary:
- boundary evidence surface only.
- no Sobolev theorem completion is claimed.
- no uniqueness theorem completion is claimed.
- no continuum PDE closure claim is made.

Evidence tokens:
- `GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM`
- `GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_SOBELOV_v0: NOT_CLAIMED`
- `GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_UNIQUENESS_v0: NOT_CLAIMED`
- `GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_CONTINUUM_COMPLETION_v0: NOT_CLAIMED`
- artifact path: `formal/output/gr01_function_space_nonclaim_boundary_evidence_v0.json`
- gate path: `formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py`

Anchors:
- `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0.md`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/docs/paper/TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md`

Interpretation:
- this evidence discharges the explicit non-claim boundary row only.
- it does not imply continuum regularity completion.