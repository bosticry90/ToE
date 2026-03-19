# TOE GR01 Function-Space Discrete Regularity Evidence v0

Spec ID:
- `TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0`

Classification:
- `T-CONDITIONAL`

Purpose:
- Provide concrete evidence for the already-scoped discrete regularity class used by GR01.
- Discharge the current discrete regularity scope row without claiming continuum Sobolev closure.

Non-claim boundary:
- discrete regularity evidence only.
- no continuum regularity theorem is claimed.
- no Sobolev-space theorem is claimed.
- no uniqueness theorem is claimed.

Evidence tokens:
- `GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM`
- `GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_CLASS_v0: FINITE_DISCRETE_LATTICE_SCALAR_FIELD_CLASS`
- `GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_WITNESS_1D_v0: ScalarField1D`
- `GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_WITNESS_3D_v0: ScalarField3D`
- `GR01_FUNCTION_SPACE_DISCRETE_BOUNDARY_POSTURE_v0: EXPLICIT_PERIODIC_OR_DISCRETE_BOUNDARY_CONVENTIONS`
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_STATUS_v0: EXPLICIT_v0_DISCRETE_SCOPE_NONCLAIM`
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_NAME_v0: PERIODIC_DISCRETE_SUMMATION_BY_PARTS_BOUNDARY_CANCELLATION`
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_HYPOTHESES_v0: FINITE_DISCRETE_LATTICE_PLUS_BOUNDED_NEAREST_NEIGHBOR_DIFFERENCES`
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_CONCLUSION_v0: BOUNDARY_PAIRING_CANCELED_INTERIOR_TERM_RETAINS_BOUNDED_REGULARITY`
- artifact path: `formal/output/gr01_function_space_discrete_regularity_evidence_v0.json`
- gate path: `formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py`

Formal anchors:
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean`
- `formal/toe_formal/ToeFormal/Variational/DiscreteField.lean`

## Local Boundary-Term Regularity Lemma (bounded restart slice)

- carrier and domain:
	finite discrete lattice scalar fields with bounded nearest-neighbor differences are the only admissible inputs.
- boundary contract:
	under `ASM-GR01-BND-01`, the periodic/discrete endpoint pairing cancels exactly in the summation-by-parts step.
- bounded conclusion:
	after cancellation, the interior first-difference pairing remains inside the already-declared bounded discrete regularity class and does not promote any continuum, Sobolev, or uniqueness claim.

Interpretation:
- the theorem-facing carrier in GR01 v0 is discrete, finite, and bounded in the sense required by the current weak-field theorem surface.
- this discharges only the discrete regularity-scope row of the function-space criteria bundle.