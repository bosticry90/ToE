# ToE GR01 Function-Space Regularity Surface v0

Spec ID:
- `TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0`

Classification:
- `P-POLICY`

Purpose:
- Make the function-space and regularity posture for GR01 explicit as a direct publication-claim attack surface.
- Separate current bounded discrete regularity posture from future continuum/Sobolev closure.

Non-claim boundary:
- theorem-facing surface only.
- no Sobolev-space theorem claim by itself.
- no uniqueness claim by itself.

Regularity posture bundle:
- `GR01_FUNCTION_SPACE_REGULARITY_STATUS_v0: ATTACK_TRACK_ACTIVE_NONCLAIM`
- `GR01_FUNCTION_SPACE_CURRENT_SCOPE_v0: DISCRETE_BOUNDED_FIELD_REGULARITY_ONLY`
- `GR01_FUNCTION_SPACE_NEXT_SCOPE_v0: CONTINUUM_REGULARITY_CLASS_EXPLICITATION_REQUIRED`
- `GR01_FUNCTION_SPACE_SOBELOV_CLAIM_v0: NOT_CLAIMED`
- `GR01_FUNCTION_SPACE_UNIQUENESS_CLAIM_v0: NOT_CLAIMED`
- artifact path: `formal/output/gr01_function_space_regularity_surface_v0.json`
- gate path: `formal/python/tests/test_gr01_publication_theorem_claim_advancement_gate.py`

Local boundary-term regularity lemma bundle:
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_STATUS_v0: EXPLICIT_v0_DISCRETE_SCOPE_NONCLAIM`
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_NAME_v0: PERIODIC_DISCRETE_SUMMATION_BY_PARTS_BOUNDARY_CANCELLATION`
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_HYPOTHESES_v0: FINITE_DISCRETE_LATTICE_PLUS_BOUNDED_NEAREST_NEIGHBOR_DIFFERENCES`
- `GR01_BOUNDARY_TERM_LOCAL_LEMMA_CONCLUSION_v0: BOUNDARY_PAIRING_CANCELED_INTERIOR_TERM_RETAINS_BOUNDED_REGULARITY`
- evidence note path: `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md`
- analytic note path: `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- weak-field note path: `formal/docs/paper/TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md`

Completion criteria bundle:
- `GR01_FUNCTION_SPACE_COMPLETION_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED`
- `GR01_FUNCTION_SPACE_PARTIAL_DISCHARGE_STATUS_v0: ROW_01_AND_ROW_03_DISCHARGED_ROW_02_ROUTE_EXPLICITATED_NONCLAIM`
- `GR01_FUNCTION_SPACE_COMPLETION_CRITERIA_ARTIFACT_v0: gr01_function_space_completion_criteria_cycle10_v0`
- criteria artifact path: `formal/output/gr01_function_space_completion_criteria_cycle10_v0.json`
- `GR01_FUNCTION_SPACE_ROW_01_EVIDENCE_ARTIFACT_v0: gr01_function_space_discrete_regularity_evidence_v0`
- row-01 evidence path: `formal/output/gr01_function_space_discrete_regularity_evidence_v0.json`
- row-01 evidence note path: `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md`
- row-01 evidence gate path: `formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py`
- `GR01_FUNCTION_SPACE_ROW_02_ROUTE_ARTIFACT_v0: gr01_function_space_continuum_regularity_route_v0`
- row-02 route path: `formal/output/gr01_function_space_continuum_regularity_route_v0.json`
- row-02 route note path: `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md`
- row-02 route gate path: `formal/python/tests/test_gr01_function_space_continuum_regularity_route_gate.py`
- `GR01_FUNCTION_SPACE_ROW_03_EVIDENCE_ARTIFACT_v0: gr01_function_space_nonclaim_boundary_evidence_v0`
- row-03 evidence path: `formal/output/gr01_function_space_nonclaim_boundary_evidence_v0.json`
- row-03 evidence note path: `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md`
- row-03 evidence gate path: `formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py`
- criteria gate path: `formal/python/tests/test_gr01_function_space_completion_criteria_gate.py`

Completion criteria rows (cycle-010 pinned):
1. `GR01_FUNCTION_SPACE_CRITERIA_ROW_01_v0: CURRENT_DISCRETE_REGULARITY_SCOPE_DISCHARGED_WITH_CONCRETE_EVIDENCE`
- required anchor token:
	- `GR01_FUNCTION_SPACE_CURRENT_SCOPE_v0: DISCRETE_BOUNDED_FIELD_REGULARITY_ONLY`
- evidence note token:
	- `GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_CLASS_v0: FINITE_DISCRETE_LATTICE_SCALAR_FIELD_CLASS`

2. `GR01_FUNCTION_SPACE_CRITERIA_ROW_02_v0: CONTINUUM_REGULARITY_CLASS_EXPLICITATION_ROUTE_EXPLICITATED_NONCLAIM`
- required anchor token:
	- `GR01_FUNCTION_SPACE_NEXT_SCOPE_v0: CONTINUUM_REGULARITY_CLASS_EXPLICITATION_REQUIRED`
- route token:
	- `GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_STATUS_v0: ROUTE_EXPLICITATED_v0_NONCLAIM`

3. `GR01_FUNCTION_SPACE_CRITERIA_ROW_03_v0: SOBOLEV_AND_UNIQUENESS_NONCLAIM_BOUNDARY_DISCHARGED_WITH_CONCRETE_EVIDENCE`
- required anchor tokens:
	- `GR01_FUNCTION_SPACE_SOBELOV_CLAIM_v0: NOT_CLAIMED`
	- `GR01_FUNCTION_SPACE_UNIQUENESS_CLAIM_v0: NOT_CLAIMED`
- evidence note token:
	- `GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM`

4. `GR01_FUNCTION_SPACE_CRITERIA_ROW_04_v0: STATE_ROADMAP_AND_GATE_SYNC_PINNED`
- required synchronization surfaces:
	- `State_of_the_Theory.md`
	- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
	- `formal/python/tests/test_gr01_function_space_completion_criteria_gate.py`