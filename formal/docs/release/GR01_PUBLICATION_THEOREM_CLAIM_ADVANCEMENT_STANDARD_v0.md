# GR01 Publication Theorem-Claim Advancement Standard v0

Spec ID:
- `GR01_PUBLICATION_THEOREM_CLAIM_ADVANCEMENT_STANDARD_v0`

Classification:
- `P-POLICY`

Purpose:
- Move GR01 beyond bounded publication-package parity into an explicit theorem-claim advancement track.
- Require direct attack surfaces for continuum-limit correspondence and function-space regularity before any stronger publication wording.
- Keep stronger publication claims scoped to theorem-facing advancement, not completed continuum closure.

Non-claim boundary:
- advancement-standard surface only.
- no continuum-limit theorem completion by itself.
- no Sobolev-space uniqueness claim by itself.
- no external-truth claim.

Canonical anchors:
- `formal/docs/release/GR01_PUBLICATION_GRADE_DISCHARGE_PACKAGE_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md`
- `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0.md`
- `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md`
- `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md`
- `formal/docs/paper/TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md`
- `formal/output/gr01_function_space_completion_criteria_cycle10_v0.json`
- `formal/output/gr01_function_space_discrete_regularity_evidence_v0.json`
- `formal/output/gr01_function_space_continuum_regularity_route_v0.json`
- `formal/output/gr01_function_space_nonclaim_boundary_evidence_v0.json`
- `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md`
- `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md`
- `formal/python/tests/test_gr01_publication_theorem_claim_advancement_gate.py`
- `formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py`
- `formal/python/tests/test_gr01_function_space_continuum_regularity_route_gate.py`
- `formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py`
- `formal/python/tests/test_gr01_function_space_completion_criteria_gate.py`

Advancement interpretation:
- stronger theorem-level publication claims are allowed only when continuum-limit and function-space attack tracks are explicit and cross-pinned.
- stronger theorem-level publication claims now require row-level completion criteria to be pinned for both the continuum bridge and function-space regularity surfaces.
- row-wise partial discharge is allowed on the function-space side when a row is backed by explicit discrete regularity-class evidence and remains within non-claim scope.
- row-wise partial discharge is allowed for non-claim boundary rows when explicit evidence is pinned.
- row-wise continuum advancement can be recorded as an explicit regularity-class route without claiming route completion.
- attack-track activation is not theorem completion.
- bounded discrete publication package remains necessary but not sufficient.

Required tokens:
- `GR01_PUBLICATION_THEOREM_CLAIM_ADVANCEMENT_STATUS_v0: ATTACK_TRACK_ACTIVE_NONCLAIM`
- `GR01_PUBLICATION_THEOREM_CLAIM_CONTINUUM_TRACK_v0: DIRECT_ATTACK_REQUIRED`
- `GR01_PUBLICATION_THEOREM_CLAIM_FUNCTION_SPACE_TRACK_v0: DIRECT_ATTACK_REQUIRED`
- `GR01_PUBLICATION_THEOREM_CLAIM_COMPLETION_MODE_v0: CONTINUUM_AND_FUNCTION_SPACE_ROW_LEVEL_CRITERIA_PINNED`
- `GR01_PUBLICATION_THEOREM_CLAIM_CONTINUUM_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED`
- `GR01_PUBLICATION_THEOREM_CLAIM_FUNCTION_SPACE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED`