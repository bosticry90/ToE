# TOE QFT Scalar Route Completion Criteria v0

Spec ID:
- `TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0`

Purpose:
- Define auditable completion criteria for the flagship scalar-route deliverable.

Flagship milestone condition:
- The master action yields a scalar field sector equivalent to Klein-Gordon class under explicitly declared assumptions, with one demonstrated quantization route and reproducible artifacts.

Completion criteria:
1. Master-action derivation produces a scalar field equation equivalent to Klein-Gordon class under stated assumptions and scope.
2. A quantization route is demonstrated with explicit intermediate structures.
3. A non-relativistic limit recovers Schrodinger behavior in the stated regime.
4. All route artifacts are reproducible through the repository pipeline.
5. Governance and regression tests pass for all added route gates.

Phase gates and artifact families:
- Phase 0:
  - `formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md`
  - `formal/python/tests/test_toe_qft_scalar_route_charter_gate.py`
- Phase 1:
  - `formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md`
  - `formal/output/toe_qft_scalar_field_equations_v0.json`
  - `formal/python/tests/test_toe_qft_scalar_field_equation_gate.py`
- Phase 2:
  - `formal/docs/paper/toe_qft_scalar_covariance_report_v0.md`
  - `formal/output/toe_qft_scalar_stress_energy_artifact_v0.json`
  - `formal/python/tests/test_toe_qft_scalar_covariance_gate.py`
- Phase 3 (one primary route required):
  - canonical: `formal/docs/paper/toe_qft_scalar_canonical_quantization_report_v0.md`
  - or path-integral: `formal/docs/paper/toe_qft_scalar_path_integral_report_v0.md`
- Phase 3.5:
  - `formal/docs/paper/toe_qft_scalar_propagator_report_v0.md`
  - `formal/output/toe_qft_scalar_two_point_function_artifact_v0.json`
  - `formal/python/tests/test_toe_qft_scalar_propagator_gate.py`
- Phase 4:
  - `formal/docs/paper/toe_qft_scalar_equivalence_statement_v0.md`
  - `formal/output/toe_qft_nonrelativistic_limit_artifact_v0.json`
  - `formal/python/tests/test_toe_qft_scalar_equivalence_gate.py`
- Phase 5:
  - `formal/docs/paper/TOE_QFT_SCALAR_DERIVATION_MANUSCRIPT_v0.md`
  - `formal/docs/paper/TOE_QFT_SCALAR_EVIDENCE_PACKAGE_v0.md`
  - `formal/python/tests/test_toe_qft_publication_package_integrity_gate.py`
- Review-readiness package:
  - `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_REVIEW_READINESS_v0.md`
  - `formal/output/toe_qft_scalar_route_review_readiness_checkpoint_v0.json`
  - `formal/python/tests/test_toe_qft_scalar_route_review_readiness_gate.py`

Alternative planning notes:
- Conservative route: freeze classical scalar derivation first, defer quantization packaging.
- Aggressive route: if scalar sector stabilizes early, prepare a scoped extension lane toward gauge emergence.
