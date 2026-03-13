# Derivation Target: ToE QFT Scalar Route v0

Spec ID:
- `DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0`

Target ID:
- `TARGET-TOE-QFT-SCALAR-ROUTE-v0`

Classification:
- `P-FOUNDATIONAL`

Purpose:
- Lock a single 12-16 week flagship deliverable: derive a QFT-compatible scalar field sector from the master action with publication-grade reproducibility.
- Bound the target to Klein-Gordon-class structure plus one explicit quantization route.
- Define gates and artifacts for each phase so progress is auditable and replayable.

Primary deliverable:
- Publication-grade derivation showing the master action yields a relativistic scalar field sector compatible with Klein-Gordon-class dynamics, with one clear quantization route and reproducible artifacts.

Starting point:
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`

Comparison object:
- Relativistic scalar QFT (Klein-Gordon class) under declared assumptions and scope limits.

Field content and admissible assumptions:
- Real scalar field `phi(x)` as the primary route.
- Optional complex-scalar extension is deferred unless needed for consistency checks.
- Smoothness, boundary decay/compact support assumptions, and integration-by-parts admissibility are declared explicitly per phase artifact.
- Any approximation regime (weak-field, low-energy, or truncation) must be tagged and justified where used.

Non-claim boundary:
- No Standard Model unification claim.
- No claim of full interacting QFT completion beyond the scalar route.
- No claim of non-perturbative completeness beyond what is explicitly constructed and tested.

Canonical anchors:
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0.md`
- `formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md`
- `formal/output/toe_qft_scalar_field_equations_v0.json`

## Delivery roadmap (12-16 weeks)

Phase 0 (week 1): Charter and scope lock
- artifacts:
  - `formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md`
  - `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0.md`
- gate:
  - `formal/python/tests/test_toe_qft_scalar_route_charter_gate.py`

Phase 1 (weeks 2-4): Classical scalar field sector from the master action
- objective: derive Euler-Lagrange field equations and map them to Klein-Gordon-class structure under declared conditions.
- artifacts:
  - `formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md`
  - `formal/output/toe_qft_scalar_field_equations_v0.json`
- gate:
  - `formal/python/tests/test_toe_qft_scalar_field_equation_gate.py`
- lean surfaces (planned):
  - `ToeFormal.Variational.ScalarFieldFromMasterAction`
  - theorem token: `master_action_scalar_eom_surface`

Phase 2 (weeks 5-7): Relativistic covariance and field interpretation
- objective: verify Lorentz-covariant scalar behavior and canonical stress-energy construction.
- artifacts (planned):
  - `formal/docs/paper/toe_qft_scalar_covariance_report_v0.md`
  - `formal/output/toe_qft_scalar_stress_energy_artifact_v0.json`
- gate (planned):
  - `formal/python/tests/test_toe_qft_scalar_covariance_gate.py`
- lean surface (planned):
  - `ToeFormal.FieldTheory.RelativisticScalarSurface`

Phase 3 (weeks 8-11): Quantization route
- objective: establish one primary quantization route.
- route A (primary default): canonical quantization
  - deliverables include Hamiltonian density, canonical momentum, commutation structure.
  - planned artifact: `formal/docs/paper/toe_qft_scalar_canonical_quantization_report_v0.md`
  - planned gate: `formal/python/tests/test_toe_qft_scalar_quantization_gate.py`
- route B (acceptable alternate): path integral
  - deliverables include generating functional and propagator structure.
  - planned artifact: `formal/docs/paper/toe_qft_scalar_path_integral_report_v0.md`
  - planned gate: `formal/python/tests/test_toe_qft_scalar_path_integral_gate.py`

Phase 4 (weeks 12-14): Compatibility and limits
- objective: connect the scalar route to known limits.
- targets:
  - Klein-Gordon equivalence statement.
  - non-relativistic limit recovering Schrodinger behavior.
- planned artifacts:
  - `formal/docs/paper/toe_qft_scalar_equivalence_statement_v0.md`
  - `formal/output/toe_qft_nonrelativistic_limit_artifact_v0.json`
- planned gate:
  - `formal/python/tests/test_toe_qft_scalar_equivalence_gate.py`

Phase 5 (weeks 15-16): Publication package
- objective: assemble paper-ready derivation and reproducibility package.
- planned artifacts:
  - `formal/docs/paper/TOE_QFT_SCALAR_DERIVATION_MANUSCRIPT_v0.md`
  - `formal/docs/paper/TOE_QFT_SCALAR_EVIDENCE_PACKAGE_v0.md`
- planned final gate:
  - `formal/python/tests/test_toe_qft_publication_package_integrity_gate.py`

## Immediate execution packet (current session)

1. Charter creation and scope lock (this document).
2. Completion criteria freeze.
3. Minimal charter gate enforcing existence and required structure.
4. Phase 1 kickoff: Euler-Lagrange derivation report + symbolic equation artifact.

## Architecture phase coverage (v1)
- `TARGET_DEFINITION`
- `ASSUMPTION_FREEZE`
- `CANONICAL_ROUTE`
- `ANTI_SHORTCUT`
- `COUNTERFACTUAL`
- `INDEPENDENT_NECESSITY`
- `HARDENING`
- `BOUNDED_SCOPE`
- `DRIFT_GATES`
- `ADJUDICATION_SYNC`
