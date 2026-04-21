# Research Formalization Routing Contract 2026-04-20 v0

Spec ID:
- `RESEARCH_FORMALIZATION_ROUTING_CONTRACT_20260420_v0`

Classification:
- `P-POLICY`

Purpose:
- Add a small machine-readable routing rule that explains whether a research artifact should stay in Python, start in Lean4, mature from Python into Lean4, or explicitly defer formalization.
- Keep formalization routing advisory-only inside research mode.

Required routing tokens:
- `RESEARCH_FORMALIZATION_ROUTING_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM`
- `RESEARCH_FORMALIZATION_ROUTE_SET_v0: PYTHON_FIRST_PLUS_LEAN4_FIRST_PLUS_PYTHON_THEN_LEAN4_PLUS_DEFER_FORMALIZATION`
- `RESEARCH_FORMALIZATION_ASSUMPTION_STABILITY_SET_v0: LOW_PLUS_MEDIUM_PLUS_HIGH`
- `RESEARCH_FORMALIZATION_ARTIFACT_NATURE_SET_v0: NUMERICAL_PLUS_SYMBOLIC_PLUS_STRUCTURAL_PLUS_MIXED`
- `RESEARCH_FORMALIZATION_DEFAULT_RULE_v0: DEFAULT_TO_PYTHON_THEN_LEAN4_UNLESS_NUMERICAL_WITH_NONHIGH_STABILITY_OR_STRUCTURAL_WITH_HIGH_STABILITY_OR_OBJECT_IS_UNDERSPECIFIED`
- `RESEARCH_FORMALIZATION_ADVISORY_ONLY_RULE_v0: ROUTING_IS_ADVISORY_ONLY_AND_DOES_NOT_AUTHORIZE_CANONICAL_MUTATION_OR_GOVERNANCE_TRANSITION`
- `RESEARCH_FORMALIZATION_REQUIRED_METADATA_FIELDS_v0: ASSUMPTION_STABILITY_PLUS_ARTIFACT_NATURE_PLUS_FORMALIZATION_ROUTE_PLUS_ROUTE_JUSTIFICATION_PLUS_LEAN_CANDIDATE_TARGET_PLUS_LEAN_MODULE_TARGET`
- `RESEARCH_FORMALIZATION_GATE_v0: formal/python/tests/test_research_mode_formalization_routing_contract_gate.py`

Routing rules:
- `PYTHON_FIRST`: use when the artifact is numerical, exploratory, fast-changing, or solver-dependent.
- `LEAN4_FIRST`: use only for narrow high-stability structural targets with an explicit Lean module target.
- `PYTHON_THEN_LEAN4`: use when the artifact begins exploratory but success would naturally mature into a theorem or invariant obligation.
- `DEFER_FORMALIZATION`: use when assumptions or notation remain too unstable for honest formalization.

Boundaries:
- This routing contract is advisory-only.
- It does not create a new governance lane.
- It does not force mandatory CI, canonical mutation, or automatic Lean integration.

Canonical bindings:
- `formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md`
- `formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md`
- `formal/python/tests/test_research_mode_formalization_routing_contract_gate.py`

Non-claim boundary:
- This contract defines repository-local routing guidance only.
- This contract does not authorize promotion, canonical mutation, or scientific adequacy claims.