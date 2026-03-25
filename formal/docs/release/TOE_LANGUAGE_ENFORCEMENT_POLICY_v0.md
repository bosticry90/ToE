# ToE Language Enforcement Policy v0

Spec ID:
- `TOE_LANGUAGE_ENFORCEMENT_POLICY_v0`

Classification:
- `P-POLICY`

Purpose:
- Enforce layer-qualified closure language on canonical status surfaces.
- Prevent overread from governance or route discharge into global-physics completeness claims.

Canonical surfaces in scope:
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `State_of_the_Theory.md`
- `README.md`
- `formal/docs/release/TOE_CLOSURE_SEMANTICS_STANDARD_v0.md`

Required language rules:
- `LANGUAGE_RULE_01_v0: STATUS_SUMMARIES_REQUIRE_LAYER_QUALIFIED_CLOSURE`
- `LANGUAGE_RULE_02_v0: UNQUALIFIED_COMPLETE_CLOSED_DISCHARGED_PROHIBITED_IN_INTERPRETATION_LINES`
- `LANGUAGE_RULE_03_v0: SEAM_GOVERNANCE_COMPLETE_DOES_NOT_IMPLY_SEAM_PHYSICS_COMPLETE`
- `LANGUAGE_RULE_04_v0: TERMINAL_REPO_COMPLETION_TOKENS_ARE_NONCLAIM_SCOPE`

Required qualifier tokens for gate lines:
- `ALLOWED_v0_PHYSICS_CLOSED_UNDER_BOUNDED_DERIVATION_SCOPE`
- `ALLOWED_v0_GOVERNANCE_CLOSED_PER_CANONICAL_POLICY_SCOPE`

Regex controls:
- `FORBIDDEN_BARE_CLOSED_REGEX_v0: (?<![-_])\bCLOSED\b(?![_-](v\d+|UNDER|WITH|PER|BOUNDED|PINNED))`
- `FORBIDDEN_BARE_DISCHARGED_REGEX_v0: (?<![-_])\bDISCHARGED\b(?![_-](v\d+|UNDER|WITH|PER|BOUNDED|PINNED))`
- `FORBIDDEN_BARE_COMPLETE_REGEX_v0: (?<![-_])\bCOMPLETE\b(?![_-](v\d+|UNDER|WITH|PER|BOUNDED|PINNED))`

Enforcement gates:
- `formal/python/tests/test_toe_closure_status_language_ambiguity_guard_gate.py`
- `formal/python/tests/test_toe_seam_status_split_gate.py`
- `formal/python/tests/test_toe_language_enforcement_policy_gate.py`
- `formal/python/tests/test_toe_status_language_lock_guard_gate.py`

Non-claim boundary:
- Policy compliance confirms language hygiene and scope discipline.
- Policy compliance does not promote theorem status, matrix status, or external-truth claims.
