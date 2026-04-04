# WS-10 Implementation Tranche 19 Declaration (2026-04-04)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_19_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_FOUNDATION

## Objective
Start bounded implementation of the information-constraint and operational-position integration plan by pinning one non-claim target surface, one checkpoint artifact, and one focused gate, while wiring first references into canonical action/registry/compendium surfaces.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_19_DECLARATION_20260404_v0.md (new)
- formal/docs/paper/DERIVATION_TARGET_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_INTEGRATION_v0.md (new)
- formal/output/information_constraint_operational_position_integration_v0.json (new)
- formal/python/tests/test_information_constraint_operational_position_integration_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)
- formal/python/tests/test_information_constraint_operational_position_authority_parity_gate.py (new)
- formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md (edit)
- formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md (edit)
- formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md (edit)

## Out of scope
- state-core generated mirrors
- seam completion status flips
- Packet41 hold release, Packet42 hold changes, scalar freeze changes
- any theorem-promotion claim or external-truth claim

## Acceptance
1. formal/python/tests/test_information_constraint_operational_position_integration_gate.py is green.
2. Full formal/python/tests suite is green.
3. ./checkpoint_ladder.ps1 is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
db0377c

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.

## Boundary freshness note
This tranche is the implementation start for the new information-constraint program and is intentionally scoped to statement/route surfaces plus one bounded checkpoint gate.