# External Implications Integration Plan v0

Document ID: EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0
Owner: Governance
Status: Active
Last-Updated: 2026-03-06

## Authority Tokens

EXTERNAL_IMPLICATIONS_POLICY_MODE_v0: REFERENCE_ONLY_NON_PROMOTIONAL
EXTERNAL_IMPLICATIONS_NO_PROMOTION_v0: NO_RESULTS_TABLE_OR_ADJUDICATION_PROMOTION
EXTERNAL_IMPLICATIONS_LOCALIZATION_GATE_v0: PILOT_DOC_SCOPE_ONLY
EXTERNAL_IMPLICATIONS_BOUNDARY_v0: NO_STATE_ROADMAP_MATRIX_WRITES
EXTERNAL_IMPLICATIONS_CONFIDENCE_TIERS_v0: TIER_1_HIGH;TIER_2_MEDIUM;TIER_3_EXPLORATORY
EXTERNAL_IMPLICATIONS_CITATION_MINIMUM_v0: SOURCE_URL_OR_DOI_AND_ACCESS_DATE_REQUIRED
EXTERNAL_IMPLICATIONS_PILOT_TARGET_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0.md
EXTERNAL_IMPLICATIONS_PARENT_BINDING_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md
EXTERNAL_IMPLICATIONS_GOVERNANCE_GATE_v0: formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py

## Intake Contract

- External scientific inputs may be captured only as reference surfaces.
- Each captured input must include a confidence tier from `EXTERNAL_IMPLICATIONS_CONFIDENCE_TIERS_v0`.
- Each captured input must include citation metadata satisfying `EXTERNAL_IMPLICATIONS_CITATION_MINIMUM_v0`.
- The pilot lane is bounded to COSMO background reference-only content and does not authorize theorem-body discharge.

## Hard Boundaries

- No updates to `formal/docs/paper/RESULTS_TABLE_v0.md` are authorized by this plan.
- No updates to `State_of_the_Theory.md` are authorized by this plan.
- No updates to `formal/docs/paper/PHYSICS_ROADMAP_v0.md` are authorized by this plan.
- No updates to `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json` are authorized by this plan.
- No claim or inevitability promotion is authorized by this plan.

## Execution Note

- Run `./governance_suite.ps1` after any change to pilot-scope documents listed above.
