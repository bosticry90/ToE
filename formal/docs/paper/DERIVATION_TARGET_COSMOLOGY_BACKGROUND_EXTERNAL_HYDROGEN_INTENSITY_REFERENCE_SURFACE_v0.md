# Derivation Target: Cosmology Background External Hydrogen Intensity Reference Surface v0

Spec ID:
- `DERIVATION_TARGET_COSMOLOGY_BACKGROUND_EXTERNAL_HYDROGEN_INTENSITY_REFERENCE_SURFACE_v0`

Target ID:
- `TARGET-COSMO-BG-EXTERNAL-HI-REFERENCE-SURFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Capture external hydrogen-intensity summaries as a bounded reference-only surface.
- Keep COSMO background lane synchronized with citation and confidence metadata.

Parent binding:
- `COSMO_EXTERNAL_IMPLICATIONS_PARENT_TARGET_v0: formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- `COSMO_EXTERNAL_IMPLICATIONS_PLAN_POINTER_v0: formal/docs/release/EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0.md`

Adjudication and scope tokens:
- `COSMO_EXTERNAL_IMPLICATIONS_ADJUDICATION_v0: NOT_YET_DISCHARGED_REFERENCE_ONLY`
- `COSMO_EXTERNAL_IMPLICATIONS_SCOPE_BOUNDARY_v0: BACKGROUND_REFERENCE_SURFACE_ONLY`
- `COSMO_EXTERNAL_IMPLICATIONS_LOCALIZATION_GATE_v0: PILOT_DOC_SCOPE_ONLY`
- `COSMO_EXTERNAL_IMPLICATIONS_NO_PROMOTION_v0: NO_RESULTS_TABLE_STATE_ROADMAP_OR_MATRIX_PROMOTION`
- `COSMO_EXTERNAL_IMPLICATIONS_BOUNDARY_v0: NO_CLAIM_OR_INEVITABILITY_PROMOTION`

Confidence/citation contract:
- `COSMO_EXTERNAL_IMPLICATIONS_CONFIDENCE_TIERS_v0: TIER_1_HIGH;TIER_2_MEDIUM;TIER_3_EXPLORATORY`
- `COSMO_EXTERNAL_IMPLICATIONS_CITATION_MINIMUM_v0: SOURCE_URL_OR_DOI_AND_ACCESS_DATE_REQUIRED`

Reference surface schema (pilot):
- `reference_surface_id`
- `observation_summary`
- `claimed_redshift_window`
- `claimed_signal_channel`
- `confidence_tier`
- `citation_url_or_doi`
- `citation_access_date`
- `notes_non_claim`

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote claim labels by itself.
- no comparator-lane authorization.
- no full cosmological model completion claim.
- no external truth claim.

Governance pointers:
- parent COSMO object target: `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md`
- integration plan: `formal/docs/release/EXTERNAL_IMPLICATIONS_INTEGRATION_PLAN_v0.md`
- policy gate: `formal/python/tests/test_cosmo_external_implications_reference_surface_policy_gate.py`
