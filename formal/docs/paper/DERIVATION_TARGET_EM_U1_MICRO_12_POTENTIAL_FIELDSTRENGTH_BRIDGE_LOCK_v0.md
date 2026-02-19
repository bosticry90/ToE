# Derivation Target: EM U1 Micro-12 Potential/FieldStrength Bridge Lock v0

Spec ID:
- `DERIVATION_TARGET_EM_U1_MICRO_12_POTENTIAL_FIELDSTRENGTH_BRIDGE_LOCK_v0`

Target ID:
- `TARGET-EM-U1-MICRO-12-POTENTIAL-FIELDSTRENGTH-BRIDGE-LOCK-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze the definitional bridge between gauge potential `A` and field strength `F` in forms and tensor notation.
- Keep this cycle planning-only/non-claim and definition-only.
- Pin a typed bridge seam for later Maxwell-route attempts without introducing new physics selections.

Adjudication token:
- `EM_U1_MICRO12_AF_BRIDGE_ADJUDICATION: NOT_YET_DISCHARGED`

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

## TARGET section

- Deliver one bounded potential/field-strength bridge-lock artifact:
  - forms bridge seam: `F := dA`,
  - tensor bridge seam: `F_{μν} := ∂_μ A_ν − ∂_ν A_μ`.
- Deliver one typed bridge harness seam in Lean for later theorem-route attachment.
- Keep Bianchi identity as a pinned seam marker only (no derivation/promotion):
  - `EM_U1_BIANCHI_SURFACE_v0: HOMOG_EQUATION_SEAM_PINNED`.

## ASSUMPTION FREEZE section

- Canonical assumption classes:
  - `MATH|DEF|POLICY|SCOPE`
- Required source assumption ID:
  - `ASM-EM-U1-PHY-SOURCE-01`
- Required convention prerequisite tokens:
  - `EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED`
  - `EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED`
  - `EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE`
- Non-selection policy remains active:
  - `EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION`
  - `EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS`

## CANONICAL_ROUTE section

- Canonical bridge route:
  - pin forms definition seam exactly as a definition:
    - `F := dA`
  - pin tensor definition seam exactly as a definition:
    - `F_{μν} := ∂_μ A_ν − ∂_ν A_μ`
  - pin Bianchi seam marker as a dependency label only:
    - `EM_U1_BIANCHI_SURFACE_v0: HOMOG_EQUATION_SEAM_PINNED`
- This cycle is definition-only:
  - no derivation is asserted,
  - no theorem discharge/promotion is asserted,
  - no dynamics closure is asserted.

## ANTI_SHORTCUT section

- Required anti-shortcut token:
  - `EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED`
- Forbidden shortcuts:
  - promoting bridge definitions as proofs of Maxwell equations,
  - introducing gauge-fixing/units/constitutive selections through bridge wording,
  - importing derivation language into this definition-only cycle.

## COUNTERFACTUAL ROUTE section

- Counterfactual scaffold token:
  - `EM_U1_COUNTERFACTUAL_SCaffold_v0: REQUIRED_ASSUMPTION_REMOVAL_BREAKS_CLOSURE`
- Without a pinned `A↔F` bridge seam, later equation-surface attempts can drift in symbol semantics and notation alignment.

## INDEPENDENT NECESSITY ROUTE section

- Independent-necessity class token:
  - `EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE`
- Cycle-012 remains structural-only and does not alter theorem/discharge status.

## HARDENING section

- Cycle-012 hardening posture:
  - bridge-definition tokens must be synchronized across doc/Lean/target/state/roadmap,
  - `F := dA` and `F_{μν} := ∂_μ A_ν − ∂_ν A_μ` phrases are localized to this cycle artifact,
  - derivation/promotion language is forbidden in this artifact.
- Hardening scaffold token:
  - `EM_U1_HARDENING_SCAFFOLD_v0: ROBUSTNESS_NEGCTRL_TEMPLATES_PINNED`

## BOUNDED_SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- bounded potential/field-strength definition-bridge scope only.
- no derivation claim.
- no theorem/discharge promotion claim.
- no wave-equation claim.
- no Lagrangian claim.
- no constitutive closure claim.
- no unit-system selection claim.
- no gauge-fixing selection claim.
- no non-Abelian completion claim.
- no Standard Model completion claim.
- no external truth claim.

## DRIFT_GATES section

- Cycle-012 progress token:
  - `EM_U1_PROGRESS_CYCLE12_v0: POTENTIAL_FIELDSTRENGTH_BRIDGE_TOKEN_PINNED`
- Forms bridge token:
  - `EM_U1_AF_BRIDGE_FORMS_v0: F_EQUALS_DA_SEAM_PINNED`
- Tensor bridge token:
  - `EM_U1_AF_BRIDGE_TENSOR_v0: F_MUNU_FROM_A_SEAM_PINNED`
- Bianchi seam token:
  - `EM_U1_BIANCHI_SURFACE_v0: HOMOG_EQUATION_SEAM_PINNED`
- Localization gate token:
  - `EM_U1_AF_BRIDGE_LOCALIZATION_GATE_v0: CYCLE12_ARTIFACTS_ONLY`
- No-derivation gate token:
  - `EM_U1_AF_BRIDGE_NO_DERIVATION_v0: DEFINITION_ONLY`

## ADJUDICATION_SYNC section

- Cycle-012 adjudication token:
  - `EM_U1_MICRO12_AF_BRIDGE_ADJUDICATION: NOT_YET_DISCHARGED`
- Canonical gate test pointer:
  - `formal/python/tests/test_em_u1_micro12_potential_fieldstrength_bridge_lock.py`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean`
- `formal/python/tests/test_em_u1_micro12_potential_fieldstrength_bridge_lock.py`
