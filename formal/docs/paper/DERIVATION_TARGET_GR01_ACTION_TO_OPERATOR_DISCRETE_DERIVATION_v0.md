# Derivation Target: GR01 Action-to-Operator Discrete Derivation v0

Spec ID:
- `DERIVATION_TARGET_GR01_ACTION_TO_OPERATOR_DISCRETE_DERIVATION_v0`

Target ID:
- `TARGET-GR01-ACTION-TO-OPERATOR-DISCRETE-DERIVATION_v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze post-`TOE-GR-3D-03` bounded/discrete closure posture as baseline.
- Open one upstream micro-target: derive operator-surface obligations from the discrete action/variation route.
- Keep scope inside GR only (no new pillar unlocks, no comparator expansion, no physics-grade calibration expansion).

Non-claim boundary:
- planning-only artifact.
- non-claim control surface.
- does not promote theorem labels by itself.
- no continuum-limit claim.
- no infinite-domain inversion claim.
- no uniqueness claim.

## Baseline Freeze (must remain explicit)

- `TOE-GR-3D-03` remains `T-CONDITIONAL` under bounded/discrete v0 scope.
- closure-package adjudication remains:
  - `ADJUDICATION: SATISFIED_v0_DISCRETE`
- action/RAC alignment remains conditional-publish:
  - `ALIGNMENT_ADJUDICATION: DISCHARGED_CONDITIONAL_PUBLISH_v0`

## Micro-target Scope

Primary question:
- can the discrete action surface and finite-difference variation surface discharge operator-side posture without repackaging assumptions?

Pinned upstream surfaces:
- `formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean`
- `formal/toe_formal/ToeFormal/Variational/ActionToFirstVariationBridgeRep32.lean`

Pinned downstream operator posture:
- `formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DSpherical.lean`
- token: `operator_equation_3d_away_from_source`

## Required Deliverables (all required)

1. Discrete action form is explicit and frozen:
- `actionRep32.action = actionRep32Cubic g`
- `Rep32CubicLaneAssumptions`

2. Finite-difference variation surface is explicit and frozen:
- `formalFirstVariationRep32At e he`
- `ActionRep32FiniteDifferenceRepresentsP e he`
- `ActionVariationBridgeRep32At e he`

3. Bridge assembly route is explicit and auditable:
- `ActionRep32FiniteDifferenceRepresentsEL_of_parts`
- `ActionVariationBridgeRep32At_of_finiteDifferenceRepresentsEL`
- `Rep32_cubic_lane_declared_g`

4. Cross-surface synchronization remains explicit:
- `formal/docs/paper/TOE_GR01_THEOREM_SURFACE_v0.md`
- `formal/docs/paper/TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`

5. Scope lock:
- no SR/EM/QM unlock.
- no comparator-lane expansion.
- no physics-grade calibration expansion while this micro-target is open.

## Cycle-001 Discharge Attempt (2026-02-14)

Attempt artifact:
- `formal/toe_formal/ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean`

Attempt verdict:
- `B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN`

New theorem-surface token:
- `actionRep32_produces_operator_equation_discrete_v0`

Proved pressure-sequence micro-lemmas:
- `actionRep32_variation_bridge_sequence_discrete_v0`
- `actionRep32_el_identification_discrete_v0`

Exact pinned obstruction (single missing bridge lemma):
- `actionRep32_bridge_to_operator_equation_3d_away_from_source_v0`
- shape:
  - `ActionVariationBridgeRep32At e he`
  - plus `EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32`
  - implies 3D away-from-source operator posture:
    `DiscreteLaplacian3D Phi3D p = kappa * rho3D p`

## Cycle-002 Decomposition Attempt (2026-02-14)

Attempt artifact:
- `formal/toe_formal/ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean`

Attempt verdict:
- `B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN`

Decomposition introduced:
- Micro-transport A token (still open):
  - `actionRep32_el_to_residual3d_away_from_source_transport_v0`
  - shape:
    - `EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32`
    - implies away-from-source pointwise residual zero:
      `DiscretePoissonResidual3D Phi3D rho3D kappa p = 0`
- Micro-transport B theorem (proved):
  - `actionRep32_residual3d_away_from_source_implies_operator_equation_discrete_v0`
  - shape:
    - away-from-source pointwise residual zero
    - implies away-from-source operator equation:
      `DiscreteLaplacian3D Phi3D p = kappa * rho3D p`
- Interface reduction theorem (proved):
  - `actionRep32_el_to_residual3d_away_from_source_of_radial_interface_v0`
  - role:
    - reduces Micro-A to a smaller radial interface token under spherical mapping assumptions.

Pinned smaller interface token (open):
- `actionRep32_el_to_radial_residual_transport_interface_v0`
- shape:
  - `EL_toe_rep32 = P_cubic_rep32_def declared_g_rep32`
  - implies radial residual:
    `DiscretePoissonResidualRadial Phir rhor kappa i = 0`

Further decomposition (introduced):
- evaluator-level EL semantics token:
  - `actionRep32_el_to_radial_evaluator_zero_transport_interface_v0`
- evaluator-to-residual matching token:
  - `actionRep32_radial_evaluator_matches_discrete_residual_interface_v0`
- bridge theorem (proved):
  - `actionRep32_el_to_radial_residual_transport_of_evaluator_interfaces_v0`
- interpretation:
  - MICRO-03A1 is now reducible to evaluator-level semantics + evaluator/residual agreement.

Guarded no-repackaging route token:
- `actionRep32_produces_operator_equation_discrete_of_el_to_residual_transport_v0`
- signature intentionally avoids taking direct operator-equation assumptions.

## Cycle-003 Evaluator Concretization Attempt (2026-02-14)

Attempt artifact:
- `formal/toe_formal/ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean`

Attempt verdict:
- `B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN`

Concrete evaluator introduced:
- `evalRadial_rep32_cubic`
  - shape:
    - `evalRadial_rep32_cubic hLaplacianExtraction Phir rhor kappa i`
    - `= hLaplacianExtraction.extractedOperator Phir i - kappa * rhor i`

New theorems:
- `evalRadial_rep32_cubic_matches_discrete_residual_v0`
  - discharges evaluator/residual match for the concrete evaluator under
    `LaplacianExtraction`.
- `actionRep32_el_to_evalRadial_rep32_cubic_zero_of_el_semantics_v0`
  - reduces EL-to-evaluator-zero transport to the existing EL semantics witness
    object:
    `ELImpliesDiscretePoissonResidual ...`.
- `actionRep32_produces_operator_equation_discrete_of_rep32_cubic_evaluator_semantics_v0`
  - guarded end-to-end instantiation via the concrete evaluator and the two
    evaluator interfaces.

## Cycle-004 Bridge Witness Constructor Attempt (2026-02-14)

Attempt artifact:
- `formal/toe_formal/ToeFormal/Variational/GR01ActionToOperatorDiscrete.lean`

Attempt verdict:
- `DISCHARGED_v0_DISCRETE` (bounded/discrete conditional route)

New constructor/route theorems:
- `mk_ELImpliesDiscretePoissonResidual_from_bridge_v0`
  - packages bridge semantics assumptions into the required witness object
    `ELImpliesDiscretePoissonResidual ...`.
- `actionRep32_el_to_evalRadial_rep32_cubic_zero_of_bridge_v0`
  - discharges MICRO-03A2 for the concrete evaluator from bridge semantics
    assumptions.
- `actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_v0`
  - one-call guarded route from action-side assumptions + bridge semantics
    assumptions to 3D away-from-source operator posture.

Interpretation:
- the previously pinned remaining object (`ELImpliesDiscretePoissonResidual ...`)
  now has an explicit constructor route in-module.
- end-to-end action->operator transport is now fully assembled as a theorem
  chain inside the bounded/discrete scope.

## Micro-Lemma Targets (pinned)

1. `TARGET-GR01-A2O-MICRO-01-VARIATION-BRIDGE-SEQUENCE-v0`
- objective token: `actionRep32_variation_bridge_sequence_discrete_v0`
- status: `PROVED` (Cycle-001)

2. `TARGET-GR01-A2O-MICRO-02-EL-IDENTIFICATION-v0`
- objective token: `actionRep32_el_identification_discrete_v0`
- status: `PROVED` (Cycle-001)

3. `TARGET-GR01-A2O-MICRO-03-ACTION-TO-OPERATOR-BRIDGE-v0`
- objective token: `actionRep32_bridge_to_operator_equation_3d_away_from_source_v0`
- status: `PROVED` (Cycle-004, via bridge witness-constructor route)
- role: final action-side bridge needed before adjudication can move to
  `DISCHARGED_v0_DISCRETE`.

4. `TARGET-GR01-A2O-MICRO-03A-EL-TO-RESIDUAL3D-TRANSPORT-v0`
- objective token: `actionRep32_el_to_residual3d_away_from_source_transport_v0`
- status: `PROVED` (Cycle-004, via MICRO-03A2 + MICRO-03A3 + reduction theorem)
- role: pinned missing EL-semantics interface (pointwise 3D residual, away-from-source).

5. `TARGET-GR01-A2O-MICRO-03B-RESIDUAL3D-TO-OPERATOR-v0`
- objective token: `actionRep32_residual3d_away_from_source_implies_operator_equation_discrete_v0`
- status: `PROVED` (Cycle-002)
- role: algebraic transport from residual form to operator-equation form.

6. `TARGET-GR01-A2O-MICRO-03A1-EL-TO-RADIAL-RESIDUAL-INTERFACE-v0`
- objective token: `actionRep32_el_to_radial_residual_transport_interface_v0`
- status: `PROVED` (Cycle-004, instantiated through bridge witness constructor)
- role: radial residual interface token now derived from smaller evaluator-level interfaces.

7. `TARGET-GR01-A2O-MICRO-03A2-EL-TO-RADIAL-EVALUATOR-ZERO-v0`
- objective token: `actionRep32_el_to_radial_evaluator_zero_transport_interface_v0`
- status: `PROVED` (Cycle-004, theorem `actionRep32_el_to_evalRadial_rep32_cubic_zero_of_bridge_v0`)
- role: evaluator-zero transport now discharged for the concrete evaluator under
  explicit bridge semantics assumptions.

8. `TARGET-GR01-A2O-MICRO-03A3-RADIAL-EVALUATOR-MATCHES-RESIDUAL-v0`
- objective token: `actionRep32_radial_evaluator_matches_discrete_residual_interface_v0`
- status: `PROVED` (Cycle-003, concrete evaluator instance)
- role: evaluator meaning obligation discharged for
  `evalRadial_rep32_cubic`.

## Adjudication Token

Allowed values:
- `NOT_YET_DISCHARGED`
- `DISCHARGED_v0_DISCRETE`

Single required token line:
- `ACTION_TO_OPERATOR_ADJUDICATION: <allowed value>`

Current token:
- `ACTION_TO_OPERATOR_ADJUDICATION: DISCHARGED_v0_DISCRETE`

## Enforcement Hooks

- `formal/python/tests/test_physics_roadmap_enforcement.py`
- `formal/python/tests/test_paper_ready_physics_gate.py`
- `formal/python/tests/test_paper_semantic_drift_bans.py`
- `formal/python/tests/test_gr01_action_operator_discharge_gate.py`

## Freeze Policy

- This target does not alter existing theorem labels.
- This target does not change `TOE-GR-3D-03` adjudication status.
- This target does not unlock any non-GR pillar.
