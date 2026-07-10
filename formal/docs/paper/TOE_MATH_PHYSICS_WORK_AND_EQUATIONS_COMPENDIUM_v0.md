# ToE Math, Physics, and Equations Compendium v0

Spec ID:
- `TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0`

Classification:
- `P-POLICY`

Purpose:
- Provide one centralized, canonical place for active math work, physics work, and equation surfaces.
- Keep equation statements, derivation-route status, and canonical source pointers in one document.
- Reduce context-switching across many per-target files while preserving traceability.

Non-claim boundary:
- This compendium is a consolidation surface, not a theorem promotion surface.
- No new claim is created by inclusion in this document.
- Canonical claim status remains governed by source target docs, checkpoints, and gate files.

## 1) Canonical equation register

| equation_id | domain | equation_surface | status | canonical source |
| --- | --- | --- | --- | --- |
| `EQ-GR01-POISSON-TARGET-v0` | `physics` | `nabla^2 Phi = kappa * rho` | `TARGET_PINNED` | `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md` |
| `EQ-GR01-POISSON-3D-TARGET-v0` | `physics` | `nabla_3D^2 Phi = kappa * rho` | `TARGET_PINNED` | `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md` |
| `EQ-GR01-POISSON1D-PREDICATE-v0` | `math+physics` | `PoissonEquation1D` canonical discrete predicate | `THEOREM_SURFACE_PINNED` | `formal/docs/paper/TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md` |
| `EQ-GR01-POISSON3D-PREDICATE-v0` | `math+physics` | `PoissonEquation3D` canonical discrete predicate | `THEOREM_SURFACE_PINNED` | `formal/docs/paper/TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md` |
| `EQ-EM-U1-INHOM-TENSOR-v0` | `physics` | `d_mu F^{mu nu} = J^nu` | `STATEMENT_LOCK_PINNED` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md` |
| `EQ-EM-U1-HOM-TENSOR-v0` | `physics` | `d_[alpha F_{beta gamma]} = 0` | `STATEMENT_LOCK_PINNED` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md` |
| `EQ-EM-U1-HOM-FORMS-v0` | `physics` | `dF = 0` | `STATEMENT_LOCK_PINNED` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md` |
| `EQ-EM-U1-INHOM-FORMS-v0` | `physics` | `d*F = J` | `STATEMENT_LOCK_PINNED` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md` |
| `EQ-EM-U1-TENSOR-FORMS-MAP-INHOM-v0` | `physics` | `d_mu F^{mu nu} = J^nu <-> d*F = J` | `COMPATIBILITY_MAP_PINNED` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0.md` |
| `EQ-EM-U1-TENSOR-FORMS-MAP-HOM-v0` | `physics` | `d_[alpha F_{beta gamma]} = 0 <-> dF = 0` | `COMPATIBILITY_MAP_PINNED` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0.md` |
| `EQ-QFT-SCALAR-EULER-LAGRANGE-v0` | `math+physics` | `delta S / delta phi = 0` | `ROUTE_ACTIVE_NONCLAIM` | `formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md` |
| `EQ-QFT-SCALAR-KG-CLASS-v0` | `physics` | `(Box + m^2) phi = 0` | `ROUTE_ACTIVE_NONCLAIM` | `formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md` |
| `EQ-QFT-SCALAR-STRESS-ENERGY-v0` | `math+physics` | `T^{mu nu} = partial^mu phi partial^nu phi - eta^{mu nu} [1/2 partial_alpha phi partial^alpha phi + 1/2 m^2 phi^2]` | `ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO` | `formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-MINKOWSKI-v0.json` |
| `EQ-QFT-SCALAR-STRESS-DIVERGENCE-IDENTITY-v0` | `math+physics` | `partial_mu T^{mu nu} = (Box phi - m^2 phi) partial^nu phi` | `ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO` | `formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-MINKOWSKI-v0.json` |
| `EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0` | `math+physics` | `nabla_mu T^{mu nu} = (Box_g phi - V'(phi)) nabla^nu phi` | `ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO` | `formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-CONFORMAL-BACKGROUND-v0.json` |
| `EQ-QM-SCHRODINGER-FORM-v0` | `physics` | `i * d_t psi = H psi` | `CLAIM_SURFACE_TARGET_PINNED` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` |
| `EQ-INFO-OPERATIONAL-POSITION-CONSTRAINT-v0` | `physics+information` | `Position := timing-window + correlation-consistency constraint satisfiability` | `STATEMENT_LOCK_PINNED` | `formal/docs/paper/DERIVATION_TARGET_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_INTEGRATION_v0.md` |
| `EQ-SR-COVARIANCE-STRUCTURE-v0` | `physics` | `Lorentz/Poincare invariance + transformation laws` | `STRUCTURE_SURFACE_PINNED` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` |
| `EQ-STAT-ENTROPY-BALANCE-STRUCTURE-v0` | `physics` | `entropy production/balance structure` | `STRUCTURE_SURFACE_PINNED` | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` |
| `EQ-COSMO-EXPANSION-RELATION-PLACEHOLDER-v0` | `physics` | `COSMO_BG_MICRO02_EXPANSION_RELATION_SURFACE_v0` | `PLACEHOLDER_SURFACE_PINNED_NONCLAIM` | `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0.md` |
| `EQ-COSMO-EOS-PLACEHOLDER-v0` | `physics` | `COSMO_BG_MICRO03_EOS_SURFACE_v0` | `PLACEHOLDER_SURFACE_PINNED_NONCLAIM` | `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_03_SOURCE_COUPLING_SURFACE_v0.md` |

Notes:
- `TARGET_PINNED` means a target equation/structure is explicitly pinned for derivation route control.
- `STATEMENT_LOCK_PINNED` means statement-level equation surfaces are pinned under explicit non-claim boundaries.
- `ROUTE_ACTIVE_NONCLAIM` means active route-level work exists, but theorem-promotion status is not implied by this ledger.
- `PLACEHOLDER_SURFACE_PINNED_NONCLAIM` means typed equation/structure placeholders are pinned for route discipline only.

### Additional scoped evidence

The canonical-source cell and existing scoped status of
`EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0` remain unchanged. Its accepted
fixed-background Level 3 evidence additionally includes:

- `formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_NONZERO_CURVATURE_BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0.json`
- `formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0.json`

These pointers add scoped evidence only; they do not create a new equation surface or
promote gravity evolution, Einstein-source, Bianchi, QFT-GR seam, Level 4/5, CCFT, or
master-action claims.

## 2) Centralized math work map

| work_id | scope | canonical source | checkpoint | gate |
| --- | --- | --- | --- | --- |
| `WORK-MATH-ASSUMPTION-LEDGER-v1` | Assumption semantics and IDs | `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` |
| `WORK-MATH-CLAIM-TAXONOMY-v0` | Claim/non-claim policy semantics | `formal/docs/paper/CLAIM_TAXONOMY_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_toe_closure_and_action_promotion_standards_gate.py` |
| `WORK-MATH-QM-EVOLUTION-CONTRACT-v0` | QM formal theorem surface | `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` | `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md` | `formal/python/tests/test_qm_derivation_chain_gate.py` |
| `WORK-MATH-QM-FULL-DISCHARGE-v0` | QM bounded Schrodinger-form derivation discharge surface | `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_qm_full_derivation_discharge_gate.py` |
| `WORK-MATH-GR-CONSERVATION-CONTRACT-v0` | GR formal conservation contract | `formal/toe_formal/ToeFormal/GR/ConservationContract.lean` | `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md` | `formal/python/tests/test_gr01_conservation_compatibility_promotion_gate.py` |
| `WORK-MATH-GR-CANONICAL-EQUIVALENCE-v0` | GR canonical Poisson-equivalence theorem surface | `formal/docs/paper/TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` |
| `WORK-MATH-PROOF-DEBT-BURNDOWN-c04` | Open proof debt ledger | `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE04_v0.md` | `formal/output/proof_debt_burndown_checkpoint_cycle04_v0.json` | `formal/python/tests/test_toe_complete_v1_terminal_gate.py` |

## 3) Centralized physics work map

| work_id | scope | canonical source | checkpoint | gate |
| --- | --- | --- | --- | --- |
| `WORK-PHYS-ROADMAP-v0` | Route dispatch and pin registry | `formal/docs/paper/PHYSICS_ROADMAP_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` |
| `WORK-PHYS-EM-U1-OBJECT-v0` | EM U1 object route | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_em_u1_maxwell_object_gate.py` |
| `WORK-PHYS-QM-OBJECT-v0` | QM evolution object route | `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md` | `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md` | `formal/python/tests/test_qm_full_derivation_discharge_gate.py` |
| `WORK-PHYS-GR-OBJECT-v0` | GR geometry object route | `formal/docs/paper/DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md` | `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md` | `formal/python/tests/test_gr01_publication_theorem_claim_advancement_gate.py` |
| `WORK-PHYS-SR-COVARIANCE-v0` | SR covariance planning/discharge-criteria route | `formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md` | `formal/output/sr_covariance_discharge_criteria_cycle10_v0.json` | `formal/python/tests/test_sr_m5_theory_parity_link_cycle56_gate.py` |
| `WORK-PHYS-STAT-ENTROPY-v0` | STAT entropy-lane route and scaffold controls | `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md` | `formal/output/stat_m3_completion_promotion_cycle01_v0.json` | `formal/python/tests/test_stat_m3_completion_promotion_cycle01_gate.py` |
| `WORK-PHYS-INFO-CONSTRAINT-INTEGRATION-v0` | information-constraint and operational-position integration route | `formal/docs/paper/DERIVATION_TARGET_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_INTEGRATION_v0.md` | `formal/output/information_constraint_operational_position_integration_v0.json` | `formal/python/tests/test_information_constraint_operational_position_integration_gate.py` |
| `WORK-PHYS-COSMO-BG-v0` | COSMO background expansion/source-coupling scaffold route | `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md` | `formal/output/cosmo_m3_completion_promotion_cycle01_v0.json` | `formal/python/tests/test_cosmo_background_kickoff_gate.py` |
| `WORK-PHYS-QFT-SCALAR-ROUTE-v0` | QFT scalar derivation route | `formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md` | `formal/output/toe_qft_scalar_field_equations_v0.json` | `formal/python/tests/test_toe_qft_scalar_field_equation_gate.py` |
| `WORK-PHYS-QFT-SCALAR-STRESS-DIVERGENCE-MINKOWSKI-v0` | Level 3 flat-limit scalar stress-energy divergence pretest | `formal/docs/release/SCALAR_STRESS_ENERGY_DIVERGENCE_IDENTITY_MINKOWSKI_CALCULATION_RESULT_REVIEW_20260709_v0.json` | `formal/output/CALC-SCALAR-STRESS-ENERGY-DIVERGENCE-IDENTITY-MINKOWSKI-v0.json` | `formal/python/tests/test_scalar_stress_energy_minkowski_result_review.py` |
| `WORK-PHYS-QFT-SCALAR-STRESS-DIVERGENCE-CONFORMAL-CONNECTION-v0` | Level 3 locally-flat nontrivial-connection scalar covariant-divergence test | `formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_CONFORMAL_BACKGROUND_CALCULATION_RESULT_REVIEW_20260709_v0.json` | `formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-CONFORMAL-BACKGROUND-v0.json` | `formal/python/tests/test_scalar_stress_energy_conformal_background_result_review.py` |

## 4) Pillar equation family index

| pillar | primary equation/structure family | primary source | status posture |
| --- | --- | --- | --- |
| `GR` | `nabla^2 Phi = kappa * rho`, `PoissonEquation1D/3D` | `formal/docs/paper/DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md` | `TARGET_PINNED + THEOREM_SURFACE_PINNED` |
| `EM` | Maxwell tensor/forms statements and compatibility map | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md` | `STATEMENT_LOCK_PINNED` |
| `QM` | `i * d_t psi = H psi` Schrodinger-form target | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | `CLAIM_SURFACE_TARGET_PINNED` |
| `QFT` | Euler-Lagrange scalar route, KG-class mapping | `formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md` | `ROUTE_ACTIVE_NONCLAIM` |
| `SR` | Lorentz/Poincare invariance and covariance placeholders | `formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md` | `STRUCTURE_SURFACE_PINNED` |
| `STAT` | entropy production/balance structure | `formal/docs/paper/TOE_CLAIM_SURFACE_v0.md` | `STRUCTURE_SURFACE_PINNED` |
| `COSMO` | expansion-law and EOS placeholder surfaces | `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0.md` | `PLACEHOLDER_SURFACE_PINNED_NONCLAIM` |

## 5) Usage contract

- If you need one place for "what equations/work exist now", use this file first.
- If you need claim status or adjudication strength, follow each row's canonical source + checkpoint + gate.
- If a new equation surface is introduced, add one new row in Section 1 and one work-map row in Section 2 or 3 in the same patch set.

## 6) Compatibility pointer

- Inventory authority surface that points to this compendium:
  - `formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md`
