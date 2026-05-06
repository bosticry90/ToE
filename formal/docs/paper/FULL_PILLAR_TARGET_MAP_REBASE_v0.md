# Full Pillar Target Map Rebase v0

Spec ID:
- `FULL_PILLAR_TARGET_MAP_REBASE_v0`

Classification:
- `P-POLICY`

Purpose:
- Rebase the ToE project around full mathematical target maps for all admitted pillars and seams.
- Distinguish current local results from full pillar targets.
- Record whether each route is derived, conditional, supplied, residual-only, refuted, retained, or not authorized.
- Preserve non-claim boundaries and master-action citation-bound status.

Non-claim boundary:
- This is a target-map surface only.
- It does not claim full pillar completion.
- It does not begin full-pillar theorem derivation work.
- It does not close seams, authorize Phase 2, claim empirical adequacy, or promote the master action.

Consumed target:
- `prepare_full_pillar_target_map_rebase`

Selected next target:
- `review_full_pillar_target_map_rebase_result`

Lean authority:
- `formal/toe_formal/ToeFormal/Derivation/FullPillarTargetMapRebase.lean`

## Row Schema

Required row fields:

```text
row_id
domain
target_type
current_local_result
full_target
route_source
completion_scale
claim_posture
retained_blocker
semantic_status
next_admissible_action
not_authorized
```

Allowed `route_source` values:

```text
derived
conditional
supplied
residual_only
refuted
retained
not_authorized
```

Allowed `completion_scale` values:

```text
local
pillar
seam
master_action
```

Allowed `claim_posture` values:

```text
T-PROVED
T-CONDITIONAL
E-REPRO
P-POLICY/nonclaim
P-POLICY/planning_only
P-POLICY/speculative
B-BLOCKED/not_authorized
```

Acceptance constraints:
- No row may have a blank `route_source`.
- No local result may use `completion_scale = pillar`.
- Every open pillar row must name the missing full target.
- Every supplied route must name the supplied object.
- The master-action row must remain `MASTER_ACTION_CITATION_BOUND`.

## Target Rows

| row_id | domain | target_type | current_local_result | full_target | route_source | completion_scale | claim_posture | retained_blocker | semantic_status | next_admissible_action | not_authorized |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `FULL_GR_TARGET_MAP_v0` | `GR` | `pillar` | GR01 weak-field / Poisson target under explicit assumptions | Einstein-equation derivation from action variation with stress-energy source, conservation compatibility, boundary terms, and weak-field recovery | `conditional` | `local` | `T-CONDITIONAL` | `gr01_continuum_limit_source_identification_retained` | `LOCAL_DONE_PILLAR_TARGET_OPEN` | `map_full_einstein_equation_derivation_obligations` | `no_full_GR_claim_no_Einstein_equation_derivation_claim_no_strong_gravity_claim` |
| `FULL_QM_TARGET_MAP_v0` | `QM` | `pillar` | QM evolution contract plus supplied evolution-to-transport semantic bridge | State space, observables, Schrodinger evolution, Born/probability semantics, expectation rule, measurement semantics, and classical/statistical limits | `retained` | `local` | `T-CONDITIONAL` | `PHASE1-BLOCKER-QMSTAT-EVOLUTION-TO-TRANSPORT-SEMANTIC-BRIDGE-RETAINED` | `LOCAL_ADVANCED_PILLAR_TARGET_OPEN` | `map_full_qm_probability_measurement_semantics_obligations` | `no_Born_rule_derivation_no_measurement_closure_no_full_QM_pillar_claim` |
| `FULL_EM_TARGET_MAP_v0` | `EM` | `pillar` | Maxwell/U(1) equation surfaces and compatibility maps pinned | Gauge-potential to field-strength construction, gauge invariance, action derivation, source-current semantics, current conservation, and tensor/form compatibility | `retained` | `local` | `P-POLICY/nonclaim` | `PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED` | `LOCAL_ADVANCED_PILLAR_TARGET_OPEN` | `map_full_em_gauge_action_and_source_current_obligations` | `no_nonabelian_claim_no_EM_QFT_closure_no_full_EM_pillar_claim` |
| `FULL_SR_TARGET_MAP_v0` | `SR` | `pillar` | local covariance / transform structure plus SR-COSMO transport package | Lorentz and Poincare structure, invariant interval, velocity addition, and covariance of admitted field laws | `retained` | `local` | `T-CONDITIONAL` | `PHASE1-BLOCKER-SR-COSMO-GLOBAL-BRIDGE-SEMANTIC-MAP-RETAINED` | `LOCAL_ADVANCED_PILLAR_TARGET_OPEN` | `map_full_sr_covariance_and_field_law_obligations` | `no_global_cosmology_bridge_closure_no_full_SR_pillar_promotion` |
| `FULL_SCALAR_QFT_TARGET_MAP_v0` | `SCALAR_QFT` | `pillar` | scalar route advanced retained handoff ready through A1A31 raw-IBP-to-Green conditional package | Complete scalar QFT derivation with scalar action, variation, Klein-Gordon equation, canonical momentum, Hamiltonian, quantization, commutators, mode expansion, vacuum, particles, propagator/two-point package, normalization, and nonrelativistic limit | `retained` | `local` | `T-CONDITIONAL` | `PHASE1-BLOCKER-003A2A15A1A31_RAW_IBP_TO_GREEN_CONVERGENCE_PACKAGE_RETAINED` | `LOCAL_ADVANCED_PILLAR_TARGET_OPEN` | `map_scalar_qft_quantization_and_full_scalar_target_obligations` | `no_interacting_QFT_claim_no_Standard_Model_QFT_claim_no_scalar_only_drilling_without_dependency_graph_change` |
| `FULL_STAT_TARGET_MAP_v0` | `STAT` | `pillar` | entropy/probability scaffold plus supplied QM-STAT transport residuals | Probability/density structure, entropy definition, transport law, equilibrium/nonequilibrium structure, entropy production, microscopic link, irreversibility/coarse-graining, and QM-STAT seam alignment | `supplied` | `local` | `P-POLICY/speculative` | `PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED` | `LOCAL_ADVANCED_PILLAR_TARGET_OPEN` | `map_full_stat_entropy_transport_and_irreversibility_obligations` | `no_statistical_mechanics_derivation_no_irreversibility_closure_no_full_STAT_pillar_claim` |
| `FULL_COSMO_TARGET_MAP_v0` | `COSMO` | `pillar` | COSMO expansion and equation-of-state placeholder target surface | Friedmann-like equations, equation-of-state structure, local-to-global bridge, expansion observables, curvature/topology assumptions, and dark-sector assumptions | `not_authorized` | `local` | `P-POLICY/planning_only` | `cosmo_background_reduction_and_expansion_observable_retained` | `PLACEHOLDER_SURFACE_PINNED_PILLAR_TARGET_OPEN` | `map_friedmann_equation_and_local_global_cosmology_obligations` | `no_Friedmann_derivation_no_cosmology_pillar_closure_no_dark_sector_claim` |
| `FULL_SEAM_QFT_GR_TARGET_MAP_v0` | `QFT_GR` | `seam` | supplied operator-domain semantics construct stress-energy object; package-only derivation refuted | QFT stress-energy operator domain, state expectation functional, renormalized expectation, weak-curvature source identification, covariance/conservation, and full source-map semantic closure | `supplied` | `seam` | `T-CONDITIONAL` | `PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-OPERATOR-DOMAIN-SEMANTICS-RETAINED` | `SUPPLIED_SEMANTIC_ASSUMPTION_RETAINED` | `prepare_full_pillar_target_map_rebase` | `no_QFT_GR_seam_closure_no_semiclassical_gravity_claim_no_Einstein_equation_derivation_claim` |
| `FULL_SEAM_QM_STAT_TARGET_MAP_v0` | `QM_STAT` | `seam` | finite transport residual package works under supplied transport; contract-only probability extraction refuted | source probability extraction, target entropy semantics, transport-map semantics, observable transport, coarse-graining/irreversibility, and residual-package semantic closure | `supplied` | `seam` | `T-CONDITIONAL` | `PHASE1-BLOCKER-QMSTAT-SOURCE-PROBABILITY-EXTRACTION-SEMANTICS-RETAINED` | `SUPPLIED_SEMANTIC_ASSUMPTION_RETAINED` | `map_qm_stat_full_probability_entropy_transport_obligations` | `no_QM_STAT_seam_closure_no_statistical_mechanics_derivation_claim` |
| `FULL_SEAM_EM_QFT_TARGET_MAP_v0` | `EM_QFT` | `seam` | shared-dynamics and interface-alignment supplied routes exist; governance/zero-residual/interface-only closure routes refuted | shared dynamics, residual unification semantics, source-current semantics, gauge/quantization semantics, and EM-QFT bridge closure | `supplied` | `seam` | `T-CONDITIONAL` | `PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED` | `SEAM_TARGET_OPEN` | `map_em_qft_shared_dynamics_source_current_and_gauge_quantization_obligations` | `no_EM_QFT_seam_closure_no_source_current_bridge_slice_no_gauge_quantization_bridge_slice` |
| `FULL_SEAM_SR_COSMO_TARGET_MAP_v0` | `SR_COSMO` | `seam` | local SR covariance through cosmology regime transport residual package; global semantic-map closure refuted | local SR covariance, cosmology background/regime alignment, global semantic map, local-to-global transport, and expansion observable semantics | `residual_only` | `seam` | `T-CONDITIONAL` | `PHASE1-BLOCKER-SR-COSMO-GLOBAL-BRIDGE-SEMANTIC-MAP-RETAINED` | `RESIDUAL_ONLY_SEMANTIC_OPEN` | `map_sr_cosmo_global_bridge_semantic_obligations` | `no_global_SR_COSMO_bridge_closure_no_cosmology_pillar_closure` |
| `FULL_SEAM_GR_QM_TARGET_MAP_v0` | `GR_QM` | `seam` | GR-QM scoped seam package with legacy transition boundary | bounded GR-QM bridge classification distinct from QFT-GR source-map semantics and full quantum gravity | `conditional` | `seam` | `P-POLICY/nonclaim` | `gr_qm_master_action_citation_scope_boundary_retained` | `BOUNDED_SEAM_DONE` | `map_gr_qm_scope_boundary_against_full_quantum_gravity_target` | `no_quantum_gravity_claim_no_QFT_GR_source_map_closure_claim` |
| `MASTER_ACTION_FULL_DEPENDENCY_MAP_v0` | `MASTER_ACTION` | `master_action` | candidate master action remains citation-bound and non-promoted | Every term mapped to pillar or seam function with derived/supplied/speculative/placeholder status and dependency gaps listed | `not_authorized` | `master_action` | `P-POLICY/nonclaim` | `master_action_dependency_frontier_retained_no_promotion` | `MASTER_ACTION_CITATION_BOUND` | `retain_master_action_as_dependency_map_during_target_rebase` | `MASTER_ACTION_CITATION_BOUND_no_canonical_promotion_no_Phase2_no_empirical_claim_no_global_seam_closure` |

## Full Target Sections

### FULL_GR_TARGET_MAP_v0

Current local result: weak-field / Poisson target.

Full target: Einstein-equation derivation from action variation, stress-energy source definition, conservation compatibility, boundary terms, assumptions, and weak-field recovery.

Status: `LOCAL_DONE_PILLAR_TARGET_OPEN`.

### FULL_QM_TARGET_MAP_v0

Current local result: evolution-contract advanced.

Full target: state space, observables, Schrodinger evolution, Born/probability semantics, expectation values, measurement semantics, and classical/statistical limits.

Status: `LOCAL_ADVANCED_PILLAR_TARGET_OPEN`.

### FULL_EM_TARGET_MAP_v0

Current local result: Maxwell/U(1) equation surfaces pinned.

Full target: gauge-potential construction, field strength, gauge invariance, action derivation, source-current semantics, current conservation, and tensor/form compatibility.

Status: `LOCAL_ADVANCED_PILLAR_TARGET_OPEN`.

### FULL_SR_TARGET_MAP_v0

Current local result: local covariance and transformation structure.

Full target: Lorentz/Poincare structure, invariant interval, velocity addition, and covariance of admitted laws.

Status: `LOCAL_ADVANCED_PILLAR_TARGET_OPEN`.

### FULL_SCALAR_QFT_TARGET_MAP_v0

Current local result: scalar route advanced retained handoff ready.

Full target: scalar QFT derivation through action, variation, Klein-Gordon equation, canonical momentum, Hamiltonian, quantization, commutators, mode expansion, vacuum, particles, propagator/two-point structure, normalization, and nonrelativistic limit.

Status: `LOCAL_ADVANCED_PILLAR_TARGET_OPEN`; interacting / Standard Model QFT remains out of current scope.

### FULL_STAT_TARGET_MAP_v0

Current local result: entropy/probability scaffold plus supplied QM-STAT transport residuals.

Full target: probability/density structure, entropy definition, transport law, equilibrium/nonequilibrium structure, entropy production, microscopic link, irreversibility/coarse-graining, and QM-STAT seam alignment.

Status: `LOCAL_ADVANCED_PILLAR_TARGET_OPEN`.

### FULL_COSMO_TARGET_MAP_v0

Current local result: placeholder target surface.

Full target: Friedmann-like equations, equation-of-state structure, local-to-global bridge, observables, and curvature/topology/dark-sector assumptions.

Status: `PLACEHOLDER_SURFACE_PINNED_PILLAR_TARGET_OPEN`.

### FULL_SEAM_COMPLETION_MAP_v0

The seam rows ask five questions:

```text
Do the objects fit?
Is the bridge legal?
Does transport preserve the obligation?
Does the regime limit stay valid?
Is the meaning derived or supplied?
```

Current seam target statuses:
- `QFT_GR`: supplied operator-domain route retained; full source-map semantics open.
- `QM_STAT`: supplied source-probability and transport structures retained; target entropy, transport-map, and irreversibility semantics open.
- `EM_QFT`: supplied shared-dynamics and interface routes exist; source-current and gauge/quantization semantics open.
- `SR_COSMO`: local zero-residual transport exists; global semantic map open.
- `GR_QM`: bounded scope recorded; full quantum gravity is not claimed.

### MASTER_ACTION_FULL_DEPENDENCY_MAP_v0

The master action remains:

```text
MASTER_ACTION_CITATION_BOUND
```

It is a dependency map and candidate surface only. It is not canonical, not promoted, not externally true by itself, and not a theorem-promotion surface.
