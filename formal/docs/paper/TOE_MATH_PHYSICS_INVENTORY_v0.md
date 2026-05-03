# ToE Math and Physics Inventory v0

Spec ID:
- `TOE_MATH_PHYSICS_INVENTORY_v0`

Classification:
- `P-POLICY`

Purpose:
- Provide one canonical, current-state inventory for math objects, physics objects, and major claim surfaces.
- Distinguish defined, used, validated, bounded/non-claim, and open/proof-debt states.
- Point to canonical source, checkpoint, and gate surfaces without duplicating detailed derivation content.
- Pin one centralized work-and-equations compendium surface for direct math/physics equation lookup.

Non-claim boundary:
- inventory/control artifact only.
- no theorem promotion by itself.
- no adjudication upgrade by itself.
- no external truth claim.

## 1) Scope and semantics

This inventory is:
- a current-state ledger for canonical surfaces used to answer "what do we have now".
- a crosswalk across document, artifact, and gate surfaces.
- a dependency-aware status map for active/open decision-relevant rows.

This inventory is not:
- a full historical changelog.
- a replacement for derivation target documents.
- a substitute for release notes, policy standards, or artifact payloads.

Status semantics:
- `DEFINED`: canonical object/surface exists with pinned definition source.
- `USED`: object/surface is consumed by one or more active canonical routes.
- `VALIDATED`: object/surface has checkpoint and gate evidence in canonical surfaces.
- `BOUNDED_NONCLAIM`: object/surface is intentionally policy-bounded and not promoted to stronger claim class.
- `OPEN_PROOF_DEBT`: object/surface has unresolved proof, seam, empirical, or packaging debt.

Decision relevance semantics:
- `CURRENT`: directly affects current admissible actions and status decisions.
- `BACKGROUND`: active support context, not a near-term decision switch.
- `ARCHIVAL_SHADOW`: retained only for traceability, no direct current decision role.

Row schema:
- `inventory_id`
- `domain` (`math` or `physics`)
- `category`
- `name`
- `decision_relevance`
- `canonical_source`
- `checkpoint_source`
- `gate_source`
- `status`
- `claim_level`
- `dependencies`
- `notes`

## 2) Mathematical inventory

| inventory_id | domain | category | name | decision_relevance | canonical_source | checkpoint_source | gate_source | status | claim_level | dependencies | notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `INV-MATH-ASSUMPTION-REGISTRY-v1` | `math` | `assumptions` | Assumption registry ledger | `CURRENT` | `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` | `VALIDATED` | `P-POLICY` | `INV-MATH-CLAIM-TAXONOMY-v0` | Canonical assumption ID ledger used across theorem surfaces. |
| `INV-MATH-CLAIM-TAXONOMY-v0` | `math` | `claim_semantics` | Claim taxonomy semantics | `CURRENT` | `formal/docs/paper/CLAIM_TAXONOMY_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_toe_closure_and_action_promotion_standards_gate.py` | `VALIDATED` | `P-POLICY` | `none` | Canonical claim/non-claim labels used by this inventory. |
| `INV-MATH-DERIV-COMPLETENESS-GATE-v0` | `math` | `theorem_surfaces` | Derivation completeness gate policy | `CURRENT` | `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md` | `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json` | `formal/python/tests/test_pillar_deep_maturity_program_gate.py` | `USED` | `P-POLICY` | `INV-MATH-ASSUMPTION-REGISTRY-v1` | Publication-grade sufficiency constraints. |
| `INV-MATH-PILLAR-STATUS-MATRIX-v1` | `math` | `invariants` | Pillar status matrix | `CURRENT` | `formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_pillar_phase_advancement_gate.py` | `VALIDATED` | `P-POLICY` | `none` | Matrix-closure state surface under bounded semantics. |
| `INV-MATH-PROOF-DEBT-BURNDOWN-c04` | `math` | `proof_debt` | Proof debt burndown checkpoint c04 | `CURRENT` | `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE04_v0.md` | `formal/output/proof_debt_burndown_checkpoint_cycle04_v0.json` | `formal/python/tests/test_toe_complete_v1_terminal_gate.py` | `OPEN_PROOF_DEBT` | `P-POLICY` | `INV-MATH-ASSUMPTION-REGISTRY-v1` | GapID-based proof debt traceability surface. |
| `INV-MATH-QM-EVOLUTION-CONTRACT` | `math` | `theorem_surfaces` | QM evolution contract theorem surface | `BACKGROUND` | `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` | `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md` | `formal/python/tests/test_qm_derivation_chain_gate.py` | `USED` | `T-CONDITIONAL` | `INV-MATH-ASSUMPTION-REGISTRY-v1` | Canonical typed theorem surface consumed by QM routes. |
| `INV-MATH-GR-CONSERVATION-CONTRACT` | `math` | `theorem_surfaces` | GR conservation compatibility theorem surface | `BACKGROUND` | `formal/toe_formal/ToeFormal/GR/ConservationContract.lean` | `formal/docs/paper/TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md` | `formal/python/tests/test_gr01_conservation_compatibility_promotion_gate.py` | `USED` | `T-CONDITIONAL` | `INV-MATH-ASSUMPTION-REGISTRY-v1` | Bridge-compatible conservation theorem surface. |
| `INV-MATH-SEAM-WITNESS-PACKAGE` | `math` | `witnesses` | Seam witness package schema | `CURRENT` | `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean` | `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md` | `formal/python/tests/test_toe_master_action_class_b_inventory_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | Required witness route surface for seam promotions. |
| `INV-MATH-PHYS-WORK-EQ-COMPENDIUM-v0` | `math` | `synthesis_surface` | Centralized math/physics work and equations compendium | `CURRENT` | `formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` | `USED` | `P-POLICY` | `INV-MATH-CLAIM-TAXONOMY-v0` | Single lookup surface for active equation statements and route-level work pointers. |
| `INV-MATH-LEAN-QFT-SCALAR-AGGREGATE-v0` | `math` | `theorem_surfaces` | Lean aggregate for current strict scalar/QFT, cross-pillar, QM-STAT, QFT-GR, SR/COSMO, QM evolution, EM-QFT, and master-action citation surfaces | `CURRENT` | `formal/toe_formal/ToeFormal.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-PHYS-STRICT-DERIVATION-OBLIGATION-MAP-v0` | Aggregate import surface now includes the current scalar/QFT analytic blocker split, A2A15 boundary-flux subblocker split, A2A15A finite raw-IBP theorem model, A2A15A1 analytic interval lift contract, A2A15A1A graph-Laplacian convergence channel split, A2A15A1B endpoint-flux convergence channel split, A2A15A1C raw-IBP/Green-identity convergence channel split, A2A15A1 channel assembly capstone and anti-loop readout, A2A15A1A quadratic-stencil consistency proof plus obstruction readout, A2A15A1A stencil-remainder error readout, A2A15A1A2 Taylor/remainder-control retained bridge, A2A15A1A3 fourth-derivative-bound retained bridge, A2A15A1A4 degree <= 3 polynomial certificate, A2A15A1A5 bounded degree-four polynomial remainder certificate, A2A15A1A polynomial test-class capstone, A2A15A1A6 general smooth Taylor/refinement retained surface, A2A15A1A graph-Laplacian channel capstone, A2A15A1A7 concrete Taylor remainder slice, A2A15A1A7 symmetric Taylor-to-stencil bridge, A2A15A1A8 mathlib endpoint Taylor alignment, A2A15A1A9 endpoint package derivation from mathlib with scalar coefficient formula, reflected-left expansion/bound route, centered-alignment from the global smoothness/nondegenerate mathlib route proved, two-sided endpoint package construction feeding the local stencil-bound route, A2A15A1A10 uniform mesh convergence contract/wiring, A2A15A1A11 uniform mesh evidence conditional theorem, A2A15A1A12 order-`h^2` mesh-limit bridge, A2A15A1A13 concrete mesh/zero-error instantiation, A2A15A1A14 nonzero stencil-error normal-form bound, A2A15A1A15 endpoint-package stencil-error uniform-bound bridge, A2A15A1A16 actual graph stencil-error identification, A1A graph-channel semantic closure review with conditional parent-field bridge, A2A15A1A17 parent graph-channel interface-map review retained by semantic-map-free counterexample, A2A15A1A18 restricted parent graph-channel interface with restricted-to-arbitrary bridge retained, A2A15A1A19 parent-interface equivalence bridge retained, A2A15A1A20 parent-interface abstraction review retained, A2A15A1A21 parent graph-channel interface refactor retained, A2A15A1A22 specialized A2A15A1 witness attempt retained, A2A15A1A23 specialized endpoint-flux evidence connector retained, A2A15A1A24 endpoint-flux evidence derivation attempt retained, A2A15A1A25 endpoint-source obligation split retained, A2A15A1A26 endpoint representation/semantics obligation retained, A2A15A1A27 endpoint convergence/consistency obligation retained, A2A15A1A28 endpoint orientation/trace compatibility retained, A2A15A1A29 refined endpoint-source assembly with remaining non-endpoint obligations retained, A2A15A1A30 remaining non-endpoint obligation split retained, A2A15A1A31 raw-IBP-to-Green convergence conditional bridge retained, scalar/QFT handoff capstone with status `SCALAR_QFT_ADVANCED_RETAINED_HANDOFF_READY`, cross-pillar derivation protocol, all-pillar frontier map, master-action dependency frontier, historical post-sweep theorem queue, QM-STAT post-budget cross-pillar review, QFT-GR post-budget cross-pillar review, free-scalar witness, finite QM-STAT transport, QM-STAT transport residual package, QM evolution-to-QM-STAT transport-hypotheses adjudication, QM evolution-to-transport semantic bridge theorem, QM evolution post-budget cross-pillar review, QFT-GR stress-energy expectation source-map, QFT-GR residual-only semantic obstruction, SR/COSMO regime transport, SR/COSMO global-bridge semantic-map obstruction, SR/COSMO post-budget cross-pillar review, EM-QFT physics-blocker protocol, EM-QFT shared-dynamics residual-unification bridge, EM-QFT interface-alignment semantic bridge, EM-QFT post-budget review, master-action retained-assumption citation usage, master-action citation-language audit, master-action dependency-graph review, master-action retained-blocker prioritization review, QM-STAT transport semantics retained-blocker protocol row, QM-STAT transport semantics protocol-row readiness review, QM-STAT source-probability extraction semantics, QM-STAT source-probability result review, post-QM-STAT retained-blocker prioritization review, QFT-GR source-map semantics retained-blocker protocol row, and QFT-GR source-map semantics protocol-row readiness review modules. Focused Lean checks are green for the QFT-GR readiness review and direct frontier dependencies; no full aggregate build is claimed for this tranche. |
| `INV-MATH-CROSS-PILLAR-DERIVATION-PROTOCOL-v0` | `math` | `methodology_surfaces` | Cross-pillar derivation protocol | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/CrossPillarDerivationProtocol.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-LEAN-QFT-SCALAR-AGGREGATE-v0` | Standardizes the scalar-extracted pattern `target -> evidence package -> conditional bridge -> obstruction/counterexample -> retained blocker -> next strict target` with statuses `proved`, `conditional`, `retained`, `refuted`, and `not_authorized`; it supplies no Phase 2 or master-action promotion. |
| `INV-MATH-CROSS-PILLAR-CLOSURE-FRONTIER-v0` | `math` | `synthesis_surface` | All-pillar closure frontier map | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/CrossPillarClosureFrontier.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-CROSS-PILLAR-DERIVATION-PROTOCOL-v0` | Records Scalar/QFT, QM evolution, QM-STAT, SR covariance, GR01, Cosmology, QFT-GR seam, GR-QM seam, EM-QFT seam, and master-action rows with strongest surface, retained blocker, proof-debt scope, dependency class, and next strict slice; it supplies no seam promotion or master-action promotion. |
| `INV-MATH-MASTER-ACTION-DEPENDENCY-FRONTIER-v0` | `math` | `synthesis_surface` | Master-action dependency frontier | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/MasterActionDependencyFrontier.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-CROSS-PILLAR-CLOSURE-FRONTIER-v0` | Classifies citation-boundary dependencies as `required_for_coherence`, `required_for_closure`, `publication_grade_only`, or `local_proof_debt`; retained assumptions may be cited only under non-promotion wording. |
| `INV-MATH-POST-SWEEP-THEOREM-QUEUE-v0` | `math` | `work_queue` | Historical first post-sweep theorem queue | `CURRENT_TRACEABILITY` | `formal/toe_formal/ToeFormal/Derivation/PostSweepTheoremQueue.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-MASTER-ACTION-DEPENDENCY-FRONTIER-v0` | Historical first-wave queue marked `HISTORICAL_NONLIVE_FIRST_WAVE_QUEUE_v0`; it preserves the original QM-STAT, QFT-GR, and scalar slice ordering for traceability but cannot supply or override the live next target. |
| `INV-MATH-QMSTAT-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `math` | `work_queue` | QM-STAT post-budget cross-pillar review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QMSTATPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-POST-SWEEP-THEOREM-QUEUE-v0` | Executes the loop-control attempt-budget review after the QM-STAT component residual evidence slice; same-lane QM-STAT continuation and scalar reopening are not authorized, the master-action citation scope is refreshed without promotion, and QFT-GR stress-energy source-map work is selected as the next strict slice. |
| `INV-MATH-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-v0` | `math` | `theorem_surfaces` | QM-STAT unified transport residual package | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_TransportResidualPackage.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-POST-SWEEP-THEOREM-QUEUE-v0` | Defines the source QM evolution, target STAT/entropy, transport-map, preserved-quantity, residual/error package, and component residual evidence; finite equivalence transport builds a zero-residual package plus componentwise entropy/mean/second-moment/variance/unified residual-zero evidence under supplied alignment data, while full QM-STAT seam semantics remain retained as `PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED`. |
| `INV-MATH-QMSTAT-EVOLUTION-TRANSPORT-HYPOTHESES-ADJUDICATION-v0` | `math` | `theorem_surfaces` | QM evolution transport-hypotheses adjudication | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_EvolutionTransportHypothesesAdjudication.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-v0` | Proves contract-only QM evolution does not derive the finite transport equivalence, probability-source alignment, STAT target, observable alignment, or transport semantics required by the QM-STAT residual package; records `PHASE1-BLOCKER-QMSTAT-EVOLUTION-MAP-TO-TRANSPORT-HYPOTHESES-RETAINED`, while a supplied semantic bridge still constructs the residual package route and no seam/promotion claim is made. |
| `INV-MATH-QMSTAT-EVOLUTION-TRANSPORT-SEMANTIC-BRIDGE-v0` | `math` | `theorem_surfaces` | QM evolution transport semantic bridge theorem | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_EvolutionTransportSemanticBridge.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QMSTAT-EVOLUTION-TRANSPORT-HYPOTHESES-ADJUDICATION-v0` | Names the finite state transport, probability extraction/alignment, STAT target, observable extraction/transport, and transport-semantics obligations; proves supplied bridge data constructs the finite QM-STAT transport hypotheses, residual package, and component evidence while retaining `PHASE1-BLOCKER-QMSTAT-EVOLUTION-TO-TRANSPORT-SEMANTIC-BRIDGE-RETAINED`. |
| `INV-MATH-QM-EVOLUTION-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `math` | `work_queue` | QM evolution post-budget cross-pillar review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QMEvolutionPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QMSTAT-EVOLUTION-TRANSPORT-SEMANTIC-BRIDGE-v0` | Executes the loop-control attempt-budget review after the supplied semantic bridge theorem; same-lane QM evolution continuation and scalar/QM-STAT/QFT-GR/SR-COSMO reopenings are not authorized, stronger-QM-dynamics derivation is not supplied, and EM-QFT physics-blocker extraction is selected. |
| `INV-MATH-EM-QFT-PHYSICS-BLOCKER-PROTOCOL-ROW-v0` | `math` | `work_queue` | EM-QFT physics-blocker protocol row | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/EMQFTPhysicsBlockerProtocolRow.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QM-EVOLUTION-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | Consumes `extract_em_qft_physics_blocker_into_protocol_row`, records EM-QFT governance complete / physics incomplete, classifies the shared-dynamics plus residual-unification blocker and interface-alignment semantic bridge obligation, and selects `derive_or_refute_em_qft_shared_dynamics_residual_unification_bridge` as the next bounded target without seam or master-action promotion. |
| `INV-MATH-EM-QFT-SHARED-DYNAMICS-RESIDUAL-UNIFICATION-BRIDGE-v0` | `math` | `theorem_surfaces` | EM-QFT shared-dynamics residual-unification bridge adjudication | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SharedDynamicsResidualUnificationBridge.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-EM-QFT-PHYSICS-BLOCKER-PROTOCOL-ROW-v0` | Proves supplied EM/shared and QFT/shared current alignments plus supplied residual-unification semantics construct a bounded zero-residual package, while zero-residual-only and governance-witness-only routes do not force full EM-QFT bridge semantics; selects `derive_or_refute_em_qft_interface_alignment_semantic_bridge` as the next bounded target without seam or master-action promotion. |
| `INV-MATH-EM-QFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-v0` | `math` | `theorem_surfaces` | EM-QFT interface-alignment semantic bridge adjudication | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/EM_QFT_InterfaceAlignmentSemanticBridge.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-EM-QFT-SHARED-DYNAMICS-RESIDUAL-UNIFICATION-BRIDGE-v0` | Proves supplied EM/QFT interface alignment constructs a bounded interface package, while interface-alignment-only routes do not force source-current semantics or gauge/quantization semantics; selects `em_qft_post_budget_cross_pillar_review` after the second retained EM-QFT slice without seam or master-action promotion. |
| `INV-MATH-EM-QFT-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `math` | `work_queue` | EM-QFT post-budget cross-pillar review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/EMQFTPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-EM-QFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-v0` | Completes the two-slice EM-QFT attempt-budget review, blocks third same-lane source-current or gauge/quantization drilling here, keeps EM-QFT required-for-coherence retained, and selects citation-only `cite_only_bounded_retained_assumptions` without seam or master-action promotion. |
| `INV-MATH-MASTER-ACTION-RETAINED-ASSUMPTION-CITATION-USAGE-v0` | `math` | `synthesis_surface` | Master-action retained-assumption citation usage | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/MasterActionRetainedAssumptionCitationUsage.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-EM-QFT-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | Consumes `cite_only_bounded_retained_assumptions`, reuses the existing master-action citation-boundary list, carries every forbidden-promotion scope forward, leaves dependency classes unchanged, and selects `audit_master_action_citation_language_against_retained_boundaries` without seam closure, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-MASTER-ACTION-CITATION-LANGUAGE-AUDIT-v0` | `math` | `synthesis_surface` | Master-action citation-language audit | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/MasterActionCitationLanguageAudit.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-MASTER-ACTION-RETAINED-ASSUMPTION-CITATION-USAGE-v0` | Consumes `audit_master_action_citation_language_against_retained_boundaries`, verifies that master-action language does not imply closure, Phase 2 authorization, seam completion, empirical validation, proof-complete status beyond retained assumptions, or master-action promotion, and selects `review_master_action_dependency_graph_after_citation_language_audit` without reopening seam lanes. |
| `INV-MATH-MASTER-ACTION-DEPENDENCY-GRAPH-REVIEW-v0` | `math` | `synthesis_surface` | Master-action dependency-graph review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/MasterActionDependencyGraphReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-MASTER-ACTION-CITATION-LANGUAGE-AUDIT-v0` | Consumes `review_master_action_dependency_graph_after_citation_language_audit`, records that cleaned citation language changes no dependency class, unblocks no paused lane, authorizes no promotion, and selects `prioritize_retained_blockers_after_master_action_dependency_graph_review` without seam closure, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-MASTER-ACTION-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0` | `math` | `synthesis_surface` | Master-action retained-blocker prioritization review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/MasterActionRetainedBlockerPrioritizationReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-MASTER-ACTION-DEPENDENCY-GRAPH-REVIEW-v0` | Consumes `prioritize_retained_blockers_after_master_action_dependency_graph_review`, ranks retained blockers, selects `PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED` as top priority, and selects `prepare_qm_stat_transport_semantics_retained_blocker_protocol_row` as protocol-row preparation only without theorem work, lane reopening, seam closure, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-PROTOCOL-ROW-v0` | `math` | `synthesis_surface` | QM-STAT transport semantics retained-blocker protocol row | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-MASTER-ACTION-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0` | Consumes `prepare_qm_stat_transport_semantics_retained_blocker_protocol_row`, records `ROW-SEAM-QM-STAT-001` / `SEAM-QM-STAT`, binds the existing residual package and component evidence to required source/target/transport/coarse-graining obligations, and selects `review_qm_stat_transport_semantics_protocol_row_readiness` without theorem work, QM-STAT lane reopening, seam closure, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-READINESS-REVIEW-v0` | `math` | `synthesis_surface` | QM-STAT transport semantics protocol-row readiness review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QMSTATTransportSemanticsProtocolRowReadinessReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-PROTOCOL-ROW-v0` | Consumes `review_qm_stat_transport_semantics_protocol_row_readiness`, marks the protocol row ready for exactly one bounded source-probability-extraction semantics slice, and selects `derive_or_refute_qm_stat_source_probability_extraction_semantics` while leaving target entropy, transport-map, coarse-graining/irreversibility, residual-package semantic closure, QM-STAT seam closure, statistical-mechanics derivation, Phase 2, empirical claim, master-action promotion, and governance-manifest enrollment unauthorized. |
| `INV-MATH-QMSTAT-SOURCE-PROBABILITY-EXTRACTION-SEMANTICS-v0` | `math` | `theorem_surfaces` | QM-STAT source-probability extraction semantics | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_SourceProbabilityExtractionSemantics.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-READINESS-REVIEW-v0` | Consumes `derive_or_refute_qm_stat_source_probability_extraction_semantics`, proves a supplied source-probability extraction route into the QM-STAT source structure, refutes contract-only QM evolution as sufficient for that extraction, records `QM_STAT_SOURCE_PROBABILITY_EXTRACTION_CONTRACT_ONLY_COUNTEREXAMPLE_FRESH_DELTA_v0`, retains source-probability semantics as supplied, and selects `review_qm_stat_source_probability_extraction_semantics_result` without target entropy, transport-map, coarse-graining/irreversibility, residual-package semantic closure, seam closure, statistical-mechanics derivation, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-QMSTAT-SOURCE-PROBABILITY-RESULT-REVIEW-v0` | `math` | `synthesis_surface` | QM-STAT source-probability result review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QMSTATSourceProbabilityExtractionResultReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QMSTAT-SOURCE-PROBABILITY-EXTRACTION-SEMANTICS-v0` | Consumes `review_qm_stat_source_probability_extraction_semantics_result`, accepts the supplied source-probability route from `QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0`, confirms contract-only extraction remains refuted, pauses same-lane QM-STAT theorem work, and selects `prioritize_retained_blockers_after_qm_stat_source_probability_result_review` without target entropy, transport-map, coarse-graining/irreversibility, residual-package semantic closure, seam closure, statistical-mechanics derivation, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-MASTER-ACTION-POST-QMSTAT-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0` | `math` | `synthesis_surface` | Post-QM-STAT retained-blocker prioritization review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/MasterActionPostQMSTATRetainedBlockerPrioritizationReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QMSTAT-SOURCE-PROBABILITY-RESULT-REVIEW-v0` | Consumes `prioritize_retained_blockers_after_qm_stat_source_probability_result_review`, keeps same-lane QM-STAT theorem work paused, selects `PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED` as the next retained blocker for protocol-row preparation, and selects `prepare_qft_gr_source_map_semantics_retained_blocker_protocol_row` without theorem work, lane reopening, QFT-GR seam closure, semiclassical-gravity claim, Einstein-equation derivation claim, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-QFTGR-SOURCE-MAP-SEMANTICS-PROTOCOL-ROW-v0` | `math` | `synthesis_surface` | QFT-GR source-map semantics retained-blocker protocol row | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QFTGRSourceMapSemanticsRetainedBlockerProtocolRow.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-MASTER-ACTION-POST-QMSTAT-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0` | Consumes `prepare_qft_gr_source_map_semantics_retained_blocker_protocol_row`, records `ROW-SEAM-QFT-GR-001` / `SEAM-QFT-GR`, binds the existing source-map package and residual-only obstruction to the still-required source-map semantic obligations, and selects `review_qft_gr_source_map_semantics_protocol_row_readiness` without theorem work, QFT-GR lane reopening, seam closure, semiclassical-gravity claim, Einstein-equation derivation claim, Phase 2, empirical claim, master-action promotion, or governance-manifest enrollment. |
| `INV-MATH-QFTGR-SOURCE-MAP-SEMANTICS-READINESS-REVIEW-v0` | `math` | `synthesis_surface` | QFT-GR source-map semantics protocol-row readiness review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QFTGRSourceMapSemanticsProtocolRowReadinessReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QFTGR-SOURCE-MAP-SEMANTICS-PROTOCOL-ROW-v0` | Consumes `review_qft_gr_source_map_semantics_protocol_row_readiness`, marks the protocol row ready for exactly one bounded stress-energy operator-domain semantics slice, and selects `derive_or_refute_qft_gr_stress_energy_operator_domain_semantics` while broader QFT-GR source-map semantics, seam closure, semiclassical-gravity claims, Einstein-equation derivation claims, Phase 2, empirical claim, master-action promotion, and governance-manifest enrollment remain unauthorized. |
| `INV-MATH-QFTGR-STRESS-ENERGY-SOURCE-MAP-v0` | `math` | `theorem_surfaces` | QFT-GR stress-energy expectation source map | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/QFT_GR_StressEnergyExpectationSourceMap.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-POST-SWEEP-THEOREM-QUEUE-v0` | Defines the QFT stress-energy object, expectation/state functional, GR source object, covariance/conservation assumptions, and residual/error package; supplied expectation/source and weak-curvature/source alignments build a zero-residual package, while full QFT-GR source-map semantics remain retained as `PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED`. |
| `INV-MATH-QFTGR-RESIDUAL-ONLY-SEMANTIC-OBSTRUCTION-v0` | `math` | `theorem_surfaces` | QFT-GR residual-only semantic obstruction | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/QFT_GR_StressEnergySourceMapResidualOnlyObstruction.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QFTGR-STRESS-ENERGY-SOURCE-MAP-v0` | Proves a residual-only counterexample: zero expectation/source and weak-curvature/source residual evidence does not close full QFT-GR source-map semantics when the required semantic fields are false; QFT-GR reaches the two-slice attempt budget and is paused after post-budget review. |
| `INV-MATH-QFTGR-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `math` | `work_queue` | QFT-GR post-budget cross-pillar review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/QFTGRPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QFTGR-RESIDUAL-ONLY-SEMANTIC-OBSTRUCTION-v0` | Executes the loop-control attempt-budget review after the QFT-GR residual-only counterexample; same-lane QFT-GR, scalar, and QM-STAT continuation are not authorized, the master dependency class is unchanged, and SR covariance through cosmology regime transport is selected as the next strict slice. |
| `INV-MATH-SR-COSMOLOGY-REGIME-TRANSPORT-v0` | `math` | `theorem_surfaces` | SR/COSMO regime-transport residual package | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/SR_CosmologyRegimeTransport.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-QFTGR-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | Defines supplied local SR covariance, supplied cosmology background/regime evidence, supplied local/regime alignment, transported interval residual, regime-scale residual, and unified residual; supplied alignment constructs a zero-residual package as a `new_theorem` fresh delta while global SR/COSMO bridge closure remains retained. |
| `INV-MATH-SR-COSMOLOGY-GLOBAL-BRIDGE-SEMANTIC-MAP-OBSTRUCTION-v0` | `math` | `theorem_surfaces` | SR/COSMO global-bridge semantic-map obstruction | `CURRENT` | `formal/toe_formal/ToeFormal/Bridges/SR_CosmologyGlobalBridgeSemanticMapObstruction.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-SR-COSMOLOGY-REGIME-TRANSPORT-v0` | Defines the stricter global SR/COSMO bridge interface and proves zero-residual transport package evidence alone does not force global bridge semantics when the required semantic-map fields are false; records `PHASE1-BLOCKER-SR-COSMO-GLOBAL-BRIDGE-SEMANTIC-MAP-RETAINED` and pauses SR/COSMO at the two-slice attempt budget. |
| `INV-MATH-SR-COSMOLOGY-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `math` | `work_queue` | SR/COSMO post-budget cross-pillar review | `CURRENT` | `formal/toe_formal/ToeFormal/Derivation/SRCosmologyPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-SR-COSMOLOGY-GLOBAL-BRIDGE-SEMANTIC-MAP-OBSTRUCTION-v0` | Executes the loop-control attempt-budget review after the SR/COSMO global semantic-map obstruction; same-lane SR/COSMO, scalar, QM-STAT, and QFT-GR continuation are not authorized, the master dependency class is unchanged, and QM evolution transport-hypotheses work is selected as the next strict slice. |
| `INV-MATH-SCALAR-A1A26-ENDPOINT-REPRESENTATION-SEMANTICS-v0` | `math` | `theorem_surfaces` | Scalar A1A26 endpoint representation/semantics obligation | `CURRENT` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointRepresentationSemanticsObligation.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-LEAN-QFT-SCALAR-AGGREGATE-v0` | Defines supplied endpoint-flux representation, trace/normal semantics, and parent trace/normal bridge interfaces; supplied pieces construct the A1A25 representation/semantics package, while full endpoint-source construction remains retained as `PHASE1-BLOCKER-003A2A15A1A26_ENDPOINT_REPRESENTATION_SEMANTICS_RETAINED`. |
| `INV-MATH-SCALAR-A1A27-ENDPOINT-CONVERGENCE-CONSISTENCY-v0` | `math` | `theorem_surfaces` | Scalar A1A27 endpoint convergence/consistency obligation | `CURRENT` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointConvergenceConsistencyObligation.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-SCALAR-A1A26-ENDPOINT-REPRESENTATION-SEMANTICS-v0` | Defines supplied boundary reconstruction compatibility, flux-term convergence mode, finite endpoint-flux consistency, and parent endpoint-field bridge interfaces; supplied pieces construct the A1A25 convergence/consistency package, while orientation/trace compatibility and full endpoint-source construction remain retained as `PHASE1-BLOCKER-003A2A15A1A27_ENDPOINT_CONVERGENCE_CONSISTENCY_RETAINED`. |
| `INV-MATH-SCALAR-A1A28-ENDPOINT-ORIENTATION-TRACE-v0` | `math` | `theorem_surfaces` | Scalar A1A28 endpoint orientation/trace compatibility obligation | `CURRENT` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointOrientationTraceCompatibilityObligation.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-SCALAR-A1A27-ENDPOINT-CONVERGENCE-CONSISTENCY-v0` | Defines supplied orientation convention, trace-normal convergence, orientation compatibility, and parent orientation/trace bridges; supplied pieces construct the A1A25 orientation/trace package, while refined endpoint-source assembly remains retained as `PHASE1-BLOCKER-003A2A15A1A28_ENDPOINT_ORIENTATION_TRACE_COMPATIBILITY_RETAINED`. |
| `INV-MATH-SCALAR-A1A29-REFINED-ENDPOINT-SOURCE-v0` | `math` | `theorem_surfaces` | Scalar A1A29 refined endpoint-source assembly | `CURRENT` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianRefinedEndpointSourceAssembly.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-SCALAR-A1A28-ENDPOINT-ORIENTATION-TRACE-v0` | Assembles the A1A26 representation/semantics package, A1A27 convergence/consistency package, and A1A28 orientation/trace package into the A1A25 endpoint-source constructor; interface mismatch is not reached, while remaining non-endpoint A2A15A1 evidence is retained as `PHASE1-BLOCKER-003A2A15A1A29_REMAINING_NONENDPOINT_OBLIGATIONS_RETAINED`. |
| `INV-MATH-SCALAR-A1A30-REMAINING-NONENDPOINT-SPLIT-v0` | `math` | `theorem_surfaces` | Scalar A1A30 remaining non-endpoint obligation split | `CURRENT` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianRemainingNonEndpointObligationSplit.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-SCALAR-A1A29-REFINED-ENDPOINT-SOURCE-v0` | Splits the residual non-endpoint A2A15A1 evidence into domain/regularity, raw-IBP-to-Green convergence, pairing convergence, separating test-class semantics, and target continuum semantics packages; supplied packages reconstruct the non-endpoint evidence object, and A1A31 consumes the selected raw-IBP-to-Green obligation as the next bounded scalar surface. |
| `INV-MATH-SCALAR-A1A31-RAW-IBP-GREEN-PACKAGE-v0` | `math` | `theorem_surfaces` | Scalar A1A31 raw-IBP-to-Green convergence package | `CURRENT` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianRawIBPGreenConvergencePackage.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `T-CONDITIONAL` | `INV-MATH-SCALAR-A1A30-REMAINING-NONENDPOINT-SPLIT-v0` | Proves that supplied A2A15A1C finite raw-IBP-to-continuum Green-identity channel evidence fills the A1A30 raw package and, with analytic interval and separating-test supplements, reconstructs the non-endpoint evidence package; evidence-free construction is refuted by a legal false raw-field contract, and scalar drilling is paused under `PHASE1-BLOCKER-003A2A15A1A31_RAW_IBP_TO_GREEN_CONVERGENCE_PACKAGE_RETAINED`. |

## 3) Physics inventory

| inventory_id | domain | category | name | decision_relevance | canonical_source | checkpoint_source | gate_source | status | claim_level | dependencies | notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `INV-PHYS-ROADMAP-v0` | `physics` | `routes` | Physics roadmap dispatch surface | `CURRENT` | `formal/docs/paper/PHYSICS_ROADMAP_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` | `VALIDATED` | `P-POLICY` | `INV-MATH-PILLAR-STATUS-MATRIX-v1` | Canonical route and pin registry. |
| `INV-PHYS-STRICT-DERIVATION-OBLIGATION-MAP-v0` | `physics` | `routes` | Strict physics derivation obligation map | `CURRENT` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `State_of_the_Theory.md` | `formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py` | `USED` | `P-POLICY` | `INV-PHYS-ROADMAP-v0` | Current strict-physics map for scalar/QFT proof-facing obligations, scalar handoff status, cross-pillar methodology, closure frontier, master-action dependency boundary, retained assumptions, and next theorem targets; no publication, promotion, or empirical claim authority by itself. |
| `INV-PHYS-SCALAR-QFT-PHASE0-BASELINE-CONTRACT-v0` | `physics` | `routes` | Scalar QFT Phase 0 baseline acceptance contract | `CURRENT` | `formal/docs/lanes/SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0.md` | `formal/output/reports/scalar_qft_phase0_baseline_acceptance_contract_v0.json` | `formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-STRICT-DERIVATION-OBLIGATION-MAP-v0` | GREEN baseline gate: theorem gap count 7, seam gap count 3, retained scalar-lane assumption rows 6, with Phase 1 blocked until this contract remains green. |
| `INV-PHYS-FREE-SCALAR-WITNESS-FIDELITY-AUDIT-v0` | `physics` | `object_surfaces` | ToE candidate free-scalar witness fidelity audit | `CURRENT` | `formal/docs/lanes/TOE_CANDIDATE_FREE_SCALAR_WITNESS_FIDELITY_AUDIT_v0.md` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` | `USED` | `P-POLICY` | `INV-MATH-LEAN-QFT-SCALAR-AGGREGATE-v0` | Records the bounded free-scalar witness as manually curated but checkable under retained regime assumptions, with A1A31 raw-IBP-to-Green conditional bridge retained and scalar handoff status `SCALAR_QFT_ADVANCED_RETAINED_HANDOFF_READY`; no parser, master-action promotion, seam closure, or empirical validation claim. |
| `INV-PHYS-EXTERNAL-BENCHMARK-REGISTRY-v0` | `physics` | `evidence_lanes` | External physics benchmark registry | `CURRENT` | `formal/docs/lanes/EXTERNAL_PHYSICS_BENCHMARK_REGISTRY_v0.md` | `formal/output/reports/external_physics_benchmark_registry_v0.json` | `formal/python/tests/test_external_physics_benchmark_registry_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-STRICT-DERIVATION-OBLIGATION-MAP-v0` | Registers ten external benchmark pressure points as contextual non-claim prompts only; no theorem-gap movement, blocker discharge, Phase 2 authorization, master-action promotion, or objective-completion claim. |
| `INV-PHYS-DEEP-MATURITY-PROGRAM-v0` | `physics` | `pillars` | Pillar deep maturity program | `CURRENT` | `formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md` | `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json` | `formal/python/tests/test_pillar_deep_maturity_program_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-ROADMAP-v0` | Program-level M1-M5 posture control. |
| `INV-PHYS-EM-U1-OBJECT-v0` | `physics` | `object_surfaces` | EM U1 Maxwell object surface | `CURRENT` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_em_u1_maxwell_object_gate.py` | `USED` | `T-CONDITIONAL` | `INV-MATH-ASSUMPTION-REGISTRY-v1` | EM U1 object and route anchor. |
| `INV-PHYS-EM-U1-MICRO21` | `physics` | `active_micro_route` | EM U1 distributional lane authorization scaffold | `CURRENT` | `formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_em_u1_micro21_distributional_lane_authorization_scaffold_gate.py` | `OPEN_PROOF_DEBT` | `P-POLICY` | `INV-PHYS-EM-U1-OBJECT-v0` | Active/open route surface with distributional debt relevance. |
| `INV-PHYS-QFT-GAUGE-OBJECT-v0` | `physics` | `object_surfaces` | QFT gauge object surface | `BACKGROUND` | `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md` | `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md` | `formal/python/tests/test_qft_full_derivation_discharge_gate.py` | `USED` | `T-CONDITIONAL` | `INV-PHYS-ROADMAP-v0` | Canonical QFT gauge route object. |
| `INV-PHYS-QM-EVOLUTION-OBJECT-v0` | `physics` | `object_surfaces` | QM evolution object surface | `BACKGROUND` | `formal/docs/paper/DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md` | `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md` | `formal/python/tests/test_qm_full_derivation_discharge_gate.py` | `USED` | `T-CONDITIONAL` | `INV-MATH-QM-EVOLUTION-CONTRACT` | QM pillar object anchor. |
| `INV-PHYS-GR-GEOMETRY-OBJECT-v0` | `physics` | `object_surfaces` | GR geometry object surface | `BACKGROUND` | `formal/docs/paper/DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md` | `formal/docs/paper/TOE_GR01_ANALYTIC_DISCHARGE_v0.md` | `formal/python/tests/test_gr01_publication_theorem_claim_advancement_gate.py` | `USED` | `T-CONDITIONAL` | `INV-MATH-GR-CONSERVATION-CONTRACT` | GR object route anchor and discharge-facing surface. |
| `INV-PHYS-SR-COVARIANCE-OBJECT-v0` | `physics` | `object_surfaces` | SR covariance object surface | `BACKGROUND` | `formal/docs/paper/DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md` | `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json` | `formal/python/tests/test_sr_m5_theory_parity_link_cycle56_gate.py` | `USED` | `T-CONDITIONAL` | `INV-PHYS-DEEP-MATURITY-PROGRAM-v0` | SR parity-link maturity surface. |
| `INV-PHYS-STAT-ENTROPY-PLAN-v0` | `physics` | `object_surfaces` | STAT entropy plan surface | `BACKGROUND` | `formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md` | `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json` | `formal/python/tests/test_stat_m3_completion_promotion_cycle01_gate.py` | `USED` | `P-POLICY` | `INV-PHYS-DEEP-MATURITY-PROGRAM-v0` | STAT route and discriminator dependency surface. |
| `INV-PHYS-COSMO-BG-OBJECT-v0` | `physics` | `object_surfaces` | Cosmology background object surface | `BACKGROUND` | `formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md` | `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json` | `formal/python/tests/test_cosmo_background_kickoff_gate.py` | `USED` | `P-POLICY` | `INV-PHYS-DEEP-MATURITY-PROGRAM-v0` | COSMO route anchor with active checkpoint chain. |
| `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | `physics` | `seams` | Class-B seam inventory | `CURRENT` | `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_toe_master_action_class_b_inventory_gate.py` | `VALIDATED` | `P-POLICY` | `INV-MATH-SEAM-WITNESS-PACKAGE` | Primary seam status and promotion-readiness surface. |
| `INV-PHYS-SEAM-CONSTRAINT-REGISTRY-v0` | `physics` | `seams` | Seam constraint registry | `CURRENT` | `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_toe_master_action_seam_registry_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | Constraint-level seam policy and class wiring. |
| `INV-PHYS-SEAM-LIVE-CONTRADICTION-v0` | `physics` | `seams` | Live seam contradiction surface | `CURRENT` | `formal/docs/release/SCIENCE_MATURITY_CONTRADICTION_REPORT_POLICY_20260416_v0.md` | `formal/output/reports/science_maturity_contradiction_report_20260416_v0.json` | `formal/python/tests/test_science_maturity_contradiction_report_live_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | Fail-closed surface exposing maturity-vs-live blocker and seam-status contradictions. |
| `INV-PHYS-PREDICTION-SCOREBOARD-v0` | `physics` | `evidence_lanes` | Prediction-first scoreboard | `CURRENT` | `formal/output/prediction_first_scoreboard_v0.json` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_prediction_first_scoreboard_gate.py` | `VALIDATED` | `E-REPRO` | `INV-PHYS-ROADMAP-v0` | Prediction/evidence lane decision surface. |
| `INV-PHYS-EMPIRICAL-PROTOCOL-v0` | `physics` | `evidence_lanes` | Foundational empirical comparison protocol | `CURRENT` | `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md` | `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json` | `formal/python/tests/test_foundational_empirical_packet05_progression_policy_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-ROADMAP-v0` | Packet progression and falsification protocol anchor. |
| `INV-PHYS-QFT-GR-PACKET41-HOLD` | `physics` | `hold_controls` | QFT-GR Packet41 hold posture | `CURRENT` | `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` | `BOUNDED_NONCLAIM` | `P-POLICY` | `INV-PHYS-SEAM-CONSTRAINT-REGISTRY-v0` | Explicit hold-retained state under missing numeric inputs. |
| `INV-PHYS-QFT-GR-PACKET41-SUCCESSOR-PACKAGE-v0` | `physics` | `hold_controls` | QFT-GR Packet41 successor discriminator package | `CURRENT` | `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_v0.md` | `formal/output/toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0.json` | `formal/python/tests/test_toe_qft_gr_seam_packet41_successor_discriminator_package_gate.py` | `BOUNDED_NONCLAIM` | `P-POLICY` | `INV-PHYS-QFT-GR-PACKET41-HOLD` | Concrete successor package pinned while hold remains active pending admissible numeric clearance. |
| `INV-PHYS-QM-STAT-RL10-COMP-ANALYSIS-PACKET01-v0` | `physics` | `evidence_lanes` | QM-STAT RL10 computational-analysis Packet-01 | `CURRENT` | `formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md` | `formal/output/qm_stat_rl10_computational_analysis_packet_01_v0.json` | `formal/python/tests/test_qm_stat_rl10_computational_analysis_packet_01_gate.py` | `BOUNDED_NONCLAIM` | `P-POLICY` | `INV-PHYS-SEAM-CONSTRAINT-REGISTRY-v0` | Auxiliary computational-analysis packet under `AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`, tied to declared RL10 bridge surfaces only; fixed to `INCONCLUSIVE_v0`, closed after one authorized refinement, and preserved via `formal/docs/paper/QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_PRESERVATION_NOTE_v0.md` as a bounded success-without-escalation result; Packet-02 and restart implication remain disallowed. |
| `INV-PHYS-TOE-MASTER-ACTION-COMP-ANALYSIS-PACKET01-v0` | `physics` | `evidence_lanes` | ToE master-action computational-analysis Packet-01 | `CURRENT` | `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md` | `formal/output/toe_master_action_computational_analysis_packet_01_v0.json` | `formal/python/tests/test_toe_master_action_computational_analysis_packet_01_gate.py` | `BOUNDED_NONCLAIM` | `P-POLICY` | `INV-PHYS-SEAM-CONSTRAINT-REGISTRY-v0` | Deterministic NumPy-first local computational-analysis packet for the master-action family; packet-level decision remains `INCONCLUSIVE_v0`, the bounded decision surface authorized exactly one local refinement, and the family is now preserved via `formal/docs/paper/TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_PRESERVATION_NOTE_v0.md` as a closed success-without-escalation result with Packet-02, GPU migration, lane reopen, and blocker movement still disallowed. |
| `INV-PHYS-TOE-MASTER-ACTION-COMP-ANALYSIS-PACKET01-REFINEMENT01-v0` | `physics` | `evidence_lanes` | ToE master-action computational-analysis Packet-01 refinement 01 | `CURRENT` | `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_v0.md` | `formal/output/toe_master_action_computational_analysis_packet_01_refinement_01_v0.json` | `formal/python/tests/test_toe_master_action_computational_analysis_packet_01_refinement_01_gate.py` | `BOUNDED_NONCLAIM` | `P-POLICY` | `INV-PHYS-TOE-MASTER-ACTION-COMP-ANALYSIS-PACKET01-v0` | Single authorized perturbation-window tightening under the frozen master-action Packet-01 operator family; the packet remains `INCONCLUSIVE_v0`, no second refinement or Packet-02 is authorized, and the family is closed by the paired closeout decision surface. |
| `INV-PHYS-TOE-MASTER-ACTION-PACKET01-TRANSPORT-BINDING-RECOVERY-v0` | `physics` | `seams` | Master-action Packet-01 transport-binding recovery surface | `CURRENT` | `formal/docs/release/MASTER_ACTION_PACKET_01_TRANSPORT_BINDING_RECOVERY_20260418_v0.json` | `formal/output/reports/master_action_packet_01_transport_binding_recovery_20260418_v0.json` | `formal/python/tests/test_master_action_packet_01_transport_binding_recovery_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-EXECUTABLE-PATH-NORMALIZATION-v0` | Canonicalizes the Phase 4 master-action transport read by preserving the Packet-01 family endpoint, binding the QM-STAT witness and minimal upstream unit, and making `PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED` the current explicit fail-closed blocker on `ROW-SEAM-QM-STAT-001` after the finite residual package refines prior `NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE`. |
| `INV-PHYS-DERIVATION-CHAIN-TRANSPORT-STANDARDIZATION-v0` | `physics` | `synthesis_surface` | Derivation-chain transport standardization surface | `CURRENT` | `formal/docs/release/DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_20260418_v0.json` | `formal/output/reports/derivation_chain_transport_standardization_20260418_v0.json` | `formal/python/tests/test_derivation_chain_transport_standardization_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-TOE-MASTER-ACTION-PACKET01-TRANSPORT-BINDING-RECOVERY-v0` | Standardizes the admitted derivation-chain pillar grammar under the canonical Phase 4 transport read and materializes one machine-checkable Phase 5 surface across the seven admitted pillars. |
| `INV-PHYS-FINAL-NONCLAIM-INTEGRATION-GATE-v0` | `physics` | `synthesis_surface` | Final non-claim integration and promotion gate surface | `CURRENT` | `formal/docs/release/FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_20260418_v0.json` | `formal/output/reports/final_nonclaim_integration_promotion_gate_20260418_v0.json` | `formal/python/tests/test_final_nonclaim_integration_promotion_gate_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-DERIVATION-CHAIN-TRANSPORT-STANDARDIZATION-v0` | Aggregates the Phase 3 normalization, Phase 4 recovery, and Phase 5 standardization surfaces under one fail-closed final non-claim integration gate. |
| `INV-PHYS-POST-PLAN-CONSOLIDATION-MEMO-v0` | `physics` | `synthesis_surface` | Post-plan consolidation memo | `CURRENT` | `formal/docs/release/POST_PLAN_CONSOLIDATION_MEMO_20260418_v0.md` | `formal/output/reports/final_nonclaim_integration_promotion_gate_20260418_v0.json` | `formal/python/tests/test_state_theory_dag.py` | `USED` | `P-POLICY` | `INV-PHYS-FINAL-NONCLAIM-INTEGRATION-GATE-v0` | Declares the Phase 3 through Phase 6 control stack canonical for current repo reads and downgrades WS-10 restart-era surfaces to historical traceability posture unless a new post-plan program explicitly reactivates them. |
| `INV-PHYS-POST-PLAN-PHYSICS-ADVANCEMENT-PROGRAM-v0` | `physics` | `synthesis_surface` | Post-plan physics advancement program | `CURRENT` | `formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md` | `formal/output/reports/blocker_burn_dashboard_20260416_v0.json` | `formal/python/tests/test_state_theory_dag.py` | `USED` | `P-POLICY` | `INV-PHYS-POST-PLAN-CONSOLIDATION-MEMO-v0` | Opens a new post-plan execution program that defines advancement strictly as live blocker reduction, seam-path improvement, or justified master-action reclassification after upstream row movement, with COSMO-SR as the sole executable seam and GR row 001 pinned to the dormant new-structure branch; the current post-cascade bounded hold is now explicitly handed off into the downstream objective-quality completion queue. |
| `INV-PHYS-POST-PLAN-OBJECTIVE-QUALITY-COMPLETION-PROGRAM-v0` | `physics` | `synthesis_surface` | Post-plan objective-quality physics completion program | `CURRENT` | `formal/docs/release/POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_PROGRAM_20260418_v0.md` | `formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json` | `formal/python/tests/test_post_plan_objective_quality_physics_completion_queue_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-PHYSICS-ADVANCEMENT-PROGRAM-v0` | Converts the held post-plan advancement stack into a closure-plus-exhaustion completion program that classifies each live route as advanced, exhausted, authority-blocked, or externally held; the currently pinned queue has already consumed the post-cascade QFT, EM, and SR continuation tranches, materialized the conversion-review wrapper, and now records a dedicated explicit exhaustion decision for the current declared family. |
| `INV-PHYS-POST-PLAN-REMAINING-PHYSICS-EXECUTION-ORDER-v0` | `physics` | `synthesis_surface` | Post-plan remaining physics execution order | `CURRENT` | `formal/docs/release/POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_20260419_v0.json` | `formal/output/reports/post_plan_remaining_physics_execution_order_20260419_v0.json` | `formal/python/tests/test_post_plan_remaining_physics_execution_order_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-OBJECTIVE-QUALITY-COMPLETION-PROGRAM-v0` | Pins the current remaining-work order after the April 19 unlock and exhaustion decisions by ranking one machine-pinned COSMO-SR continuation family first, preserving the objective-quality queue as downstream-only second, and keeping any post-cascade successor reopen third until fresh blocker-facing movement is machine-pinned. |
| `INV-PHYS-POST-PLAN-COSMO-SR-SELECTED-CONTINUATION-FAMILY-v0` | `physics` | `seams` | Post-plan COSMO-SR selected continuation family | `CURRENT` | `formal/docs/release/POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_20260419_v0.json` | `formal/output/reports/post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_selected_continuation_family_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-REMAINING-PHYSICS-EXECUTION-ORDER-v0` | Starts the next post-plan execution tranche by binding the unlocked machine-pinned Cycle08 payload into one single-use COSMO-SR continuation family whose immediate next action is `EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE`. |
| `INV-PHYS-POST-PLAN-COSMO-SR-SELECTED-CONTINUATION-EXECUTION-v0` | `physics` | `seams` | Post-plan COSMO-SR selected continuation execution | `CURRENT` | `formal/docs/release/POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_20260419_v0.json` | `formal/output/reports/post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_selected_continuation_execution_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-COSMO-SR-SELECTED-CONTINUATION-FAMILY-v0` | Records the single-use Cycle08 continuation execution as a bounded nonpromoted closeout under the current seam row and advances the downstream handoff to `PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES`. |
| `INV-PHYS-POST-PLAN-ORDERED-THEOREM-GAP-CONTINUATION-TRANCHE-v0` | `physics` | `synthesis_surface` | Post-plan ordered theorem-gap continuation tranche | `CURRENT` | `formal/docs/release/POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_20260419_v0.json` | `formal/output/reports/post_plan_ordered_theorem_gap_continuation_tranche_20260419_v0.json` | `formal/python/tests/test_post_plan_ordered_theorem_gap_continuation_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-REMAINING-PHYSICS-EXECUTION-ORDER-v0` | Binds the existing STAT theorem-gap tranche into the April 19 remaining-work ordering as the explicitly selected theorem-gap continuation surface once the higher-priority COSMO-SR continuation execution has closed out, then advances the downstream handoff to the GR dormant package. |
| `INV-PHYS-POST-PLAN-OBJECTIVE-QUALITY-COMPLETION-QUEUE-v0` | `physics` | `synthesis_surface` | Post-plan objective-quality physics completion queue | `CURRENT` | `formal/docs/release/POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_20260418_v0.json` | `formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json` | `formal/python/tests/test_post_plan_objective_quality_physics_completion_queue_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-OBJECTIVE-QUALITY-COMPLETION-PROGRAM-v0` | Materializes a theorem-gap-first completion queue that excludes QM from immediate reuse, places COSMO first, STAT second, and GR dormant-package work third while preserving the current seam and master-action hold constraints. |
| `INV-PHYS-POST-PLAN-COSMO-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `physics` | `pillars` | Post-plan COSMO theorem-gap completion tranche | `CURRENT` | `formal/docs/release/POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_cosmo_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_cosmo_theorem_gap_completion_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-OBJECTIVE-QUALITY-COMPLETION-QUEUE-v0` | Measures the first queued objective-quality theorem-gap completion tranche against `ROW-PILLAR-COSMO-001` and records that the current COSMO packet-04 route remains non-promoted under live row truth, so the next queued row is STAT rather than a seam reclassification. |
| `INV-PHYS-POST-PLAN-STAT-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `physics` | `pillars` | Post-plan STAT theorem-gap completion tranche | `CURRENT` | `formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_stat_theorem_gap_completion_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-COSMO-THEOREM-GAP-COMPLETION-TRANCHE-v0` | Measures the second queued objective-quality theorem-gap completion tranche against `ROW-PILLAR-STAT-001` and records that the current STAT packet-04 route remains non-promoted under live row truth, so the next queued row is the GR dormant new-structure path rather than a seam reclassification. |
| `INV-PHYS-POST-PLAN-GR-DORMANT-NEW-STRUCTURE-COMPLETION-TRANCHE-v0` | `physics` | `pillars` | Post-plan GR dormant new-structure completion tranche | `CURRENT` | `formal/docs/release/POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_gr_dormant_new_structure_completion_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-STAT-THEOREM-GAP-COMPLETION-TRANCHE-v0` | Measures the first heavy structural objective-quality completion tranche against `ROW-PILLAR-GR-001` using the frozen blocker file map and canonical dormant GR design package, and records explicit exhaustion of the dormant new-structure branch under unchanged live row truth so the next path is deeper blocker-definition review rather than retry-era GR packet reuse. |
| `INV-PHYS-POST-PLAN-DEEPER-BLOCKER-DEFINITION-REVIEW-SUCCESSOR-TRANCHE-v0` | `physics` | `synthesis_surface` | Post-plan deeper blocker-definition review successor tranche | `CURRENT` | `formal/docs/release/POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_deeper_blocker_definition_review_successor_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-GR-DORMANT-NEW-STRUCTURE-COMPLETION-TRANCHE-v0` | Converts the GR explicit-exhaustion result into a machine-checkable opening of the existing deeper blocker-definition review path and pins the next action to one bounded blocker-definition test packet once. |
| `INV-PHYS-POST-PLAN-BOUNDED-BLOCKER-DEFINITION-TEST-PACKET-CHAIN-v0` | `physics` | `synthesis_surface` | Post-plan bounded blocker-definition test packet chain | `CURRENT` | `formal/docs/release/POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_20260418_v0.json` | `formal/output/reports/post_plan_bounded_blocker_definition_test_packet_chain_20260418_v0.json` | `formal/python/tests/test_post_plan_bounded_blocker_definition_test_packet_chain_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-DEEPER-BLOCKER-DEFINITION-REVIEW-SUCCESSOR-TRANCHE-v0` | Materializes the bounded blocker-definition test packet, ruling, and post-decision chain under the post-plan program and records that the revised blocker definition is valid but nonmoving, so the next path is a bounded authority-coupling review rather than further blocker-definition packet reuse. |
| `INV-PHYS-POST-PLAN-AUTHORITY-COUPLING-REVIEW-PATH-v0` | `physics` | `synthesis_surface` | Post-plan authority-coupling review path | `CURRENT` | `formal/docs/release/POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_20260418_v0.json` | `formal/output/reports/post_plan_authority_coupling_review_path_20260418_v0.json` | `formal/python/tests/test_post_plan_authority_coupling_review_path_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-BOUNDED-BLOCKER-DEFINITION-TEST-PACKET-CHAIN-v0` | Materializes the bounded authority-coupling review under the post-plan program and records that the live review justifies one bounded coupling-refinement packet once rather than broader escalation or indefinite hold. |
| `INV-PHYS-POST-PLAN-BOUNDED-COUPLING-REFINEMENT-PACKET-CHAIN-v0` | `physics` | `synthesis_surface` | Post-plan bounded coupling-refinement packet chain | `CURRENT` | `formal/docs/release/POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_20260418_v0.json` | `formal/output/reports/post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json` | `formal/python/tests/test_post_plan_bounded_coupling_refinement_packet_chain_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-AUTHORITY-COUPLING-REVIEW-PATH-v0` | Materializes the bounded coupling-refinement packet, the promotion-supporting ruling, and the authority-promotion registration follow-through under the post-plan program, then routes next execution to recompute monitoring. |
| `INV-PHYS-POST-PLAN-RECOMPUTE-MONITORING-PATH-v0` | `physics` | `synthesis_surface` | Post-plan recompute-monitoring path | `CURRENT` | `formal/docs/release/POST_PLAN_RECOMPUTE_MONITORING_PATH_20260418_v0.json` | `formal/output/reports/post_plan_recompute_monitoring_path_20260418_v0.json` | `formal/python/tests/test_post_plan_recompute_monitoring_path_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-BOUNDED-COUPLING-REFINEMENT-PACKET-CHAIN-v0` | Materializes the recompute observation and post-recompute ruling chain under the post-plan program and records that trigger propagation is confirmed, canonical outputs are materially present, and the recompute family has entered a documented cascade-consequence stage rather than remaining pending. |
| `INV-PHYS-RECOMPUTE-LIVE-WRITEBACK-CONTRACT-v0` | `physics` | `synthesis_surface` | Recompute live-writeback contract | `CURRENT` | `formal/docs/release/RECOMPUTE_LIVE_WRITEBACK_CONTRACT_20260418_v0.json` | `formal/output/reports/recompute_live_writeback_contract_20260418_v0.json` | `formal/python/tests/test_recompute_live_writeback_contract_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-RECOMPUTE-MONITORING-PATH-v0` | Defines the bounded writeback contract for recompute execution after the monitoring path goes pending, including baseline capture, dry-run default execution, explicit live-writeback opt-in, rerun obligations for the observation chain, and mirror discipline that avoids overstating live completion. |
| `INV-PHYS-RECOMPUTE-DRY-RUN-EXECUTION-INSPECTION-v0` | `physics` | `synthesis_surface` | Recompute dry-run execution inspection | `CURRENT` | `formal/docs/release/RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_20260418_v0.json` | `formal/output/reports/recompute_dry_run_execution_inspection_20260418_v0.json` | `formal/python/tests/test_recompute_dry_run_execution_inspection_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-RECOMPUTE-LIVE-WRITEBACK-CONTRACT-v0` | Records that the bounded dry-run recompute bundle materializes outputs in the copied non-canonical workspace while canonical recompute surfaces remain pending and unchanged, so the next boundary is defining canonical live-writeback baseline and approval conditions rather than claiming completion. |
| `INV-PHYS-RECOMPUTE-LIVE-WRITEBACK-BASELINE-APPROVAL-v0` | `physics` | `synthesis_surface` | Recompute live-writeback baseline approval | `CURRENT` | `formal/docs/release/RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_20260418_v0.json` | `formal/output/reports/recompute_live_writeback_baseline_approval_20260418_v0.json` | `formal/python/tests/test_recompute_live_writeback_baseline_approval_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-RECOMPUTE-DRY-RUN-EXECUTION-INSPECTION-v0` | Pins the single-use canonical live-writeback approval boundary after dry-run inspection, requiring pending canonical surfaces, explicit live opt-in, and immediate rerun of the observation chain after one authorized canonical execution. |
| `INV-PHYS-POST-PLAN-POST-CASCADE-CLOSURE-REVIEW-v0` | `physics` | `synthesis_surface` | Post-plan post-cascade closure review | `CURRENT` | `formal/docs/release/POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_20260418_v0.json` | `formal/output/reports/post_plan_post_cascade_closure_review_20260418_v0.json` | `formal/python/tests/test_post_plan_post_cascade_closure_review_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-RECOMPUTE-LIVE-WRITEBACK-BASELINE-APPROVAL-v0` | Consumes the material-cascade-confirmed recompute outcome together with the already materialized seam reroute, master-action, and final integration reports and records whether the downstream route should reopen or whether the stronger evidence still only justifies an explicit bounded hold. |
| `INV-PHYS-POST-PLAN-QFT-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `physics` | `pillars` | Post-plan QFT theorem-gap completion tranche | `CURRENT` | `formal/docs/release/POST_PLAN_QFT_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_qft_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_qft_theorem_gap_completion_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-POST-CASCADE-CLOSURE-REVIEW-v0` | Measures the first cascade-informed follow-on theorem-gap completion tranche against `ROW-PILLAR-QFT-001` and records that the current QFT packet-04 route remains non-promoted under live row truth, so the next queued row is EM rather than treating the post-cascade hold as the terminal theorem-gap state. |
| `INV-PHYS-POST-PLAN-EM-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `physics` | `pillars` | Post-plan EM theorem-gap completion tranche | `CURRENT` | `formal/docs/release/POST_PLAN_EM_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_em_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_em_theorem_gap_completion_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-QFT-THEOREM-GAP-COMPLETION-TRANCHE-v0` | Measures the second cascade-informed follow-on theorem-gap completion tranche against `ROW-PILLAR-EM-001` and records that the current EM packet-04 route remains non-promoted under live row truth with QFT nonmoving history consumed explicitly, so the next queued row is SR. |
| `INV-PHYS-POST-PLAN-SR-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `physics` | `pillars` | Post-plan SR theorem-gap completion tranche | `CURRENT` | `formal/docs/release/POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_sr_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_sr_theorem_gap_completion_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-EM-THEOREM-GAP-COMPLETION-TRANCHE-v0` | Measures the third cascade-informed follow-on theorem-gap completion tranche against `ROW-PILLAR-SR-001` on the live SR packet-05 route and records that the current SR route remains non-promoted under live row truth with EM nonmoving history consumed explicitly, so the next action is the declared program-state conversion review rather than another theorem-gap row. |
| `INV-PHYS-POST-PLAN-PROGRAM-STATE-CONVERSION-REVIEW-WRAPPER-v0` | `physics` | `synthesis_surface` | Post-plan program-state conversion review wrapper | `CURRENT` | `formal/docs/release/POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_20260418_v0.json` | `formal/output/reports/post_plan_program_state_conversion_review_wrapper_20260418_v0.json` | `formal/python/tests/test_post_plan_program_state_conversion_review_wrapper_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-SR-THEOREM-GAP-COMPLETION-TRANCHE-v0` | Consumes the non-promoted SR tranche together with the existing one-shot program-state conversion review and its already materialized downstream successor path, records that the theorem-gap queue is closed against another lookalike row under the declared no-loop rule, and reuses the existing downstream path rather than reopening the conversion-review branch. |
| `INV-PHYS-POST-PLAN-POST-CASCADE-EXPLICIT-EXHAUSTION-DECISION-v0` | `physics` | `synthesis_surface` | Post-plan post-cascade explicit exhaustion decision | `CURRENT` | `formal/docs/release/POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_20260419_v0.json` | `formal/output/reports/post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json` | `formal/python/tests/test_post_plan_post_cascade_explicit_exhaustion_decision_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-PROGRAM-STATE-CONVERSION-REVIEW-WRAPPER-v0` | Consumes the bounded hold, the completed QFT/EM/SR nonmoving chain, and the conversion-review wrapper to record that the currently declared post-cascade continuation family is formally exhausted unless and until a newly declared successor family is machine-pinned. |
| `INV-PHYS-POST-PLAN-POST-CASCADE-SUCCESSOR-FAMILY-ELIGIBILITY-REVIEW-v0` | `physics` | `synthesis_surface` | Post-plan post-cascade successor-family eligibility review | `CURRENT` | `formal/docs/release/POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json` | `formal/output/reports/post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json` | `formal/python/tests/test_post_plan_post_cascade_successor_family_eligibility_review_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-POST-CASCADE-EXPLICIT-EXHAUSTION-DECISION-v0` | Consumes the exhausted post-cascade continuation state together with the blocker dashboard and target map to record whether any fresh blocker-facing movement actually authorizes a newly declared successor family, and currently records that none is eligible. |
| `INV-PHYS-POST-PLAN-THEOREM-GAP-REDUCTION-REACTIVATION-PROGRAM-v0` | `physics` | `synthesis_surface` | Post-plan theorem-gap reduction reactivation program | `CURRENT` | `formal/docs/release/POST_PLAN_THEOREM_GAP_REDUCTION_REACTIVATION_PROGRAM_20260419_v0.md` | `formal/output/reports/post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json` | `formal/python/tests/test_post_plan_theorem_gap_fresh_movement_qualification_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-POST-CASCADE-SUCCESSOR-FAMILY-ELIGIBILITY-REVIEW-v0` | Opens the post-exhaustion theorem-gap reactivation control stack, fixes STAT as the default reopen row, permits COSMO only through a machine-pinned seam-linked override, keeps GR dormant-package-only, leaves QFT/EM/SR in reserve, and keeps QM excluded pending non-QM movement. |
| `INV-PHYS-POST-PLAN-THEOREM-GAP-FRESH-MOVEMENT-QUALIFICATION-v0` | `physics` | `synthesis_surface` | Post-plan theorem-gap fresh-movement qualification | `CURRENT` | `formal/docs/release/POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_20260419_v0.json` | `formal/output/reports/post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json` | `formal/python/tests/test_post_plan_theorem_gap_fresh_movement_qualification_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-REDUCTION-REACTIVATION-PROGRAM-v0` | Consumes the exhausted post-cascade stop state plus the current blocker dashboard and target map to determine whether fresh blocker-facing movement has been machine-pinned strongly enough to select exactly one reopen row, and currently records no row selected. |
| `INV-PHYS-POST-PLAN-THEOREM-GAP-ROW-REOPEN-DOSSIER-FAMILY-v0` | `physics` | `pillars` | Post-plan theorem-gap row reopen dossier family | `CURRENT` | `formal/docs/release/POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_STAT_20260419_v0.json` | `formal/output/reports/post_plan_theorem_gap_row_reopen_dossier_stat_20260419_v0.json` | `formal/python/tests/test_post_plan_theorem_gap_row_reopen_dossier_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-FRESH-MOVEMENT-QUALIFICATION-v0` | Materializes seven reopen dossiers that bind each theorem-gap row to one explicit hypothesis, one measurable blocker-delta criterion, one bounded execution surface, and one explicit exhaustion fallback, while enforcing QM exclusion, COSMO override discipline, GR dormant-only routing, and QFT/EM/SR reserve posture. |
| `INV-PHYS-POST-PLAN-STAT-FRESH-MOVEMENT-EVIDENCE-SURFACE-v0` | `physics` | `pillars` | Post-plan STAT fresh-movement evidence surface | `CURRENT` | `formal/docs/release/POST_PLAN_STAT_FRESH_MOVEMENT_EVIDENCE_SURFACE_20260419_v0.json` | `formal/output/reports/post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json` | `formal/python/tests/test_post_plan_stat_fresh_movement_evidence_surface_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-ROW-REOPEN-DOSSIER-FAMILY-v0` | Measures whether the existing STAT packet-04 tuple plus its historical continuation chain now carry fresh blocker-facing movement strong enough for the default first reopen dossier, and currently records that the chain is ready while the theorem-gap delta is still unpinned. |
| `INV-PHYS-POST-PLAN-STAT-THEOREM-GAP-DELTA-SOURCE-REVIEW-v0` | `physics` | `pillars` | Post-plan STAT theorem-gap delta-source review | `CURRENT` | `formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_DELTA_SOURCE_REVIEW_20260419_v0.json` | `formal/output/reports/post_plan_stat_theorem_gap_delta_source_review_20260419_v0.json` | `formal/python/tests/test_post_plan_stat_theorem_gap_delta_source_review_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-STAT-FRESH-MOVEMENT-EVIDENCE-SURFACE-v0` | Reviews the concrete delta source behind the fail-closed STAT evidence surface, confirms that packet-04 remains protocol-capped while STAT is absent from the selective packet-05 bootstrap matrix, and points the next bounded move at a STAT packet-05 lane-eligibility review instead of another packet-04 replay. |
| `INV-PHYS-POST-PLAN-STAT-PACKET05-LANE-ELIGIBILITY-REVIEW-v0` | `physics` | `pillars` | Post-plan STAT packet-05 lane-eligibility review | `CURRENT` | `formal/docs/release/POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_20260420_v0.json` | `formal/output/reports/post_plan_stat_packet05_lane_eligibility_review_20260420_v0.json` | `formal/python/tests/test_post_plan_stat_packet05_lane_eligibility_review_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-STAT-THEOREM-GAP-DELTA-SOURCE-REVIEW-v0` | Converts the STAT delta-source next step into a dedicated repo-native review, confirms that the live packet-05 bootstrap still binds only `GR` and `SR`, and keeps the STAT reopen chain fail-closed while no STAT packet-05 matrix or ledger binding exists. |
| `INV-PHYS-POST-PLAN-THEOREM-GAP-SUCCESSOR-FAMILY-AUTHORIZATION-REVIEW-v0` | `physics` | `synthesis_surface` | Post-plan theorem-gap successor-family authorization review | `CURRENT` | `formal/docs/release/POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_20260419_v0.json` | `formal/output/reports/post_plan_theorem_gap_successor_family_authorization_review_20260419_v0.json` | `formal/python/tests/test_post_plan_theorem_gap_successor_family_authorization_review_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-ROW-REOPEN-DOSSIER-FAMILY-v0` | Scores the row dossiers under a single-row authorization rule, rejects stale exhausted-family reuse, fails closed on QM without prior non-QM movement, and currently records that no reopen family is authorized. |
| `INV-PHYS-POST-PLAN-THEOREM-GAP-RERANKING-v0` | `physics` | `synthesis_surface` | Post-plan theorem-gap reranking | `CURRENT` | `formal/docs/release/POST_PLAN_THEOREM_GAP_RERANKING_20260419_v0.json` | `formal/output/reports/post_plan_theorem_gap_reranking_20260419_v0.json` | `formal/python/tests/test_post_plan_theorem_gap_reranking_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-SUCCESSOR-FAMILY-AUTHORIZATION-REVIEW-v0` | Republishes the remaining theorem-gap row order only after a blocker delta or explicit exhaustion trigger, keeps QM last, and currently retains the fail-closed order `STAT -> COSMO -> GR -> QFT -> EM -> SR -> QM`. |
| `INV-PHYS-POST-PLAN-STAT-THEOREM-GAP-REACTIVATION-TRANCHE-v0` | `physics` | `pillars` | Post-plan STAT theorem-gap reactivation tranche | `CURRENT` | `formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_20260419_v0.json` | `formal/output/reports/post_plan_stat_theorem_gap_reactivation_tranche_20260419_v0.json` | `formal/python/tests/test_post_plan_stat_theorem_gap_reactivation_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-SUCCESSOR-FAMILY-AUTHORIZATION-REVIEW-v0` | Refreshes the STAT reopen contract so the family may resolve only to blocker reduction, explicit exhaustion, or repair hold, and currently fails closed because no fresh authorized STAT family has been selected. |
| `INV-PHYS-POST-PLAN-COSMO-THEOREM-GAP-REACTIVATION-TRANCHE-v0` | `physics` | `pillars` | Post-plan COSMO theorem-gap reactivation tranche | `CURRENT` | `formal/docs/release/POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_20260419_v0.json` | `formal/output/reports/post_plan_cosmo_theorem_gap_reactivation_tranche_20260419_v0.json` | `formal/python/tests/test_post_plan_cosmo_theorem_gap_reactivation_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-SUCCESSOR-FAMILY-AUTHORIZATION-REVIEW-v0` | Refreshes the COSMO reopen contract so COSMO may overtake STAT only under a machine-pinned seam-linked override and may resolve only to blocker reduction, explicit exhaustion, or repair hold, and currently fails closed because no override-qualified family has been authorized. |
| `INV-PHYS-POST-PLAN-GR-DORMANT-NEW-STRUCTURE-REACTIVATION-TRANCHE-v0` | `physics` | `pillars` | Post-plan GR dormant new-structure reactivation tranche | `CURRENT` | `formal/docs/release/POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_20260419_v0.json` | `formal/output/reports/post_plan_gr_dormant_new_structure_reactivation_tranche_20260419_v0.json` | `formal/python/tests/test_post_plan_gr_dormant_new_structure_reactivation_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-THEOREM-GAP-SUCCESSOR-FAMILY-AUTHORIZATION-REVIEW-v0` | Refreshes the GR reopen contract so GR may run only through the dormant new-structure branch and may resolve only to blocker reduction, explicit exhaustion, or repair hold, while refusing any fallback to the older empirical packet path. |
| `INV-PHYS-POST-PLAN-PHYSICS-ADVANCEMENT-TARGET-MAP-v0` | `physics` | `synthesis_surface` | Post-plan physics advancement target map | `CURRENT` | `formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_20260418_v0.json` | `formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json` | `formal/python/tests/test_post_plan_physics_advancement_target_map_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-PHYSICS-ADVANCEMENT-PROGRAM-v0` | Resolves every active pillar and seam row to one authoritative live next-step route using the completion matrix, blocker dashboard, seam SLA ledger, seam executable-path normalization report, and the GR row 001 blocker file map, with COSMO-SR pinned as the sole executable-now row. |
| `INV-PHYS-POST-PLAN-COSMO-SR-FIRST-LIVE-SEAM-TRANCHE-v0` | `physics` | `seams` | Post-plan COSMO-SR first live seam tranche | `CURRENT` | `formal/docs/release/POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_first_live_seam_tranche_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-PHYSICS-ADVANCEMENT-TARGET-MAP-v0` | Measures the first post-plan COSMO-SR execution tranche against the sole authorized executable seam path and records that the bounded Cycle07 run leaves the seam non-promoted and therefore does not justify rerouting or master-action reclassification. |
| `INV-PHYS-POST-PLAN-QM-FIRST-THEOREM-GAP-TRANCHE-v0` | `physics` | `pillars` | Post-plan QM first theorem-gap tranche | `CURRENT` | `formal/docs/release/POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_qm_first_theorem_gap_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-COSMO-SR-FIRST-LIVE-SEAM-TRANCHE-v0` | Measures the first post-plan theorem-gap-side tranche against `ROW-PILLAR-QM-001` and records that the current QM packet-04 route remains non-promoted under live row truth. |
| `INV-PHYS-POST-PLAN-SEAM-REROUTE-REASSESSMENT-v0` | `physics` | `seams` | Post-plan seam reroute reassessment | `CURRENT` | `formal/docs/release/POST_PLAN_SEAM_REROUTE_REASSESSMENT_20260418_v0.json` | `formal/output/reports/post_plan_seam_reroute_reassessment_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-QM-FIRST-THEOREM-GAP-TRANCHE-v0` | Reassesses seam eligibility after the first post-plan theorem-gap tranche and records that no reroute is justified because no upstream row movement was earned. |
| `INV-PHYS-POST-PLAN-MASTER-ACTION-REEVALUATION-v0` | `physics` | `synthesis_surface` | Post-plan master-action reevaluation | `CURRENT` | `formal/docs/release/POST_PLAN_MASTER_ACTION_REEVALUATION_20260418_v0.json` | `formal/output/reports/post_plan_master_action_reevaluation_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-SEAM-REROUTE-REASSESSMENT-v0` | Records that master action remains support-only and nonmoving because the post-plan program has not yet produced the upstream blocker movement required for bounded reevaluation. |
| `INV-PHYS-POST-PLAN-FINAL-INTEGRATION-REVIEW-v0` | `physics` | `synthesis_surface` | Post-plan final integration review | `CURRENT` | `formal/docs/release/POST_PLAN_FINAL_INTEGRATION_REVIEW_20260418_v0.json` | `formal/output/reports/post_plan_final_integration_review_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-MASTER-ACTION-REEVALUATION-v0` | Reviews the downstream post-plan posture after Phase 3 through Phase 5 and holds the existing non-claim integration state pending further blocker movement. |
| `INV-PHYS-QFT-GR-SLICEB-INC15-v0` | `physics` | `seams` | QFT-GR Slice B Increment15 bounded authority package | `CURRENT` | `formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_EXECUTION_PACKET_v0.md` | `formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_15_SYNTHESIS_NOTE_v0.md` | `formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment15_authority_mirror_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | Increment15 semantic-delta decision, execution, assessment, and synthesis bundle mirrored under authority hold invariance. |
| `INV-PHYS-COSMO-SR-PHASE2-AUTH-v0` | `physics` | `seams` | COSMO-SR Phase 2 seam authorization decision surface | `CURRENT` | `formal/docs/release/COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_20260418_v0.json` | `formal/output/reports/cosmo_sr_seam_authorization_activation_decision_20260418_v0.json` | `formal/python/tests/test_cosmo_sr_seam_authorization_activation_decision_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | Pins `ROW-SEAM-COSMO-SR-001` as the single non-frozen Phase 2 candidate while fail-closing actual activation under the current discovery-review hold. |
| `INV-PHYS-COSMO-SR-PHASE2-HOLD-RESOLUTION-v0` | `physics` | `seams` | COSMO-SR Phase 2 discovery hold-resolution surface | `CURRENT` | `formal/docs/release/COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_20260418_v0.json` | `formal/output/reports/cosmo_sr_discovery_review_hold_resolution_20260418_v0.json` | `formal/python/tests/test_cosmo_sr_discovery_review_hold_resolution_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-COSMO-SR-PHASE2-AUTH-v0` | Narrows the review hold to further discovery expansion only and resolves it for conversion of the already selected single TGC-93 candidate. |
| `INV-PHYS-COSMO-SR-PHASE2-ACTIVATION-AUTH-v0` | `physics` | `seams` | COSMO-SR Phase 2 bounded activation authorization surface | `CURRENT` | `formal/docs/release/COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_20260418_v0.json` | `formal/output/reports/cosmo_sr_bounded_activation_authorization_20260418_v0.json` | `formal/python/tests/test_cosmo_sr_bounded_activation_authorization_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-COSMO-SR-PHASE2-HOLD-RESOLUTION-v0` | Converts the resolved held decision into one bounded non-live COSMO-SR activation authorization with single-path scope and no execution-live token. |
| `INV-PHYS-POST-PLAN-COSMO-SR-BOUNDED-CONTINUATION-FAMILY-v0` | `physics` | `seams` | Post-plan COSMO-SR bounded continuation family | `CURRENT` | `formal/docs/release/POST_PLAN_COSMO_SR_BOUNDED_CONTINUATION_FAMILY_20260419_v0.json` | `formal/output/reports/post_plan_cosmo_sr_bounded_continuation_family_20260419_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_bounded_continuation_family_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-COSMO-SR-FIRST-LIVE-SEAM-TRANCHE-v0` | Consumes the already nonpromoted first live COSMO-SR seam tranche together with the Cycle06-to-07 synthesis boundary and the historical Cycle08 candidate surface to determine whether a genuinely new machine-pinned continuation payload exists, and currently closes the seam explicitly because no live Cycle08 target, artifact, or gate is pinned. |
| `INV-PHYS-POST-PLAN-COSMO-SR-CYCLE08-OR-LATER-PAYLOAD-UNLOCK-SURFACE-v0` | `physics` | `seams` | Post-plan COSMO-SR Cycle08-or-later payload unlock surface | `CURRENT` | `formal/docs/release/POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_20260419_v0.json` | `formal/output/reports/post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-POST-PLAN-COSMO-SR-BOUNDED-CONTINUATION-FAMILY-v0` | Keeps the exhausted COSMO-SR seam fail-closed until exactly one Cycle08-or-later payload tuple is machine-pinned, and currently records a locked prerequisite-only state because no such payload exists yet. |
| `INV-PHYS-QM-STAT-APPROVAL-RECORDATION-EXECUTION-v0` | `physics` | `seams` | QM-STAT approval-recordation execution surface | `CURRENT` | `formal/docs/release/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORDATION_EXECUTION_20260419_v0.json` | `formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_20260419_v0.json` | `formal/python/tests/test_qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_recordation_execution_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-EXECUTABLE-PATH-NORMALIZATION-v0` | Adds one bounded write surface for the QM-STAT policy-standard approval blocker; the surface now carries a complete recorded approval tuple, propagates the lane into the post-approval anti-alias blocker state, and still does not itself authorize restart execution. |
| `INV-PHYS-SEAM-EXECUTABLE-PATH-NORMALIZATION-v0` | `physics` | `seams` | Seam executable-path normalization surface | `CURRENT` | `formal/docs/release/SEAM_EXECUTABLE_PATH_NORMALIZATION_20260418_v0.json` | `formal/output/reports/seam_executable_path_normalization_20260418_v0.json` | `formal/python/tests/test_seam_executable_path_normalization_report.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | Normalizes all current seams into one executable-path model and pins `SEAM-COSMO-SR` as the single authorized non-live executable seam while preserving QM-STAT blocked, QFT-GR external-hold, mirror-only, and closed-monitoring path classes. |
| `INV-PHYS-SCALAR-SUBMISSION-SUPPORT-v0` | `physics` | `publication_support` | Scalar Paper 1 submission support package | `CURRENT` | `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_v0.md` | `formal/output/toe_qft_scalar_route_submission_support_package_checkpoint_v0.json` | `formal/python/tests/test_toe_qft_scalar_route_submission_support_package_gate.py` | `VALIDATED` | `P-POLICY` | `INV-PHYS-ROADMAP-v0` | Support-bundle coherence layer with explicit owner-confirmation blocker tracking. |
| `INV-PHYS-WORK-EQ-COMPENDIUM-v0` | `physics` | `synthesis_surface` | Centralized math/physics work and equations compendium | `CURRENT` | `formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` | `USED` | `P-POLICY` | `INV-PHYS-ROADMAP-v0` | Physics-facing entrypoint to unified equations/work ledger. |

## 4) Validation status

Validation interpretation:
- A row is considered validation-complete only if source, checkpoint, and gate pointers are all pinned and present in canonical surfaces.
- `OPEN_PROOF_DEBT` rows may have valid checkpoint/gate pointers while still carrying unresolved discharge obligations.

Validation rollup (v0 draft):
- `validated_rows`: 66
- `used_rows`: 53
- `open_proof_debt_rows`: 2
- `bounded_nonclaim_rows`: 5

Unresolved dependency highlights:
- `INV-PHYS-EM-U1-MICRO21` depends on distributional authorization closure in downstream EM U1 route closure attempts.
- `INV-MATH-PROOF-DEBT-BURNDOWN-c04` remains open until tracked GapID debt rows clear without policy drift.

## 5) Open debt / unresolved items

Proof debt:
- `INV-MATH-PROOF-DEBT-BURNDOWN-c04` (`OPEN_PROOF_DEBT`)
- linked closeout surfaces: `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md` and `formal/output/proof_debt_burndown_checkpoint_cycle05_v0.json`

Seam debt:
- Global seam physics completion remains non-closed in current audit posture.
- canonical status pointer: `formal/docs/release/REPO_STATUS_AUDIT_20260315_v0.md`

Empirical debt:
- Packet and discriminator coverage is active but remains bounded and mixed-progress at repository-wide posture.

Packaging/publication debt:
- Scalar submission lane is marked ready for bounded package preparation, but this does not supersede non-claim boundaries.
- Scalar submission support package is ready with owner confirmation still pending for the final corresponding-contact email.

## 6) Crosswalk

| inventory item | canonical source file | checkpoint | gate |
| --- | --- | --- | --- |
| `INV-MATH-ASSUMPTION-REGISTRY-v1` | `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` |
| `INV-MATH-CLAIM-TAXONOMY-v0` | `formal/docs/paper/CLAIM_TAXONOMY_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_toe_closure_and_action_promotion_standards_gate.py` |
| `INV-MATH-LEAN-QFT-SCALAR-AGGREGATE-v0` | `formal/toe_formal/ToeFormal.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QMSTAT-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `formal/toe_formal/ToeFormal/Derivation/QMSTATPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-v0` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_TransportResidualPackage.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QMSTAT-EVOLUTION-TRANSPORT-HYPOTHESES-ADJUDICATION-v0` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_EvolutionTransportHypothesesAdjudication.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QMSTAT-EVOLUTION-TRANSPORT-SEMANTIC-BRIDGE-v0` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_EvolutionTransportSemanticBridge.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QM-EVOLUTION-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `formal/toe_formal/ToeFormal/Derivation/QMEvolutionPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-EM-QFT-PHYSICS-BLOCKER-PROTOCOL-ROW-v0` | `formal/toe_formal/ToeFormal/Derivation/EMQFTPhysicsBlockerProtocolRow.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-EM-QFT-SHARED-DYNAMICS-RESIDUAL-UNIFICATION-BRIDGE-v0` | `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SharedDynamicsResidualUnificationBridge.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-EM-QFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-v0` | `formal/toe_formal/ToeFormal/Bridges/EM_QFT_InterfaceAlignmentSemanticBridge.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-EM-QFT-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `formal/toe_formal/ToeFormal/Derivation/EMQFTPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-MASTER-ACTION-RETAINED-ASSUMPTION-CITATION-USAGE-v0` | `formal/toe_formal/ToeFormal/Derivation/MasterActionRetainedAssumptionCitationUsage.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-MASTER-ACTION-CITATION-LANGUAGE-AUDIT-v0` | `formal/toe_formal/ToeFormal/Derivation/MasterActionCitationLanguageAudit.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-MASTER-ACTION-DEPENDENCY-GRAPH-REVIEW-v0` | `formal/toe_formal/ToeFormal/Derivation/MasterActionDependencyGraphReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-MASTER-ACTION-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0` | `formal/toe_formal/ToeFormal/Derivation/MasterActionRetainedBlockerPrioritizationReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-PROTOCOL-ROW-v0` | `formal/toe_formal/ToeFormal/Derivation/QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QFTGR-STRESS-ENERGY-SOURCE-MAP-v0` | `formal/toe_formal/ToeFormal/Bridges/QFT_GR_StressEnergyExpectationSourceMap.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-QFTGR-RESIDUAL-ONLY-SEMANTIC-OBSTRUCTION-v0` | `formal/toe_formal/ToeFormal/Bridges/QFT_GR_StressEnergySourceMapResidualOnlyObstruction.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SR-COSMOLOGY-REGIME-TRANSPORT-v0` | `formal/toe_formal/ToeFormal/Bridges/SR_CosmologyRegimeTransport.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SR-COSMOLOGY-GLOBAL-BRIDGE-SEMANTIC-MAP-OBSTRUCTION-v0` | `formal/toe_formal/ToeFormal/Bridges/SR_CosmologyGlobalBridgeSemanticMapObstruction.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SR-COSMOLOGY-POST-BUDGET-CROSS-PILLAR-REVIEW-v0` | `formal/toe_formal/ToeFormal/Derivation/SRCosmologyPostBudgetCrossPillarReview.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SCALAR-A1A26-ENDPOINT-REPRESENTATION-SEMANTICS-v0` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointRepresentationSemanticsObligation.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SCALAR-A1A27-ENDPOINT-CONVERGENCE-CONSISTENCY-v0` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointConvergenceConsistencyObligation.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SCALAR-A1A28-ENDPOINT-ORIENTATION-TRACE-v0` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointOrientationTraceCompatibilityObligation.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SCALAR-A1A29-REFINED-ENDPOINT-SOURCE-v0` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianRefinedEndpointSourceAssembly.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SCALAR-A1A30-REMAINING-NONENDPOINT-SPLIT-v0` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianRemainingNonEndpointObligationSplit.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-MATH-SCALAR-A1A31-RAW-IBP-GREEN-PACKAGE-v0` | `formal/toe_formal/ToeFormal/QFT/ContinuumSpatialGraphLaplacianRawIBPGreenConvergencePackage.lean` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-PHYS-ROADMAP-v0` | `formal/docs/paper/PHYSICS_ROADMAP_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` |
| `INV-PHYS-STRICT-DERIVATION-OBLIGATION-MAP-v0` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `State_of_the_Theory.md` | `formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py` |
| `INV-PHYS-SCALAR-QFT-PHASE0-BASELINE-CONTRACT-v0` | `formal/docs/lanes/SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0.md` | `formal/output/reports/scalar_qft_phase0_baseline_acceptance_contract_v0.json` | `formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py` |
| `INV-PHYS-FREE-SCALAR-WITNESS-FIDELITY-AUDIT-v0` | `formal/docs/lanes/TOE_CANDIDATE_FREE_SCALAR_WITNESS_FIDELITY_AUDIT_v0.md` | `formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md` | `formal/toe_formal/lakefile.toml` |
| `INV-PHYS-EXTERNAL-BENCHMARK-REGISTRY-v0` | `formal/docs/lanes/EXTERNAL_PHYSICS_BENCHMARK_REGISTRY_v0.md` | `formal/output/reports/external_physics_benchmark_registry_v0.json` | `formal/python/tests/test_external_physics_benchmark_registry_gate.py` |
| `INV-PHYS-DEEP-MATURITY-PROGRAM-v0` | `formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md` | `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json` | `formal/python/tests/test_pillar_deep_maturity_program_gate.py` |
| `INV-PHYS-SEAM-CLASSB-INVENTORY-v0` | `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_toe_master_action_class_b_inventory_gate.py` |
| `INV-PHYS-QFT-GR-PACKET41-SUCCESSOR-PACKAGE-v0` | `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_v0.md` | `formal/output/toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0.json` | `formal/python/tests/test_toe_qft_gr_seam_packet41_successor_discriminator_package_gate.py` |
| `INV-PHYS-QM-STAT-RL10-COMP-ANALYSIS-PACKET01-v0` | `formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md` | `formal/output/qm_stat_rl10_computational_analysis_packet_01_v0.json` | `formal/python/tests/test_qm_stat_rl10_computational_analysis_packet_01_gate.py` |
| `INV-PHYS-TOE-MASTER-ACTION-COMP-ANALYSIS-PACKET01-v0` | `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md` | `formal/output/toe_master_action_computational_analysis_packet_01_v0.json` | `formal/python/tests/test_toe_master_action_computational_analysis_packet_01_gate.py` |
| `INV-PHYS-TOE-MASTER-ACTION-COMP-ANALYSIS-PACKET01-REFINEMENT01-v0` | `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_v0.md` | `formal/output/toe_master_action_computational_analysis_packet_01_refinement_01_v0.json` | `formal/python/tests/test_toe_master_action_computational_analysis_packet_01_refinement_01_gate.py` |
| `INV-PHYS-TOE-MASTER-ACTION-PACKET01-TRANSPORT-BINDING-RECOVERY-v0` | `formal/docs/release/MASTER_ACTION_PACKET_01_TRANSPORT_BINDING_RECOVERY_20260418_v0.json` | `formal/output/reports/master_action_packet_01_transport_binding_recovery_20260418_v0.json` | `formal/python/tests/test_master_action_packet_01_transport_binding_recovery_report.py` |
| `INV-PHYS-DERIVATION-CHAIN-TRANSPORT-STANDARDIZATION-v0` | `formal/docs/release/DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_20260418_v0.json` | `formal/output/reports/derivation_chain_transport_standardization_20260418_v0.json` | `formal/python/tests/test_derivation_chain_transport_standardization_report.py` |
| `INV-PHYS-FINAL-NONCLAIM-INTEGRATION-GATE-v0` | `formal/docs/release/FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_20260418_v0.json` | `formal/output/reports/final_nonclaim_integration_promotion_gate_20260418_v0.json` | `formal/python/tests/test_final_nonclaim_integration_promotion_gate_report.py` |
| `INV-PHYS-POST-PLAN-CONSOLIDATION-MEMO-v0` | `formal/docs/release/POST_PLAN_CONSOLIDATION_MEMO_20260418_v0.md` | `formal/output/reports/final_nonclaim_integration_promotion_gate_20260418_v0.json` | `formal/python/tests/test_state_theory_dag.py` |
| `INV-PHYS-POST-PLAN-PHYSICS-ADVANCEMENT-PROGRAM-v0` | `formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md` | `formal/output/reports/blocker_burn_dashboard_20260416_v0.json` | `formal/python/tests/test_state_theory_dag.py` |
| `INV-PHYS-POST-PLAN-OBJECTIVE-QUALITY-COMPLETION-PROGRAM-v0` | `formal/docs/release/POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_PROGRAM_20260418_v0.md` | `formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json` | `formal/python/tests/test_post_plan_objective_quality_physics_completion_queue_report.py` |
| `INV-PHYS-POST-PLAN-REMAINING-PHYSICS-EXECUTION-ORDER-v0` | `formal/docs/release/POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_20260419_v0.json` | `formal/output/reports/post_plan_remaining_physics_execution_order_20260419_v0.json` | `formal/python/tests/test_post_plan_remaining_physics_execution_order_report.py` |
| `INV-PHYS-POST-PLAN-COSMO-SR-SELECTED-CONTINUATION-FAMILY-v0` | `formal/docs/release/POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_20260419_v0.json` | `formal/output/reports/post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_selected_continuation_family_report.py` |
| `INV-PHYS-POST-PLAN-COSMO-SR-SELECTED-CONTINUATION-EXECUTION-v0` | `formal/docs/release/POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_20260419_v0.json` | `formal/output/reports/post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_selected_continuation_execution_report.py` |
| `INV-PHYS-POST-PLAN-ORDERED-THEOREM-GAP-CONTINUATION-TRANCHE-v0` | `formal/docs/release/POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_20260419_v0.json` | `formal/output/reports/post_plan_ordered_theorem_gap_continuation_tranche_20260419_v0.json` | `formal/python/tests/test_post_plan_ordered_theorem_gap_continuation_tranche_report.py` |
| `INV-PHYS-POST-PLAN-OBJECTIVE-QUALITY-COMPLETION-QUEUE-v0` | `formal/docs/release/POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_20260418_v0.json` | `formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json` | `formal/python/tests/test_post_plan_objective_quality_physics_completion_queue_report.py` |
| `INV-PHYS-POST-PLAN-COSMO-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `formal/docs/release/POST_PLAN_COSMO_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_cosmo_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_cosmo_theorem_gap_completion_tranche_report.py` |
| `INV-PHYS-POST-PLAN-STAT-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_stat_theorem_gap_completion_tranche_report.py` |
| `INV-PHYS-POST-PLAN-GR-DORMANT-NEW-STRUCTURE-COMPLETION-TRANCHE-v0` | `formal/docs/release/POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_gr_dormant_new_structure_completion_tranche_report.py` |
| `INV-PHYS-POST-PLAN-DEEPER-BLOCKER-DEFINITION-REVIEW-SUCCESSOR-TRANCHE-v0` | `formal/docs/release/POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_deeper_blocker_definition_review_successor_tranche_report.py` |
| `INV-PHYS-POST-PLAN-BOUNDED-BLOCKER-DEFINITION-TEST-PACKET-CHAIN-v0` | `formal/docs/release/POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_20260418_v0.json` | `formal/output/reports/post_plan_bounded_blocker_definition_test_packet_chain_20260418_v0.json` | `formal/python/tests/test_post_plan_bounded_blocker_definition_test_packet_chain_report.py` |
| `INV-PHYS-POST-PLAN-AUTHORITY-COUPLING-REVIEW-PATH-v0` | `formal/docs/release/POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_20260418_v0.json` | `formal/output/reports/post_plan_authority_coupling_review_path_20260418_v0.json` | `formal/python/tests/test_post_plan_authority_coupling_review_path_report.py` |
| `INV-PHYS-POST-PLAN-BOUNDED-COUPLING-REFINEMENT-PACKET-CHAIN-v0` | `formal/docs/release/POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_20260418_v0.json` | `formal/output/reports/post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json` | `formal/python/tests/test_post_plan_bounded_coupling_refinement_packet_chain_report.py` |
| `INV-PHYS-POST-PLAN-RECOMPUTE-MONITORING-PATH-v0` | `formal/docs/release/POST_PLAN_RECOMPUTE_MONITORING_PATH_20260418_v0.json` | `formal/output/reports/post_plan_recompute_monitoring_path_20260418_v0.json` | `formal/python/tests/test_post_plan_recompute_monitoring_path_report.py` |
| `INV-PHYS-RECOMPUTE-LIVE-WRITEBACK-CONTRACT-v0` | `formal/docs/release/RECOMPUTE_LIVE_WRITEBACK_CONTRACT_20260418_v0.json` | `formal/output/reports/recompute_live_writeback_contract_20260418_v0.json` | `formal/python/tests/test_recompute_live_writeback_contract_report.py` |
| `INV-PHYS-RECOMPUTE-DRY-RUN-EXECUTION-INSPECTION-v0` | `formal/docs/release/RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_20260418_v0.json` | `formal/output/reports/recompute_dry_run_execution_inspection_20260418_v0.json` | `formal/python/tests/test_recompute_dry_run_execution_inspection_report.py` |
| `INV-PHYS-RECOMPUTE-LIVE-WRITEBACK-BASELINE-APPROVAL-v0` | `formal/docs/release/RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_20260418_v0.json` | `formal/output/reports/recompute_live_writeback_baseline_approval_20260418_v0.json` | `formal/python/tests/test_recompute_live_writeback_baseline_approval_report.py` |
| `INV-PHYS-POST-PLAN-POST-CASCADE-CLOSURE-REVIEW-v0` | `formal/docs/release/POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_20260418_v0.json` | `formal/output/reports/post_plan_post_cascade_closure_review_20260418_v0.json` | `formal/python/tests/test_post_plan_post_cascade_closure_review_report.py` |
| `INV-PHYS-POST-PLAN-QFT-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `formal/docs/release/POST_PLAN_QFT_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_qft_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_qft_theorem_gap_completion_tranche_report.py` |
| `INV-PHYS-POST-PLAN-EM-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `formal/docs/release/POST_PLAN_EM_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_em_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_em_theorem_gap_completion_tranche_report.py` |
| `INV-PHYS-POST-PLAN-SR-THEOREM-GAP-COMPLETION-TRANCHE-v0` | `formal/docs/release/POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_sr_theorem_gap_completion_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_sr_theorem_gap_completion_tranche_report.py` |
| `INV-PHYS-POST-PLAN-PROGRAM-STATE-CONVERSION-REVIEW-WRAPPER-v0` | `formal/docs/release/POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_20260418_v0.json` | `formal/output/reports/post_plan_program_state_conversion_review_wrapper_20260418_v0.json` | `formal/python/tests/test_post_plan_program_state_conversion_review_wrapper_report.py` |
| `INV-PHYS-POST-PLAN-POST-CASCADE-EXPLICIT-EXHAUSTION-DECISION-v0` | `formal/docs/release/POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_20260419_v0.json` | `formal/output/reports/post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json` | `formal/python/tests/test_post_plan_post_cascade_explicit_exhaustion_decision_report.py` |
| `INV-PHYS-POST-PLAN-POST-CASCADE-SUCCESSOR-FAMILY-ELIGIBILITY-REVIEW-v0` | `formal/docs/release/POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json` | `formal/output/reports/post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json` | `formal/python/tests/test_post_plan_post_cascade_successor_family_eligibility_review_report.py` |
| `INV-PHYS-POST-PLAN-PHYSICS-ADVANCEMENT-TARGET-MAP-v0` | `formal/docs/release/POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_20260418_v0.json` | `formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json` | `formal/python/tests/test_post_plan_physics_advancement_target_map_report.py` |
| `INV-PHYS-POST-PLAN-COSMO-SR-FIRST-LIVE-SEAM-TRANCHE-v0` | `formal/docs/release/POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_cosmo_sr_first_live_seam_tranche_report.py` |
| `INV-PHYS-POST-PLAN-QM-FIRST-THEOREM-GAP-TRANCHE-v0` | `formal/docs/release/POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_20260418_v0.json` | `formal/output/reports/post_plan_qm_first_theorem_gap_tranche_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` |
| `INV-PHYS-POST-PLAN-SEAM-REROUTE-REASSESSMENT-v0` | `formal/docs/release/POST_PLAN_SEAM_REROUTE_REASSESSMENT_20260418_v0.json` | `formal/output/reports/post_plan_seam_reroute_reassessment_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` |
| `INV-PHYS-POST-PLAN-MASTER-ACTION-REEVALUATION-v0` | `formal/docs/release/POST_PLAN_MASTER_ACTION_REEVALUATION_20260418_v0.json` | `formal/output/reports/post_plan_master_action_reevaluation_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` |
| `INV-PHYS-POST-PLAN-FINAL-INTEGRATION-REVIEW-v0` | `formal/docs/release/POST_PLAN_FINAL_INTEGRATION_REVIEW_20260418_v0.json` | `formal/output/reports/post_plan_final_integration_review_20260418_v0.json` | `formal/python/tests/test_post_plan_phase3_to_phase6_reports.py` |
| `INV-PHYS-QFT-GR-SLICEB-INC15-v0` | `formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_EXECUTION_PACKET_v0.md` | `formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_15_SYNTHESIS_NOTE_v0.md` | `formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment15_authority_mirror_gate.py` |
| `INV-PHYS-SCALAR-SUBMISSION-SUPPORT-v0` | `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_SUPPORT_PACKAGE_v0.md` | `formal/output/toe_qft_scalar_route_submission_support_package_checkpoint_v0.json` | `formal/python/tests/test_toe_qft_scalar_route_submission_support_package_gate.py` |
| `INV-PHYS-PREDICTION-SCOREBOARD-v0` | `formal/output/prediction_first_scoreboard_v0.json` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_prediction_first_scoreboard_gate.py` |
| `INV-MATH-PHYS-WORK-EQ-COMPENDIUM-v0` | `formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md` | `formal/output/repo_status_audit_20260315_checkpoint_v0.json` | `formal/python/tests/test_repo_status_audit_20260315_gate.py` |

## Canonical pointers for authority surfaces

- Compact authority surface pointer: `State_of_the_Theory.md`
- Centralized math/physics/equations compendium pointer: `formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md`
- Live seam SLA policy pointer: `formal/docs/release/SEAM_RESOLUTION_SLA_POLICY_20260416_v0.md`
- Live seam contradiction policy pointer: `formal/docs/release/SCIENCE_MATURITY_CONTRADICTION_REPORT_POLICY_20260416_v0.md`
- Live seam contradiction report pointer: `formal/output/reports/science_maturity_contradiction_report_20260416_v0.json`
- Live seam contradiction gate pointer: `formal/python/tests/test_science_maturity_contradiction_report_live_gate.py`
- Changelog archive summary pointer: `archive/docs/release/TOE_CHANGELOG_ARCHIVE_v0.md`
- Packet history archive summary pointer: `archive/docs/release/TOE_PACKET_HISTORY_ARCHIVE_v0.md`
- Seam history archive summary pointer: `archive/docs/release/TOE_SEAM_HISTORY_ARCHIVE_v0.md`
- Archived history extract pointer: `archive/State_of_the_Theory_ARCHIVED_HISTORY_EXTRACT_v0.md`

## Transitional compatibility pointers (state-pin migration tranche)

- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md`
- `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean`
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean`
- `formal/python/tests/test_em_qft_seam_promotion_cycle01_theorem_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`
- `formal/python/tests/test_em_qft_seam_promotion_cycle02_discharge_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`
- `formal/python/tests/test_em_qft_seam_promotion_cycle03_class_flip_gate.py`
- `formal/docs/release/PREDICTION_FIRST_HYPOTHESIS_TEMPLATE_v0.md`
- `formal/docs/lanes/HYPOTHESIS_OV_DR_BR_PACKET02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md`
- `formal/python/tests/test_qm_empirical_packet_02_decision_record_gate.py`
- `formal/python/tests/test_gr_empirical_packet_02_decision_record_gate.py`
- `formal/python/tests/test_stat_empirical_packet_02_decision_record_gate.py`
- `formal/python/tests/test_cosmo_empirical_packet_02_decision_record_gate.py`
- `formal/python/tests/test_em_empirical_packet_02_decision_record_gate.py`
- `formal/python/tests/test_qft_empirical_packet_02_decision_record_gate.py`
- `formal/python/tests/test_sr_empirical_packet_02_decision_record_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_02_v0.md`
- `formal/python/tests/test_qm_empirical_comparison_packet_02_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`
- `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`
- `formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py`
- `formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py`
- `formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_QM_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- `formal/python/tests/test_qm_m4_seam_closure_promotion_cycle01_gate.py`
- `formal/python/tests/test_gr_m4_seam_closure_promotion_cycle01_gate.py`
- `formal/python/tests/test_stat_m4_seam_closure_promotion_cycle01_gate.py`
- `formal/python/tests/test_cosmo_m4_seam_closure_promotion_cycle01_gate.py`
- `formal/python/tests/test_em_m4_seam_closure_promotion_cycle01_gate.py`
- `formal/python/tests/test_qft_m4_seam_closure_promotion_cycle01_gate.py`
- `QFT_M4_STATUS_v0: COMPLETE_BOUNDED_v0`
- `QFT_M4_LIVE_BLOCKER_QUALIFIER_v0: LIVE_THEOREM_GAP_OPEN_v0`
- `QFT_M4_PROMOTION_READINESS_v0: CROSS_PILLAR_SEAM_BUNDLE_PINNED_v0`
- `QFT_M4_SEAM_CLOSURE_ARTIFACT_v0: qft_m4_seam_closure_promotion_cycle01_v0`
- `QFT_M4_SEAM_CLOSURE_SHA256_v0: 5f01e0e528c0c46748f0059994f026142c29f51103ea0a30afb9ddf51af6fbd4`
- `QFT_M4_SEAM_CLOSURE_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_m4_seam_closure_promotion_cycle01_v0.json`
- `QFT_M3_STATUS_v0: COMPLETE_BOUNDED_v0`
- `QFT_M3_PROMOTION_READINESS_v0: FIRST_DISCRIMINATOR_CLOSED_AND_PROMOTED_v0`
- `QFT_M3_COMPLETION_ARTIFACT_v0: qft_m3_completion_promotion_cycle01_v0`
- `QFT_M3_COMPLETION_SHA256_v0: f0dbe27f97b08b2d9f652f21d914d2e9fdb52397f1c1aee8d5ea6b7428b88f3c`
- `QFT_M3_COMPLETION_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/docs/paper/DERIVATION_TARGET_QFT_M3_COMPLETION_PROMOTION_v0.md`
- `formal/output/qft_m3_completion_promotion_cycle01_v0.json`
- `formal/python/tests/test_qft_m3_completion_promotion_cycle01_gate.py`
- `QFT_M2_ANALYTIC_COMPLETENESS_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `QFT_M2_ANALYTIC_COMPLETENESS_ARTIFACT_v0: qft_m2_analytic_completeness_scaffold_cycle01_v0`
- `QFT_M2_ANALYTIC_COMPLETENESS_SHA256_v0: 77131b316529184d14401ed586ef698538b96491e1def62f03e20edd3cced13e`
- `QFT_M2_ANALYTIC_COMPLETENESS_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_m2_analytic_completeness_scaffold_cycle01_v0.json`
- `formal/python/tests/test_qft_m2_analytic_completeness_scaffold_cycle01_gate.py`
- `QFT_M2_CANONICAL_EQUIVALENCE_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `QFT_M2_CANONICAL_EQUIVALENCE_ARTIFACT_v0: qft_m2_canonical_equivalence_scaffold_cycle01_v0`
- `QFT_M2_CANONICAL_EQUIVALENCE_SHA256_v0: 88891e4413ce6bb767c0f9d1eb04a6958514d45d6109354340d157930a67a7bc`
- `QFT_M2_CANONICAL_EQUIVALENCE_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_m2_canonical_equivalence_scaffold_cycle01_v0.json`
- `formal/python/tests/test_qft_m2_canonical_equivalence_scaffold_cycle01_gate.py`
- `QFT_M2_ASSUMPTION_MINIMIZATION_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `QFT_M2_ASSUMPTION_MINIMIZATION_ARTIFACT_v0: qft_m2_assumption_minimization_scaffold_cycle01_v0`
- `QFT_M2_ASSUMPTION_MINIMIZATION_SHA256_v0: 8ac9c8f558e4608ee08d34b5ac6e38f18503fc5f5909f65bcb2c2a969b66948c`
- `QFT_M2_ASSUMPTION_MINIMIZATION_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_m2_assumption_minimization_scaffold_cycle01_v0.json`
- `formal/python/tests/test_qft_m2_assumption_minimization_scaffold_cycle01_gate.py`
- `QFT_M2_LITERATURE_ALIGNMENT_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `QFT_M2_LITERATURE_ALIGNMENT_ARTIFACT_v0: qft_m2_literature_alignment_scaffold_cycle01_v0`
- `QFT_M2_LITERATURE_ALIGNMENT_SHA256_v0: 7c59d4c9758cba8f1f2919fa2eab41931aa180d65483caddb5b5ed0a078ef285`
- `QFT_M2_LITERATURE_ALIGNMENT_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_m2_literature_alignment_scaffold_cycle01_v0.json`
- `formal/python/tests/test_qft_m2_literature_alignment_scaffold_cycle01_gate.py`
- `QFT_M2_STATUS_v0: COMPLETE_BOUNDED_v0`
- `QFT_M2_COMPLETION_ARTIFACT_v0: qft_m2_completion_promotion_cycle01_v0`
- `QFT_M2_COMPLETION_SHA256_v0: 4da23bb3d4938d961905f836465a7ecf91fdcbb9418a2a7be1cab58f950fe232`
- `QFT_M2_COMPLETION_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_m2_completion_promotion_cycle01_v0.json`
- `formal/python/tests/test_qft_m2_completion_promotion_cycle01_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle01_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_SHA256_v0: e577ce28c1ec133d1fb81fd4f02c86cb8cbc51ff2d376fb28007d85e31160d3a`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle01_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE02_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle02_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE02_SHA256_v0: 016c677d58dc07cac5dd07ecb990d2146668b5b24174d20db96ce9efbb2f2c84`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE02_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle02_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle02_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle03_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_SHA256_v0: 2a0abd347388e0b75407da1a859503405afa49f45a489b4eaca0e1a68fc0263d`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE03_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle03_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle03_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE04_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle04_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE04_SHA256_v0: 88694de01be7d77e4da94d9f96a1f199380dc03abd26467f792c183ef3f50f87`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE04_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle04_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle04_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE05_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle05_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE05_SHA256_v0: 1b01ad0d9c251eaf03944c0bc2004e8a2818ff6be49a18bb94e37ea6d7bf6514`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE05_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle05_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle05_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE06_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle06_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE06_SHA256_v0: b4f4f44a67a4e59f2c2ea86ea2437cf46c429d6a97f73d4736809a1a16be00d6`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE06_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle06_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle06_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE07_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle07_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE07_SHA256_v0: 3dda804c32a267996ea7053ac825d4d4e3fa5d76efd08ba810e01af7cec0aaed`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE07_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle07_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle07_gate.py`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE08_ARTIFACT_v0: qft_evidence_diversification_checkpoint_cycle08_v0`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE08_SHA256_v0: 2935256b2002f6962c5a288dd4a08497a1366e5c1bee09f87fef91cbb4d73234`
- `QFT_EVIDENCE_DIVERSIFICATION_CHECKPOINT_CYCLE08_GATE_v0: ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED`
- `formal/output/qft_evidence_diversification_checkpoint_cycle08_v0.json`
- `formal/python/tests/test_qft_evidence_diversification_checkpoint_coupling_cycle08_gate.py`
- `formal/python/tests/test_sr_m4_seam_closure_promotion_cycle01_gate.py`
- `formal/docs/release/TOE_SEAM_STATUS_SEMANTICS_STANDARD_v0.md`
- `formal/python/tests/test_toe_seam_status_split_gate.py`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET03_MATRIX_v0.json`
- `formal/python/tests/test_foundational_empirical_packet03_matrix_consistency_gate.py`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET04_MATRIX_v0.json`
- `formal/python/tests/test_foundational_empirical_packet04_matrix_consistency_gate.py`
- `formal/python/tests/test_foundational_empirical_packet04_decision_policy_gate.py`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json`
- `formal/docs/release/FOUNDATIONAL_EMPIRICAL_PACKET05_PROGRESSION_POLICY_v0.md`
- `formal/python/tests/test_foundational_empirical_packet05_matrix_consistency_gate.py`
- `formal/python/tests/test_foundational_empirical_packet05_progression_policy_gate.py`
- `formal/docs/release/FOUNDATIONAL_EMPIRICAL_PACKET05_OVERRIDE_POLICY_v0.md`
- `formal/docs/paper/FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET_MATRIX_v0.json`
- `formal/python/tests/test_foundational_empirical_packet_matrix_consistency_gate.py`
- `formal/python/tests/test_foundational_empirical_packet_progression_policy_gate.py`
- `formal/python/tests/test_foundational_empirical_packet05_override_policy_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_03_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_03_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_03_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_COMPARISON_PACKET_03_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_COMPARISON_PACKET_03_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_COMPARISON_PACKET_03_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_03_v0.md`
- `formal/python/tests/test_qm_empirical_comparison_packet_03_gate.py`
- `formal/python/tests/test_gr_empirical_comparison_packet_03_gate.py`
- `formal/python/tests/test_stat_empirical_comparison_packet_03_gate.py`
- `formal/python/tests/test_cosmo_empirical_comparison_packet_03_gate.py`
- `formal/python/tests/test_em_empirical_comparison_packet_03_gate.py`
- `formal/python/tests/test_qft_empirical_comparison_packet_03_gate.py`
- `formal/python/tests/test_sr_empirical_comparison_packet_03_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_04_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_04_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_04_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_COMPARISON_PACKET_04_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_COMPARISON_PACKET_04_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_COMPARISON_PACKET_04_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_04_v0.md`
- `formal/python/tests/test_qm_empirical_comparison_packet_04_gate.py`
- `formal/output/reports/qm_blocker_moving_tranche_20260411_v0.json`
- `formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json`
- `formal/output/reports/science_next_attack_class_selection_20260411_v0.json`
- `formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json`
- `formal/python/tests/test_qm_blocker_moving_control_stack_gate.py`
- `formal/output/reports/qm_stat_transport_residual_packet_20260411_v0.json`
- `formal/output/reports/qm_stat_transport_residual_ruling_20260411_v0.json`
- `formal/output/reports/science_post_direct_attack_class_decision_20260411_v0.json`
- `formal/python/tests/test_qm_stat_transport_residual_live_control_stack_gate.py`
- `formal/docs/release/ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_20260411_v0.json`
- `formal/output/reports/architecture_level_blocker_diagnosis_packet_20260411_v0.json`
- `formal/python/tests/test_architecture_level_blocker_diagnosis_live_gate.py`
- `formal/docs/release/ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET_20260411_v0.json`
- `formal/output/reports/architecture_seam_master_action_alignment_attack_class_packet_20260411_v0.json`
- `formal/python/tests/test_architecture_seam_master_action_alignment_live_gate.py`
- `formal/docs/release/ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_PACKET_EXECUTION_20260411_v0.json`
- `formal/output/reports/architecture_seam_master_action_alignment_packet_execution_20260411_v0.json`
- `formal/docs/release/ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_RULING_20260411_v0.json`
- `formal/output/reports/architecture_seam_master_action_alignment_ruling_20260411_v0.json`
- `formal/docs/release/SCIENCE_POST_ARCHITECTURE_ALIGNMENT_DECISION_20260411_v0.json`
- `formal/output/reports/science_post_architecture_alignment_decision_20260411_v0.json`
- `formal/python/tests/test_architecture_seam_master_action_alignment_execution_live_gate.py`
- `formal/docs/release/PROGRAM_POSTURE_REVIEW_PACKET_20260411_v0.json`
- `formal/output/reports/program_posture_review_packet_20260411_v0.json`
- `formal/python/tests/test_program_posture_review_live_gate.py`
- `formal/docs/release/POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION_20260411_v0.json`
- `formal/output/reports/post_posture_review_program_mode_transition_20260411_v0.json`
- `formal/python/tests/test_post_posture_review_program_mode_transition_live_gate.py`
- `formal/docs/release/BOUNDED_MEASUREMENT_REGIME_PILOT_EXECUTION_20260411_v0.json`
- `formal/output/reports/bounded_measurement_regime_pilot_execution_20260411_v0.json`
- `formal/docs/release/BOUNDED_MEASUREMENT_REGIME_PILOT_RULING_20260411_v0.json`
- `formal/output/reports/bounded_measurement_regime_pilot_ruling_20260411_v0.json`
- `formal/docs/release/POST_MEASUREMENT_REGIME_PILOT_DECISION_20260411_v0.json`
- `formal/output/reports/post_measurement_regime_pilot_decision_20260411_v0.json`
- `formal/python/tests/test_bounded_measurement_regime_pilot_live_gate.py`
- `formal/docs/release/REVISED_SIGNAL_DIAGNOSTIC_REGISTRATION_20260411_v0.json`
- `formal/output/reports/revised_signal_diagnostic_registration_20260411_v0.json`
- `formal/python/tests/test_revised_signal_diagnostic_registration_live_gate.py`
- `formal/docs/release/PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json`
- `formal/output/reports/program_state_conversion_review_20260411_v0.json`
- `formal/python/tests/test_program_state_conversion_review_live_gate.py`
- `formal/docs/release/DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json`
- `formal/output/reports/deeper_blocker_definition_review_20260411_v0.json`
- `formal/python/tests/test_deeper_blocker_definition_review_live_gate.py`
- `formal/docs/release/BLOCKER_BURN_DASHBOARD_POLICY_20260416_v0.md`
- `formal/output/reports/blocker_burn_dashboard_20260416_v0.json`
- `formal/python/tests/test_blocker_burn_dashboard_live_gate.py`
- `formal/docs/release/SCIENCE_GOVERNANCE_BUDGET_POLICY_20260416_v0.md`
- `formal/output/reports/science_governance_budget_20260416_v0.json`
- `formal/python/tests/test_science_governance_budget_live_gate.py`
- `formal/docs/release/SEAM_RESOLUTION_SLA_POLICY_20260416_v0.md`
- `formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json`
- `formal/python/tests/test_seam_resolution_sla_live_gate.py`
- `formal/docs/release/BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_20260411_v0.json`
- `formal/output/reports/bounded_blocker_definition_test_execution_20260411_v0.json`
- `formal/docs/release/BOUNDED_BLOCKER_DEFINITION_TEST_RULING_20260411_v0.json`
- `formal/output/reports/bounded_blocker_definition_test_ruling_20260411_v0.json`
- `formal/python/tests/test_bounded_blocker_definition_test_live_gate.py`
- `formal/docs/release/POST_BLOCKER_DEFINITION_TEST_DECISION_20260411_v0.json`
- `formal/output/reports/post_blocker_definition_test_decision_20260411_v0.json`
- `formal/python/tests/test_post_blocker_definition_test_decision_live_gate.py`
- `formal/docs/release/AUTHORITY_COUPLING_REVIEW_20260411_v0.json`
- `formal/output/reports/authority_coupling_review_20260411_v0.json`
- `formal/python/tests/test_authority_coupling_review_live_gate.py`
- `formal/docs/release/BOUNDED_COUPLING_REFINEMENT_PACKET_20260411_v0.json`
- `formal/output/reports/bounded_coupling_refinement_packet_20260411_v0.json`
- `formal/python/tests/test_bounded_coupling_refinement_packet_live_gate.py`
- `formal/docs/release/COUPLING_REFINEMENT_RULING_20260411_v0.json`
- `formal/output/reports/coupling_refinement_ruling_20260411_v0.json`
- `formal/python/tests/test_coupling_refinement_ruling_live_gate.py`
- `formal/docs/release/AUTHORITY_PROMOTION_REGISTRATION_20260411_v0.json`
- `formal/output/reports/authority_promotion_registration_20260411_v0.json`
- `formal/python/tests/test_authority_promotion_registration_live_gate.py`
- `formal/docs/release/RECOMPUTE_OBSERVATION_20260411_v0.json`
- `formal/output/reports/recompute_observation_20260411_v0.json`
- `formal/docs/release/POST_RECOMPUTE_OBSERVATION_20260411_v0.json`
- `formal/output/reports/post_recompute_observation_20260411_v0.json`
- `formal/python/tests/test_recompute_monitoring_live_gate.py`
- `formal/python/tests/test_gr_empirical_comparison_packet_04_gate.py`
- `formal/python/tests/test_stat_empirical_comparison_packet_04_gate.py`
- `formal/python/tests/test_cosmo_empirical_comparison_packet_04_gate.py`
- `formal/python/tests/test_em_empirical_comparison_packet_04_gate.py`
- `formal/python/tests/test_qft_empirical_comparison_packet_04_gate.py`
- `formal/python/tests/test_sr_empirical_comparison_packet_04_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_TOE_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_PACKET_01_EVIDENCE_PROMOTION_v0.md`
- `formal/python/tests/test_toe_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_toe_empirical_packet_01_evidence_promotion_gate.py`
- `formal/python/tests/test_qm_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_qm_empirical_packet_01_evidence_promotion_gate.py`
- `formal/python/tests/test_gr_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_gr_empirical_packet_01_evidence_promotion_gate.py`
- `formal/python/tests/test_stat_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_stat_empirical_packet_01_evidence_promotion_gate.py`
- `formal/python/tests/test_cosmo_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_cosmo_empirical_packet_01_evidence_promotion_gate.py`
- `formal/python/tests/test_em_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_em_empirical_packet_01_evidence_promotion_gate.py`
- `formal/python/tests/test_qft_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_qft_empirical_packet_01_evidence_promotion_gate.py`
- `formal/python/tests/test_sr_empirical_comparison_packet_01_gate.py`
- `formal/python/tests/test_sr_empirical_packet_01_evidence_promotion_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_DISCRIMINATOR_EMP_QM_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_DISCRIMINATOR_EMP_GR_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_STAT_EMPIRICAL_DISCRIMINATOR_EMP_STAT_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_COSMO_EMPIRICAL_DISCRIMINATOR_EMP_COSMO_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_DISCRIMINATOR_EMP_EM_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_QFT_EMPIRICAL_DISCRIMINATOR_EMP_QFT_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_DISCRIMINATOR_EMP_SR_01_v0.md`
- `formal/python/tests/test_qm_empirical_discriminator_emp_qm_01_scaffold_gate.py`
- `formal/python/tests/test_gr_empirical_discriminator_emp_gr_01_scaffold_gate.py`
- `formal/python/tests/test_stat_empirical_discriminator_emp_stat_01_scaffold_gate.py`
- `formal/python/tests/test_cosmo_empirical_discriminator_emp_cosmo_01_scaffold_gate.py`
- `formal/python/tests/test_em_empirical_discriminator_emp_em_01_scaffold_gate.py`
- `formal/python/tests/test_qft_empirical_discriminator_emp_qft_01_scaffold_gate.py`
- `formal/python/tests/test_sr_empirical_discriminator_emp_sr_01_scaffold_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE03_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE04_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE05_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE06_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE07_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE08_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE09_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE10_v0.md`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle02_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle03_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle04_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle05_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle06_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle07_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle08_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle09_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle10_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE11_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE12_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE13_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE14_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_SHADOW_NUMERICS_CYCLE15_v0.md`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle11_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle12_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle13_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle14_gate.py`
- `formal/python/tests/test_toe_master_action_shadow_numerics_cycle15_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_GR_EMPIRICAL_COMPARISON_PACKET_05_v0.md`
- `formal/output/gr_empirical_comparison_packet_05_v0.json`
- `formal/python/tests/test_gr_empirical_comparison_packet_05_gate.py`
- `formal/python/tests/test_gr_empirical_packet_05_artifact_schema_gate.py`
- `formal/docs/paper/DERIVATION_TARGET_SR_EMPIRICAL_COMPARISON_PACKET_05_v0.md`
- `formal/output/sr_empirical_comparison_packet_05_v0.json`
- `formal/python/tests/test_sr_empirical_comparison_packet_05_gate.py`
- `formal/python/tests/test_sr_empirical_packet_05_artifact_schema_gate.py`
- `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE01_v0.md`
- `formal/output/proof_debt_burndown_checkpoint_cycle01_v0.json`
- `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE02_v0.md`
- `formal/output/proof_debt_burndown_checkpoint_cycle02_v0.json`
- `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE03_v0.md`
- `formal/output/proof_debt_burndown_checkpoint_cycle03_v0.json`
- `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE04_v0.md`
- `formal/output/proof_debt_burndown_checkpoint_cycle04_v0.json`
- `formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md`
- `formal/output/proof_debt_burndown_checkpoint_cycle05_v0.json`
- `formal/output/toe_complete_v1_terminal_gate_checkpoint_v0.json`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet41_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_v0.md`
- `formal/output/toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_successor_discriminator_package_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet41_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet41_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet41_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet41_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `formal/output/toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_scorecard_cycle02_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_STATUS_v0: DEFINED_NUMERICALLY_EVALUATED_CYCLE02_REVIEW_LAYER_CLEARANCE_PENDING_v0`
- `TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_OUTCOME_v0: HOLD_RETAINED_REVIEW_LAYER_CLEARANCE_PENDING_v0`
- `TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_CYCLE02_STATUS_v0: EVALUATED_HOLD_RETAINED_REVIEW_LAYER_FAILURE_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet42_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet42_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet42_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet42_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet42_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet42_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet42_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet42_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet42_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet42_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet42_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet42_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet42_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet42_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET42_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET42_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET42_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET42_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET42_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET42_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET42_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET42_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET42_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET42_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET42_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET42_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET42_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET43_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet43_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet43_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET43_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet43_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet43_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET43_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet43_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet43_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET43_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet43_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet43_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET43_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet43_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet43_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET43_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet43_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet43_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet43_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet43_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET43_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET43_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET43_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET43_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET43_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET43_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET43_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET43_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET43_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET43_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET43_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET43_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET43_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet44_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet44_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet44_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet44_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet44_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet44_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet44_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet44_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet44_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet44_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet44_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet44_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet44_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet44_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET44_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET44_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET44_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET44_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET44_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET44_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET44_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet45_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet45_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet45_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet45_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet45_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet45_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet45_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet45_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet45_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet45_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet45_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet45_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet45_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet45_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET45_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET45_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET45_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET45_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET45_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET45_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET45_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET45_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET45_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET46_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet46_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet46_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET46_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet46_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet46_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET46_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet46_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet46_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET46_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet46_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet46_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET46_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet46_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet46_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET46_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet46_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet46_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet46_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet46_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET46_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET46_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET46_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET46_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET46_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET46_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET46_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET46_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET46_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET46_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET46_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET46_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET46_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET47_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet47_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet47_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET47_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet47_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet47_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET47_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet47_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet47_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET47_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet47_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet47_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET47_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet47_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet47_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET47_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet47_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet47_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet47_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet47_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET47_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET47_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET47_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET47_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET47_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET47_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET47_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET47_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET47_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET47_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET47_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET47_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET47_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET48_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet48_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet48_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET48_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet48_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet48_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET48_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet48_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet48_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET48_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet48_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet48_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET48_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet48_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet48_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET48_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet48_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet48_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet48_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet48_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET48_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET48_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET48_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET48_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET48_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET48_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET48_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET48_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET48_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET48_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET48_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET48_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET48_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET49_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet49_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet49_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET49_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet49_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet49_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET49_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet49_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet49_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET49_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet49_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet49_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET49_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet49_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet49_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET49_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet49_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet49_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet49_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet49_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET49_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET49_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET49_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET49_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET49_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET49_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET49_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET49_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET49_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET49_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET49_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET49_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET49_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet50_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet50_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet50_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet50_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet50_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet50_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet50_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet50_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet50_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet50_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet50_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet50_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet50_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet50_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET50_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET50_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET50_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET50_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET50_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET50_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET50_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet51_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet51_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet51_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet51_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet51_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet51_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet51_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet51_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet51_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet51_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet51_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet51_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet51_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet51_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET51_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET51_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET51_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET51_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET51_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET51_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET51_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET51_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET51_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET52_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet52_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet52_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET52_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet52_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet52_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET52_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet52_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet52_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET52_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet52_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet52_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET52_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet52_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet52_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET52_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet52_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet52_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet52_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet52_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET52_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET52_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET52_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET52_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET52_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET52_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET52_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET52_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET52_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET52_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET52_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET52_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET52_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet53_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet53_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet53_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet53_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet53_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet53_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet53_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet53_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet53_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet53_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET53_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet53_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet53_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet53_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet53_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET53_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET53_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET53_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET53_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET53_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET53_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET53_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET53_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET53_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET53_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET53_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET53_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET54_ELIGIBILITY_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet54_eligibility_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet54_eligibility_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET54_TARGETED_JUSTIFICATION_REVIEW_v0.md`
- `formal/output/toe_qft_gr_seam_packet54_targeted_justification_review_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet54_targeted_justification_review_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET54_HOLD_FORK_DECISION_v0.md`
- `formal/output/toe_qft_gr_seam_packet54_hold_fork_decision_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet54_hold_fork_decision_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET54_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md`
- `formal/output/toe_qft_gr_seam_packet54_reconsideration_numeric_thresholds_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet54_reconsideration_numeric_thresholds_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET54_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md`
- `formal/output/toe_qft_gr_seam_packet54_numeric_threshold_measurement_protocol_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet54_numeric_threshold_measurement_protocol_gate.py`
- `formal/docs/paper/TOE_QFT_GR_SEAM_PACKET54_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md`
- `formal/output/toe_qft_gr_seam_packet54_reconsideration_scorecard_worksheet_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet54_reconsideration_scorecard_worksheet_gate.py`
- `formal/output/toe_qft_gr_seam_packet54_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_gr_seam_packet54_reconsideration_scorecard_cycle01_evaluation_gate.py`
- `TOE_QFT_GR_SEAM_PACKET54_ELIGIBILITY_STATUS_v0: REVIEW_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET54_ELIGIBILITY_DISPOSITION_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET54_TARGETED_JUSTIFICATION_STATUS_v0: REVIEW_COMPLETE_INSUFFICIENT_FOR_AUTHORIZATION_v0`
- `TOE_QFT_GR_SEAM_PACKET54_TARGETED_JUSTIFICATION_OUTCOME_v0: HOLD_RETAINED_v0`
- `TOE_QFT_GR_SEAM_PACKET54_HOLD_FORK_DECISION_STATUS_v0: DECISION_COMPLETE_HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET54_HOLD_FORK_DECISION_OUTCOME_v0: HOLD_v0`
- `TOE_QFT_GR_SEAM_PACKET54_RECONSIDERATION_NUMERIC_THRESHOLDS_STATUS_v0: ACTIVE_HOLD_GATED_NUMERIC_CRITERIA_v0`
- `TOE_QFT_GR_SEAM_PACKET54_RECONSIDERATION_NUMERIC_THRESHOLDS_OUTCOME_v0: HOLD_RETAINED_UNTIL_NUMERIC_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET54_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_STATUS_v0: ACTIVE_OPERATIONAL_FORMULAS_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET54_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_OUTCOME_v0: HOLD_RETAINED_PENDING_MEASURED_CLEARANCE_v0`
- `TOE_QFT_GR_SEAM_PACKET54_RECONSIDERATION_SCORECARD_STATUS_v0: ACTIVE_CANONICAL_WORKSHEET_LOCKED_v0`
- `TOE_QFT_GR_SEAM_PACKET54_RECONSIDERATION_SCORECARD_OUTCOME_v0: HOLD_RETAINED_PENDING_SCORECARD_EVIDENCE_v0`
- `TOE_QFT_GR_SEAM_PACKET54_RECONSIDERATION_SCORECARD_CYCLE01_STATUS_v0: EVALUATED_HOLD_RETAINED_MISSING_NUMERIC_INPUTS_v0`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_CANDIDATE_BASELINE_v0.md`
- `formal/output/toe_qft_scalar_route_submission_candidate_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_submission_candidate_gate.py`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_READINESS_NOTE_v0.md`
- `formal/output/toe_qft_scalar_route_submission_readiness_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_submission_readiness_gate.py`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_PACKAGE_v0.md`
- `formal/output/toe_qft_scalar_route_submission_package_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_submission_package_gate.py`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_TECHNICAL_SIGNOFF_v0.md`
- `formal/output/toe_qft_scalar_route_technical_signoff_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_technical_signoff_gate.py`
- `SCALAR_ROUTE_SUBMISSION_CANDIDATE_STATUS_v0: BASELINE_LOCKED_FOR_INTERNAL_SUBMISSION_CANDIDATE`
- `SCALAR_ROUTE_SUBMISSION_READINESS_STATUS_v0: READY_FOR_BOUNDED_PAPER1_SUBMISSION_PACKAGE`
- `SCALAR_ROUTE_SUBMISSION_PACKAGE_STATUS_v0: EXTERNAL_SUBMISSION_PACKAGE_READY_BOUNDED`
- `QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0`
- `SCALAR_ROUTE_TECHNICAL_SIGNOFF_STATUS_v0: SIGNED_OFF_BOUNDED_RIGOR_BASELINE_v0`
- `SCALAR_ROUTE_TECHNICAL_SIGNOFF_DEBT_CLASS_v0: BOUNDED_LINKAGE_RECOVERY_DEBT_v0`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_v0.md`
- `formal/output/toe_qft_scalar_route_export_canonical_package_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_export_canonical_package_gate.py`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_v0.md`
- `formal/output/toe_qft_scalar_route_export_compile_validation_checkpoint_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_export_compile_validation_gate.py`
- `formal/docs/submission/scalar_paper1/main.tex`
- `formal/docs/submission/scalar_paper1/refs.bib`
- `formal/docs/submission/scalar_paper1/main.pdf`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_SKELETON_v0.md`
- `formal/output/toe_qft_scalar_route_section_map_v0.json`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md`
- `formal/output/toe_qft_scalar_route_manuscript_fill_map_v0.json`
- `formal/output/toe_qft_scalar_route_citation_binding_map_v0.json`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_BIBLIOGRAPHY_ALIGNMENT_v0.md`
- `formal/output/toe_qft_scalar_route_reference_map_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_manuscript_skeleton_gate.py`
- `formal/python/tests/test_toe_qft_scalar_route_manuscript_draft_gate.py`
- `formal/python/tests/test_toe_qft_scalar_route_citation_binding_gate.py`
- `formal/python/tests/test_toe_qft_scalar_route_bibliography_alignment_gate.py`
- `formal/docs/paper/TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_v0.md`
- `formal/output/toe_qft_scalar_route_full_technical_record_checkpoint_v0.json`
- `formal/output/toe_qft_scalar_route_scalar_inventory_manifest_v0.json`
- `formal/python/tests/test_toe_qft_scalar_route_full_technical_record_gate.py`
- `formal/python/tests/test_toe_qft_scalar_route_full_technical_record_coupling_gate.py`
- `SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_STATUS_v0: CANONICAL_SCALAR_PAPER1_EXPORT_OBJECT_PINNED`
- `SCALAR_ROUTE_EXPORT_COMPILE_VALIDATION_STATUS_v0: COMPILE_AND_PDF_ARTIFACT_VALIDATED`
- `SCALAR_ROUTE_FULL_TECHNICAL_RECORD_STATUS_v0: PHASE0_PHASE1_LOCKED_AUDIT_READY_V0`
- `SCALAR_ROUTE_FULL_TECHNICAL_RECORD_COUPLING_STATUS_v0: ARTIFACT_AND_STATUS_PARITY_ENFORCED`
- `SCALAR_ROUTE_FULL_TECHNICAL_RECORD_CHECKPOINT_FILE_v0: toe_qft_scalar_route_full_technical_record_checkpoint_v0.json`
- `SCALAR_ROUTE_FULL_TECHNICAL_RECORD_MANIFEST_FILE_v0: toe_qft_scalar_route_scalar_inventory_manifest_v0.json`
- `formal/python/tests/test_qft_evol_semantic_hardening_milestone_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle3_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle4_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle5_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle6_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle7_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle8_gate.py`
- `formal/python/tests/test_qft_evol_scaffold_saturation_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_52_completeness_gate.py`
- `formal/python/tests/test_qft_evol_kickoff_scaffold_gate.py`
- `formal/python/tests/test_lean_build_gate_qft_evol_object_scaffold.py`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_v0: CANONICAL_MOMENTUM_HAMILTONIAN_UNITARITY_CHAIN_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE2_v0: SEMANTIC_HARDENING_MILESTONE_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE3_v0: CANONICAL_MOMENTUM_INVARIANT_UNITARITY_ROUTE_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE3_v0: CANONICAL_MOMENTUM_INVARIANT_UNITARITY_ROUTE_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE4_v0: HAMILTONIAN_TO_GENERATOR_CANONICAL_MOMENTUM_ROUTE_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE4_v0: HAMILTONIAN_TO_GENERATOR_CANONICAL_MOMENTUM_ROUTE_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE5_v0: HAMILTONIAN_MEDIATED_REFLECTIVE_CANONICAL_MOMENTUM_GENERATOR_UNITARITY_ROUTE_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE5_v0: HAMILTONIAN_MEDIATED_REFLECTIVE_CANONICAL_MOMENTUM_GENERATOR_UNITARITY_ROUTE_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE6_v0: GENERATOR_UNITARITY_ROUTE_COHERENCE_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE6_v0: GENERATOR_UNITARITY_ROUTE_COHERENCE_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE7_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE7_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE8_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_COHERENCE_ALIGNMENT_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE8_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_COHERENCE_ALIGNMENT_TOKEN_PINNED`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle9_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle10_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle11_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle12_gate.py`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE9_v0: GENERATOR_UNITARITY_ROUTE_COHERENCE_NORMALIZATION_ALIGNMENT_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE9_v0: GENERATOR_UNITARITY_ROUTE_COHERENCE_NORMALIZATION_ALIGNMENT_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE10_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE10_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE11_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE11_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE12_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_ALIGNMENT_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE12_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_ALIGNMENT_TOKEN_PINNED`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle13_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle14_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle15_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle16_gate.py`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE13_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE13_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE14_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE14_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE15_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE15_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE16_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE16_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_TOKEN_PINNED`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle17_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle18_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle19_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle20_gate.py`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE17_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE17_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE18_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE18_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE19_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE19_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE20_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE20_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_TOKEN_PINNED`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle21_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle22_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle23_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle24_gate.py`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE21_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE21_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE22_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE22_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE23_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE23_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE24_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE24_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_TOKEN_PINNED`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle25_gate.py`
- `formal/python/tests/test_qft_evol_semantic_hardening_cycle26_gate.py`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE25_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_NORMALIZATION_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE25_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_NORMALIZATION_TOKEN_PINNED`
- `QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE26_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE26_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_ALIGNMENT_SYMMETRY_WITNESS_TOKEN_PINNED`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE27_v0: TRANCHE_ROLLOVER_LEGACY_FORBID_GATE_BUNDLE_PINNED`
- `QFT_FULL_DERIVATION_TRANCHE_ROLLOVER_GATE_v0: CYCLE26_TO_CYCLE27_HARDENING_ROUTE_ONLY`
- `QFT_FULL_DERIVATION_LEGACY_ROUTE_FORBID_GATE_v0: NO_LEGACY_PROMOTION_OR_ADJUDICATION_SHORTCUT`
- `QFT_FULL_DERIVATION_DISCHARGE_TRANSITION_POLICY_v0: LOCKED_UNTIL_EXIT_ROW_CRITERIA_AND_PREDISCHARGE_BUNDLE`
- `QFT_FULL_DERIVATION_TRANCHE_ROLLOVER_GATE_BUNDLE_ARTIFACT_v0: qft_full_derivation_tranche_rollover_gate_bundle_cycle27_v0`
- `formal/output/qft_full_derivation_tranche_rollover_gate_bundle_cycle27_v0.json`
- `formal/python/tests/test_qft_full_derivation_tranche_rollover_cycle27_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE28_v0: EXIT_ROW_CRITERIA_LOCK_BUNDLE_PINNED`
- `QFT_FULL_DERIVATION_DISCHARGE_CRITERIA_v0: PRE_DISCHARGE_EXIT_ROW_CRITERIA_PINNED`
- `QFT_FULL_DERIVATION_CRITERIA_ROW_01_v0: CANONICAL_ROUTE_CONTINUITY_PINNED`
- `QFT_FULL_DERIVATION_CRITERIA_ROW_02_v0: TRANCHE_ROLLOVER_AND_LEGACY_FORBID_PINNED`
- `QFT_FULL_DERIVATION_CRITERIA_ROW_03_v0: AUTHORITY_SURFACE_SYNC_PINNED`
- `QFT_FULL_DERIVATION_EXIT_ROW_01_STATUS_v0: LOCKED_PRE_DISCHARGE`
- `QFT_FULL_DERIVATION_EXIT_ROW_02_STATUS_v0: LOCKED_PRE_DISCHARGE`
- `QFT_FULL_DERIVATION_EXIT_ROW_03_STATUS_v0: LOCKED_PRE_DISCHARGE`
- `QFT_FULL_DERIVATION_EXIT_ROW_CRITERIA_GATE_v0: LOCKED_UNTIL_PREDISCHARGE_AND_TRANSITION_BUNDLE`
- `QFT_FULL_DERIVATION_EXIT_ROW_CRITERIA_ARTIFACT_v0: qft_full_derivation_exit_row_criteria_cycle28_v0`
- `formal/output/qft_full_derivation_exit_row_criteria_cycle28_v0.json`
- `formal/python/tests/test_qft_full_derivation_exit_row_criteria_cycle28_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE29_v0: PREDISCHARGE_TRANSITION_BUNDLE_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREDISCHARGE_TRANSITION_BUNDLE_GATE_v0: EXIT_ROW_CRITERIA_AND_ROLLOVER_REQUIRED`
- `QFT_FULL_DERIVATION_ADJUDICATION_FLIP_BLOCK_v0: REQUIRE_EXPLICIT_DISCHARGE_GATE_CLOSURE`
- `QFT_FULL_DERIVATION_PREDISCHARGE_TRANSITION_BUNDLE_ARTIFACT_v0: qft_full_derivation_predischarge_transition_bundle_cycle29_v0`
- `formal/output/qft_full_derivation_predischarge_transition_bundle_cycle29_v0.json`
- `formal/python/tests/test_qft_full_derivation_predischarge_transition_cycle29_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE30_v0: DISCHARGE_TRANSITION_READINESS_BUNDLE_LOCK_PINNED`
- `QFT_FULL_DERIVATION_DISCHARGE_TRANSITION_READINESS_GATE_v0: CYCLE27_29_LOCKS_AND_EXPLICIT_FLIP_GATE_REQUIRED`
- `QFT_FULL_DERIVATION_ADJUDICATION_FLIP_AUTHORIZATION_GATE_v0: LOCKED_UNTIL_DISCHARGE_CRITERIA_COMPLETE_AND_EXPLICIT_APPROVAL`
- `QFT_FULL_DERIVATION_DISCHARGE_TRANSITION_READINESS_BUNDLE_ARTIFACT_v0: qft_full_derivation_discharge_transition_readiness_bundle_cycle30_v0`
- `formal/output/qft_full_derivation_discharge_transition_readiness_bundle_cycle30_v0.json`
- `formal/python/tests/test_qft_full_derivation_discharge_transition_readiness_cycle30_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE31_v0: ADJUDICATION_CRITERIA_BUNDLE_LOCK_PINNED`
- `QFT_FULL_DERIVATION_ADJUDICATION_CRITERIA_GATE_v0: LOCKED_UNTIL_ALL_EXIT_ROWS_AND_TRANSITION_BUNDLES_COMPLETE`
- `QFT_FULL_DERIVATION_INEVITABILITY_CRITERIA_GATE_v0: LOCKED_UNTIL_COUNTERFACTUAL_AND_INDEPENDENT_NECESSITY_BUNDLES_COMPLETE`
- `QFT_FULL_DERIVATION_ADJUDICATION_CRITERIA_BUNDLE_ARTIFACT_v0: qft_full_derivation_adjudication_criteria_bundle_cycle31_v0`
- `formal/output/qft_full_derivation_adjudication_criteria_bundle_cycle31_v0.json`
- `formal/python/tests/test_qft_full_derivation_adjudication_criteria_cycle31_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE32_v0: FLIP_DECISION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_FLIP_DECISION_PACKET_GATE_v0: LOCKED_UNTIL_CYCLE31_CRITERIA_AND_EXPLICIT_AUTHORITY_SIGNOFF`
- `QFT_FULL_DERIVATION_FLIP_DECISION_PACKET_AUTHORITY_v0: TWO_KEY_REVIEW_REQUIRED_NO_AUTOFIP`
- `QFT_FULL_DERIVATION_FLIP_DECISION_PACKET_ARTIFACT_v0: qft_full_derivation_flip_decision_packet_cycle32_v0`
- `formal/output/qft_full_derivation_flip_decision_packet_cycle32_v0.json`
- `formal/python/tests/test_qft_full_derivation_flip_decision_packet_cycle32_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE33_v0: FINAL_PREFLIP_EVIDENCE_REGISTRY_LOCK_PINNED`
- `QFT_FULL_DERIVATION_FINAL_PREFLIP_EVIDENCE_REGISTRY_GATE_v0: LOCKED_UNTIL_ALL_REQUIRED_BUNDLES_PRESENT_AND_HASH_PINNED`
- `QFT_FULL_DERIVATION_FINAL_PREFLIP_EVIDENCE_REQUIRED_BUNDLES_v0: CYCLE27_ROLLOVER;CYCLE28_EXIT_ROW;CYCLE29_PREDISCHARGE_TRANSITION;CYCLE30_READINESS;CYCLE31_ADJUDICATION_CRITERIA;CYCLE32_FLIP_PACKET`
- `QFT_FULL_DERIVATION_FINAL_PREFLIP_EVIDENCE_REGISTRY_ARTIFACT_v0: qft_full_derivation_final_prefip_evidence_registry_cycle33_v0`
- `formal/output/qft_full_derivation_final_prefip_evidence_registry_cycle33_v0.json`
- `formal/python/tests/test_qft_full_derivation_final_prefip_evidence_registry_cycle33_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE34_v0: MANUAL_FLIP_AUTHORIZATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_PACKET_GATE_v0: LOCKED_UNTIL_CYCLE33_REGISTRY_HASH_AND_TWO_KEY_SIGNOFF_PRESENT`
- `QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_PACKET_TWO_KEY_v0: KEYA_PENDING_KEYB_PENDING`
- `QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_PACKET_ARTIFACT_v0: qft_full_derivation_manual_flip_authorization_packet_cycle34_v0`
- `formal/output/qft_full_derivation_manual_flip_authorization_packet_cycle34_v0.json`
- `formal/python/tests/test_qft_full_derivation_manual_flip_authorization_packet_cycle34_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE35_v0: ADJUDICATION_EXECUTION_GUARD_LOCK_PINNED`
- `QFT_FULL_DERIVATION_ADJUDICATION_EXECUTION_GUARD_GATE_v0: FLIP_FORBIDDEN_UNLESS_TWO_KEY_AUTHORIZED_AND_NONPENDING`
- `QFT_FULL_DERIVATION_MANUAL_FLIP_AUTHORIZATION_STATUS_GATE_v0: KEYA_KEYB_MUST_BE_AUTHORIZED`
- `QFT_FULL_DERIVATION_ADJUDICATION_EXECUTION_GUARD_ARTIFACT_v0: qft_full_derivation_adjudication_execution_guard_cycle35_v0`
- `formal/output/qft_full_derivation_adjudication_execution_guard_cycle35_v0.json`
- `formal/python/tests/test_qft_full_derivation_adjudication_execution_guard_cycle35_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE36_v0: POST_AUTHORIZATION_REVALIDATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_POST_AUTH_REVALIDATION_PACKET_GATE_v0: REVALIDATION_REQUIRED_AFTER_ANY_AUTH_STATUS_CHANGE`
- `QFT_FULL_DERIVATION_POST_AUTH_REVALIDATION_SCOPE_v0: CYCLE27_35_BUNDLE_SUITE_MUST_PASS`
- `QFT_FULL_DERIVATION_POST_AUTH_REVALIDATION_PACKET_ARTIFACT_v0: qft_full_derivation_post_authorization_revalidation_packet_cycle36_v0`
- `formal/output/qft_full_derivation_post_authorization_revalidation_packet_cycle36_v0.json`
- `formal/python/tests/test_qft_full_derivation_post_authorization_revalidation_packet_cycle36_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE37_v0: TOKEN_FLIP_DRYRUN_SIMULATOR_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_GATE_v0: SIMULATION_ONLY_NO_TOKEN_WRITE`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_SCOPE_v0: READINESS_CHECK_AGAINST_CYCLE27_36_BUNDLES_ONLY`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_SIMULATOR_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_simulator_cycle37_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE38_v0: TOKEN_FLIP_DRYRUN_ATTESTATION_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_GATE_v0: REQUIRE_SIMULATOR_OUTPUT_AND_NONWRITE_CONFIRMATION`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_SCOPE_v0: CYCLE37_SIMULATOR_AND_CYCLE27_36_INPUTS_REPLAYED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_attestation_cycle38_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE39_v0: TOKEN_FLIP_DRYRUN_RECONCILIATION_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_GATE_v0: REQUIRE_ATTESTATION_MATCH_AND_NO_TOKEN_MUTATION`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_SCOPE_v0: CYCLE38_ATTESTATION_AND_CYCLE37_SIMULATOR_ALIGNMENT`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE40_v0: TOKEN_FLIP_DRYRUN_CLOSURE_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_GATE_v0: REQUIRE_RECONCILIATION_COMPLETE_AND_NONWRITE_FINALIZED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_SCOPE_v0: CYCLE39_RECONCILIATION_PLUS_CYCLE37_38_TRACEABILITY`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_closure_cycle40_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_closure_cycle40_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_closure_cycle40_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE41_v0: TOKEN_FLIP_DRYRUN_ARCHIVAL_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_GATE_v0: REQUIRE_CYCLE40_CLOSURE_AND_IMMUTABLE_ARCHIVE_PIN`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_SCOPE_v0: CYCLE37_40_TRACE_CHAIN_ARCHIVED_NO_TOKEN_WRITE`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_archival_cycle41_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_archival_cycle41_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_archival_cycle41_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE42_v0: TOKEN_FLIP_DRYRUN_HANDOFF_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_GATE_v0: REQUIRE_ARCHIVAL_IMMUTABILITY_AND_HANDOFF_READINESS`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_SCOPE_v0: CYCLE41_ARCHIVE_CHAIN_AND_CYCLE37_40_TRACE_TRANSFER`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_handoff_cycle42_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE43_v0: TOKEN_FLIP_DRYRUN_CUSTODY_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_GATE_v0: REQUIRE_HANDOFF_COMPLETENESS_AND_CUSTODY_CHAIN_SEAL`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_SCOPE_v0: CYCLE42_HANDOFF_WITH_CYCLE37_41_AUDIT_LINKAGE`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_custody_cycle43_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_custody_cycle43_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_custody_cycle43_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE44_v0: TOKEN_FLIP_DRYRUN_NOTARIZATION_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_NOTARIZATION_GATE_v0: REQUIRE_CUSTODY_SEAL_AND_NOTARIZED_NONWRITE_ATTESTATION`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_NOTARIZATION_SCOPE_v0: CYCLE43_CUSTODY_WITH_CYCLE37_42_CHAIN_VERIFICATION`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_NOTARIZATION_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_notarization_cycle44_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_notarization_cycle44_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_notarization_cycle44_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE45_v0: TOKEN_FLIP_DRYRUN_WITNESS_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_WITNESS_GATE_v0: REQUIRE_NOTARIZATION_COMPLETION_AND_WITNESS_NONWRITE_CONFIRMATION`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_WITNESS_SCOPE_v0: CYCLE44_NOTARIZATION_WITH_CYCLE37_43_CHAIN_AUDIT`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_WITNESS_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_witness_cycle45_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_witness_cycle45_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_witness_cycle45_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE46_v0: TOKEN_FLIP_DRYRUN_RATIFICATION_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RATIFICATION_GATE_v0: REQUIRE_WITNESS_CONFIRMATION_AND_RATIFIED_NONWRITE_STATUS`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RATIFICATION_SCOPE_v0: CYCLE45_WITNESS_WITH_CYCLE37_44_CHAIN_REVIEW`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RATIFICATION_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_ratification_cycle46_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_ratification_cycle46_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_ratification_cycle46_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE47_v0: TOKEN_FLIP_DRYRUN_CONCURRENCE_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONCURRENCE_GATE_v0: REQUIRE_RATIFICATION_COMPLETION_AND_MULTI_WITNESS_CONCURRENCE`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONCURRENCE_SCOPE_v0: CYCLE46_RATIFICATION_WITH_CYCLE37_45_CHAIN_AUDIT`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONCURRENCE_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_concurrence_cycle47_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_concurrence_cycle47_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_concurrence_cycle47_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE48_v0: TOKEN_FLIP_DRYRUN_CONSENSUS_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONSENSUS_GATE_v0: REQUIRE_CONCURRENCE_COMPLETION_AND_MULTI_PARTY_CONSENSUS_NONWRITE`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONSENSUS_SCOPE_v0: CYCLE47_CONCURRENCE_WITH_CYCLE37_46_CHAIN_REVIEW`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CONSENSUS_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_consensus_cycle48_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_consensus_cycle48_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_consensus_cycle48_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE49_v0: TOKEN_FLIP_DRYRUN_UNANIMITY_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_GATE_v0: REQUIRE_CONSENSUS_COMPLETION_AND_UNANIMOUS_NONWRITE_CONFIRMATION`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_SCOPE_v0: CYCLE48_CONSENSUS_WITH_CYCLE37_47_CHAIN_REVIEW`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_unanimity_cycle49_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE50_v0: TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_GATE_v0: REQUIRE_UNANIMITY_COMPLETION_AND_FINAL_NONWRITE_CLOSURE_CONSENSUS`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_SCOPE_v0: CYCLE49_UNANIMITY_WITH_CYCLE37_48_CHAIN_REVIEW`
- `QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_CONSENSUS_ARTIFACT_v0: qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_v0`
- `formal/output/qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_v0.json`
- `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_closure_consensus_cycle50_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE51_v0: TWO_KEY_AUTH_REVALIDATION_TRANSITION_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TWO_KEY_AUTH_REVALIDATION_TRANSITION_GATE_v0: REQUIRE_EXPLICIT_TWO_KEY_AUTH_STATE_TRANSITION_PACKET_AND_NONFLIP_ENFORCEMENT`
- `QFT_FULL_DERIVATION_TWO_KEY_AUTH_REVALIDATION_TRANSITION_SCOPE_v0: KEYA_KEYB_STATUS_CHANGE_MUST_TRIGGER_POST_AUTH_REVALIDATION_REPLAY`
- `QFT_FULL_DERIVATION_TWO_KEY_AUTH_REVALIDATION_TRANSITION_ARTIFACT_v0: qft_full_derivation_two_key_auth_revalidation_transition_cycle51_v0`
- `formal/output/qft_full_derivation_two_key_auth_revalidation_transition_cycle51_v0.json`
- `formal/python/tests/test_qft_full_derivation_two_key_auth_revalidation_transition_cycle51_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE52_v0: KEYA_AUTHORIZATION_REVALIDATION_REPLAY_LOCK_PINNED`
- `QFT_FULL_DERIVATION_KEYA_AUTH_REVALIDATION_REPLAY_GATE_v0: REQUIRE_KEYA_AUTH_EVENT_PACKET_WITH_KEYB_STILL_PENDING_AND_NONFLIP_ENFORCEMENT`
- `QFT_FULL_DERIVATION_KEYA_AUTH_REVALIDATION_REPLAY_SCOPE_v0: KEYA_AUTHORIZED_KEYB_PENDING_REQUIRES_IMMEDIATE_POST_AUTH_REVALIDATION_REPLAY`
- `QFT_FULL_DERIVATION_KEYA_AUTH_REVALIDATION_REPLAY_ARTIFACT_v0: qft_full_derivation_keya_auth_revalidation_replay_cycle52_v0`
- `formal/output/qft_full_derivation_keya_auth_revalidation_replay_cycle52_v0.json`
- `formal/python/tests/test_qft_full_derivation_keya_auth_revalidation_replay_cycle52_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE53_v0: KEYB_AUTHORIZATION_REVALIDATION_REPLAY_LOCK_PINNED`
- `QFT_FULL_DERIVATION_KEYB_AUTH_REVALIDATION_REPLAY_GATE_v0: REQUIRE_KEYB_AUTH_EVENT_PACKET_WITH_KEYA_ALREADY_AUTHORIZED_AND_NONFLIP_ENFORCEMENT`
- `QFT_FULL_DERIVATION_KEYB_AUTH_REVALIDATION_REPLAY_SCOPE_v0: KEYA_AUTHORIZED_KEYB_AUTHORIZED_REQUIRES_IMMEDIATE_POST_AUTH_REVALIDATION_REPLAY`
- `QFT_FULL_DERIVATION_KEYB_AUTH_REVALIDATION_REPLAY_ARTIFACT_v0: qft_full_derivation_keyb_auth_revalidation_replay_cycle53_v0`
- `formal/output/qft_full_derivation_keyb_auth_revalidation_replay_cycle53_v0.json`
- `formal/python/tests/test_qft_full_derivation_keyb_auth_revalidation_replay_cycle53_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE54_v0: TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_LOCK_PINNED`
- `QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_GATE_v0: REQUIRE_KEYA_KEYB_AUTHORIZED_PACKET_AND_POST_AUTH_REVALIDATION_CLOSURE_NONFLIP`
- `QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_SCOPE_v0: KEYA_AUTHORIZED_KEYB_AUTHORIZED_REVALIDATION_REPLAY_CLOSURE_REQUIRED_BEFORE_ANY_FLIP`
- `QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_ARTIFACT_v0: qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_v0`
- `formal/output/qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_v0.json`
- `formal/python/tests/test_qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE55_v0: NONFLIP_EXECUTION_READINESS_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_NONFLIP_EXECUTION_READINESS_PACKET_GATE_v0: REQUIRE_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_AND_NONFLIP_EXECUTION_PACKET`
- `QFT_FULL_DERIVATION_NONFLIP_EXECUTION_READINESS_PACKET_SCOPE_v0: ADJUDICATION_REMAINS_NOT_YET_DISCHARGED_UNTIL_EXPLICIT_FLIP_AUTHORITY`
- `QFT_FULL_DERIVATION_NONFLIP_EXECUTION_READINESS_PACKET_ARTIFACT_v0: qft_full_derivation_nonflip_execution_readiness_packet_cycle55_v0`
- `formal/output/qft_full_derivation_nonflip_execution_readiness_packet_cycle55_v0.json`
- `formal/python/tests/test_qft_full_derivation_nonflip_execution_readiness_packet_cycle55_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE56_v0: PREFLIP_AUTHORITY_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREFLIP_AUTHORITY_ATTESTATION_PACKET_GATE_v0: REQUIRE_NONFLIP_EXECUTION_READINESS_PACKET_AND_EXPLICIT_PREFLIP_AUTHORITY_ATTESTATION`
- `QFT_FULL_DERIVATION_PREFLIP_AUTHORITY_ATTESTATION_PACKET_SCOPE_v0: PREFLIP_AUTHORITY_ATTESTATION_DOES_NOT_AUTHORIZE_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREFLIP_AUTHORITY_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preflip_authority_attestation_packet_cycle56_v0`
- `formal/output/qft_full_derivation_preflip_authority_attestation_packet_cycle56_v0.json`
- `formal/python/tests/test_qft_full_derivation_preflip_authority_attestation_packet_cycle56_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE57_v0: FLIP_ELIGIBILITY_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREFLIP_AUTHORITY_ATTESTATION_PACKET_AND_NONFLIP_GUARD_STILL_ACTIVE`
- `QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_SCOPE_v0: ELIGIBILITY_ATTESTED_WITHOUT_EXECUTING_OR_AUTHORIZING_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_flip_eligibility_attestation_packet_cycle57_v0`
- `formal/output/qft_full_derivation_flip_eligibility_attestation_packet_cycle57_v0.json`
- `formal/python/tests/test_qft_full_derivation_flip_eligibility_attestation_packet_cycle57_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE58_v0: FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_GATE_v0: REQUIRE_FLIP_ELIGIBILITY_ATTESTATION_PACKET_AND_FINAL_PREEXECUTION_NONFLIP_ATTESTATION`
- `QFT_FULL_DERIVATION_FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_SCOPE_v0: FINAL_PREEXECUTION_ATTESTATION_CONFIRMS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_final_preexecution_nonflip_attestation_packet_cycle58_v0`
- `formal/output/qft_full_derivation_final_preexecution_nonflip_attestation_packet_cycle58_v0.json`
- `formal/python/tests/test_qft_full_derivation_final_preexecution_nonflip_attestation_packet_cycle58_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE59_v0: PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_GATE_v0: REQUIRE_FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_AND_EXECUTION_BOUNDARY_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_SCOPE_v0: PREEXECUTION_BOUNDARY_CONFIRMATION_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE60_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_AND_EXECUTION_CUSTODY_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_CONFIRMATION_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_packet_cycle60_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_packet_cycle60_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_packet_cycle60_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE61_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_packet_cycle61_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_packet_cycle61_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_packet_cycle61_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE62_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_packet_cycle62_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_packet_cycle62_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_packet_cycle62_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE63_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_packet_cycle63_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_packet_cycle63_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_packet_cycle63_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE64_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_packet_cycle64_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_packet_cycle64_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_packet_cycle64_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE65_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_packet_cycle65_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_packet_cycle65_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_packet_cycle65_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE66_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle66_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle66_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle66_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE67_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle67_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle67_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle67_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE68_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle68_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle68_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle68_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE69_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle69_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle69_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle69_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE70_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle70_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle70_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle70_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE71_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle71_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle71_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle71_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE72_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle72_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle72_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle72_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE73_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle73_v0`
- `formal/output/qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle73_v0.json`
- `formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_cycle73_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE74_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle74_v0`
- `formal/output/qft_full_derivation_cycle74_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle74_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE75_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle75_v0`
- `formal/output/qft_full_derivation_cycle75_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle75_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE76_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle76_v0`
- `formal/output/qft_full_derivation_cycle76_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle76_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE77_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle77_v0`
- `formal/output/qft_full_derivation_cycle77_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle77_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE78_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle78_v0`
- `formal/output/qft_full_derivation_cycle78_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle78_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE79_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle79_v0`
- `formal/output/qft_full_derivation_cycle79_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle79_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE80_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle80_v0`
- `formal/output/qft_full_derivation_cycle80_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle80_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE81_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle81_v0`
- `formal/output/qft_full_derivation_cycle81_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle81_gate.py`
- `QFT_FULL_DERIVATION_DISCHARGE_PRACTICAL_ACTION_PLAN_CYCLE81_v0: PREREQUISITE_AUTHORIZATION_GUARD_EXECUTION_PLAN_PINNED`
- `formal/output/qft_full_derivation_discharge_practical_action_plan_cycle81_v0.json`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE82_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_GATE_v0: REQUIRE_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_AND_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_NONFLIP_CONFIRMATION`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle82_v0`
- `formal/output/qft_full_derivation_cycle82_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle82_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE83_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle83_v0`
- `formal/output/qft_full_derivation_cycle83_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle83_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE84_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle84_v0`
- `formal/output/qft_full_derivation_cycle84_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle84_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE85_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle85_v0`
- `formal/output/qft_full_derivation_cycle85_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle85_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE86_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle86_v0`
- `formal/output/qft_full_derivation_cycle86_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle86_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE87_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle87_v0`
- `formal/output/qft_full_derivation_cycle87_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle87_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE88_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle88_v0`
- `formal/output/qft_full_derivation_cycle88_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle88_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE89_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle89_v0`
- `formal/output/qft_full_derivation_cycle89_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle89_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE90_v0: PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_LOCK_PINNED`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_SCOPE_v0: PREEXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP`
- `QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_ARTIFACT_v0: qft_full_derivation_preexecution_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_cycle90_v0`
- `formal/output/qft_full_derivation_cycle90_v0.json`
- `formal/python/tests/test_qft_full_derivation_cycle90_gate.py`
- `QFT_FULL_DERIVATION_PROGRESS_CYCLE91_v0: FINAL_DISCHARGE_CLOSURE_AND_SIGNOFF_LOCKED`
- `QFT_FULL_DERIVATION_FINAL_DISCHARGE_CLOSURE_ARTIFACT_v0: qft_full_derivation_final_discharge_closure_cycle91_v0`
- `formal/output/qft_full_derivation_final_discharge_closure_cycle91_v0.json`
- `formal/python/tests/test_qft_full_derivation_discharge_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_05_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_06_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_07_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_08_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_09_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_10_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_11_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_12_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_13_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_14_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_15_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_16_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_40_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_41_completeness_gate.py`
- `formal/python/tests/test_qft_evol_micro_tranche_01_42_completeness_gate.py`




