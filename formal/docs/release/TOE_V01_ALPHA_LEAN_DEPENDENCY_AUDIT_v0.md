# ToE v0.1-alpha Lean Dependency Audit v0

Spec ID:
- `TOE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_v0`

Classification:
- `P-POLICY`

Result token:
- `TOE_V01_ALPHA_LEAN_RELEASE_SPINE_PREPARED`

Lean release index:
- `formal/toe_formal/ToeFormal/Release/V01Index.lean`

Audit status:
- Seeded. Audit-row completeness is gated first; exact `#print axioms` parsing is deferred.

| theorem | source file | release label | audit command | observed dependency result | project axioms used | supplied structures used | linked assumptions | audit status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `master_action_stationary_implies_free_scalar_kg` | `formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean` | `T-LEAN-COND` | `#print axioms ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg` | pending captured output | pending | `MasterActionScalarSlice.firstVariation_matches_boxPlusMass` | bounded scalar slice; stationarity | `pending` |
| `stationary_implies_operator_zero` | `formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean` | `T-LEAN-COND` | `#print axioms ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero` | pending captured output | pending | none beyond finite test-field model | separating variations | `pending` |
| `finite_transport_theorems_construct_residual_package_v0` | `formal/toe_formal/ToeFormal/Bridges/QM_STAT_TransportResidualPackage.lean` | `T-LEAN-COND` | `#print axioms ToeFormal.Bridges.QMSTATTransportResidualPackage.finite_transport_theorems_construct_residual_package_v0` | pending captured output | pending | source, target, transport structures | finite transport equivalence/alignment | `pending` |
| `qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0` | `formal/toe_formal/ToeFormal/Bridges/QFT_GR_SourceMapEligibilityLadderSummary.lean` | `B-BLOCKED` | `#print axioms ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary.qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0` | pending captured output | pending | supplied-only eligibility ladder layers | missing witness chain | `pending` |
| `supplied_interface_alignment_semantics_construct_bridge_package_v0` | `formal/toe_formal/ToeFormal/Bridges/EM_QFT_InterfaceAlignmentSemanticBridge.lean` | `T-LEAN-COND` | `#print axioms ToeFormal.Bridges.EMQFTInterfaceAlignmentSemanticBridge.supplied_interface_alignment_semantics_construct_bridge_package_v0` | pending captured output | pending | supplied interface alignment semantics | source-current/gauge obligations remain open | `pending` |
| `supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0` | `formal/toe_formal/ToeFormal/Bridges/SR_CosmologyRegimeTransport.lean` | `T-LEAN-COND` | `#print axioms ToeFormal.Bridges.SRCosmologyRegimeTransport.supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0` | pending captured output | pending | supplied local/regime alignment | global semantic map remains open | `pending` |

Nonclaim boundary:
- Pending audit rows do not promote any theorem to `T-LEAN-UNCOND`.
- This audit does not authorize master-action promotion, pillar completion, seam closure, Phase 2 readiness, empirical adequacy, canonical ToE status, or QFT-GR source-map closure.
