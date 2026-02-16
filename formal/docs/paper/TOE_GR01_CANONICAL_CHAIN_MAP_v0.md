# TOE GR01 Canonical Chain Map v0

Map ID:
- `TOE_GR01_CANONICAL_CHAIN_MAP_v0`

Scope:
- bounded/discrete weak-field v0 only

Canonical theorem chain (current):
1. Action/representation minimization route:
- `gr01_poisson_equation_of_GR01Assumptions_v0_min3`

2. Discrete residual closure route:
- `gr01_discrete_residual_from_bridge_promotion_chain_default_binding`

3. Bridge transport and residual surfaces:
- `ELImpliesOperatorResidualTransport`
- `gr01_el_implies_discrete_poisson_residual_from_operator_transport`

4. End-to-end closure surfaces:
- `gr01_end_to_end_chain_bundle_under_promoted_assumptions`
- `gr01_end_to_end_poisson_equation_under_promoted_assumptions`

Canonical source pointers:
- `formal/toe_formal/ToeFormal/Variational/GR01AssumptionLedger.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean`
- `formal/toe_formal/ToeFormal/Variational/GR01EndToEndClosure.lean`

Anti-legacy condition:
- `ELImpliesProjectedResidual` must be absent from canonical GR01 theorem surfaces.
