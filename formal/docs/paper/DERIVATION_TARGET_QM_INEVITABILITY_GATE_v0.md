# Derivation Target: QM Inevitability Gate v0

Spec ID:
- `DERIVATION_TARGET_QM_INEVITABILITY_GATE_v0`

Target ID:
- `TARGET-QM-INEVITABILITY-GATE-PLAN`

Classification:
- `P-POLICY`

Purpose:
- Define theorem-body inevitability discharge requirements for the QM lane.
- Prevent label/token promotion without constructive + counterfactual inevitability evidence.

Adjudication token:
- `QM_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: DISCHARGED_v0_BOUNDED`

Scope boundary:
- bounded theorem scope only.
- no external truth claim.
- no Born-rule or measurement-semantics completion claim by this artifact.

Required inevitability theorem-body package (all required before discharge):
1. Necessity theorem (constructive track)
- required theorem token:
  - `qm_inevitability_necessity_under_minimized_assumptions_v0`
- required minimized-assumption anchor token:
  - `QMInevitabilityMinimizedAssumptions_v0`
- required named-route assumption tokens:
  - `QMInevitabilityCanonicalConstructiveRoute_v0`
  - `QMInevitabilityUnitaryConsistencyRoute_v0`
  - `QMInevitabilityNoDirectSchrodingerInsertionRoute_v0`
- required no-shortcut elimination-chain tokens:
  - `QMNoDirectInsertionEliminationLemmaChain_v0`
  - `QMDirectSchrodingerInsertionRouteUsed_v0`
  - `QMContractBridgeCompatibilityWrapperRouteUsed_v0`
- required closure-surface token:
  - `QMInevitabilityClosureSurface_v0`
- requirement:
  - theorem body must route through the canonical QM full-derivation constructive lane.
  - theorem signature must bind minimized assumptions as `(hMin : QMInevitabilityMinimizedAssumptions_v0 h)`.

2. Counterfactual theorem (negative-control track)
- required theorem token:
  - `qm_inevitability_counterfactual_breaks_without_required_assumption_v0`
- required counterfactual break token:
  - `¬QMInevitabilityClosureSurface_v0`
- required per-assumption break theorem tokens:
  - `qm_inevitability_counterfactual_breaks_without_canonical_constructive_route_assumption_v0`
  - `qm_inevitability_counterfactual_breaks_without_unitary_consistency_assumption_v0`
  - `qm_inevitability_counterfactual_breaks_without_no_direct_schrodinger_insertion_assumption_v0`
- requirement:
  - removing any required minimized assumption must invalidate the target closure surface.
  - theorem body must explicitly consume a missing-assumption witness and derive route failure.

3. Structural classification theorem (duality/necessity-class track)
- required theorem token:
  - `qm_inevitability_structural_classification_of_constructive_route_v0`
- required classification anchor token:
  - `QMInevitabilityConstructiveRouteClassification_v0`
- requirement:
  - constructive route must be proven to belong to the necessity class under declared constraints.

4. Discharge-readiness bundle theorem track
- required theorem tokens:
  - `qm_inevitability_discharge_ready_bundle_v0`
  - `qm_inevitability_route_bundle_without_shortcuts_v0`
- requirement:
  - theorem body must compose inevitability closure with full-derivation step-total and no-direct-insertion route obligations.

Mandatory anti-circularity / nontriviality guards:
- forbidden insertion token must be enforced on inevitability-critical theorem blocks:
  - `QM_FORBIDDEN_DIRECT_SCHRODINGER_INSERTION_v0`
- anti-circularity guard must remain explicit:
  - `QM_ANTI_CIRCULARITY_GUARD_v0: NO_DIRECT_SCHRODINGER_INSERTION`
- canonical theorem blocks must include explicit nontrivial obligations and must not reduce to definitional shortcuts.

Promotion gate rule:
- `QM_FULL_DERIVATION_INEVITABILITY_ADJUDICATION` may flip to `DISCHARGED_v0_BOUNDED` only when:
  - all required theorem tokens are present,
  - theorem-body route checks pass in inevitability gate tests,
  - state/results/roadmap surfaces are synchronized,
  - no forbidden-token leakage is detected.

Canonical pointers:
- `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md`
- `formal/toe_formal/ToeFormal/QM/QMFullDerivationScaffold.lean`
- `formal/python/tests/test_qm_inevitability_gate.py`
