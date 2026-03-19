# Derivation Target: GR-QM Class-B Seam Promotion Discharge Cycle02 v0

Spec ID:
- `DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0`

Classification:
- `P-POLICY`

Purpose:
- Discharge the bounded theorem obligation for the pinned GR-QM cycle01 theorem pointer.
- Preserve `SEAM-GR-QM` as Class `B` during this tranche.
- Record auditable discharge posture prior to any class-flip request.

Non-claim boundary:
- bounded proof-discharge surface only.
- no Class-A promotion by itself.
- no registry class flip by itself.
- no full-derivation inevitability claim.
- no empirical adjudication by itself.

Cycle02 lineage anchors:
- `formal/docs/paper/DERIVATION_TARGET_GR_QM_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`

Cycle02 discharge bundle (bounded)
1. Witness package pointer:
- `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean`

2. Theorem pointer surface:
- `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean#gr_qm_seam_cycle01_theorem_pointer`

3. Discharge theorem pointer surface:
- `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean#gr_qm_seam_cycle02_discharge_proof`

4. No-shortcut / anti-circularity seam tag requirement:
- `NO_SHORTCUT_PROMOTION_CHECKLIST_PINNED_v0`

5. Discharge gate pointer:
- `formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py`

6. Explicitly excluded from cycle02:
- registry class flip (`B -> A`).

Cycle02 deliverables
- `DELIVERABLE-GR-QM-SEAM-PROMOTION-DISCHARGE-01_v0: CYCLE02_TARGET_PINNED`
- `DELIVERABLE-GR-QM-SEAM-PROMOTION-DISCHARGE-02_v0: BOUNDED_DISCHARGE_THEOREM_PINNED`
- `DELIVERABLE-GR-QM-SEAM-PROMOTION-DISCHARGE-03_v0: DISCHARGE_GATE_PINNED`
- `DELIVERABLE-GR-QM-SEAM-PROMOTION-DISCHARGE-04_v0: CLASS_B_RETENTION_PINNED`

Cycle02 discharge posture
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_STATUS_v0: PROOF_DISCHARGED_CLASS_B_PENDING_CLASS_FLIP_v0`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_THEOREM_STATUS_v0: DISCHARGED_BOUNDED_v0_NONCLAIM`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_DISCHARGE_THEOREM_v0: formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean#gr_qm_seam_cycle02_discharge_proof`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_DISCHARGE_GATE_v0: formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py`

Cycle02 bounded bridge statement
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_STATUS_v0: EXPLICIT_BOUNDED_v0_NONCLAIM`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_NAME_v0: CYCLE02_DISCHARGE_IMPLIES_CLASS_B_COMPATIBILITY_RETENTION`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_THEOREM_v0: formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean#gr_qm_cycle02_class_b_retention_bridge`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_HYPOTHESES_v0: CYCLE02_DISCHARGE_SURFACE_ESTABLISHED`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_BRIDGE_STATEMENT_CONCLUSION_v0: CLASS_B_COMPATIBILITY_SURFACE_RETAINED`
- Bounded interpretation: once the cycle02 discharge surface is established, the tranche retains the cycle01 Class-B compatibility surface while remaining explicitly non-promotional.

Cycle02 bounded compatibility persistence corollary
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_STATUS_v0: EXPLICIT_BOUNDED_v0_NONCLAIM`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_NAME_v0: CLASS_B_COMPATIBILITY_TAG_PERSISTS_AFTER_DISCHARGE`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_THEOREM_v0: formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean#gr_qm_cycle02_compatibility_tag_persistence`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_DEPENDS_ON_v0: gr_qm_cycle02_class_b_retention_bridge`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_HYPOTHESES_v0: CYCLE02_DISCHARGE_SURFACE_ESTABLISHED`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_COMPATIBILITY_PERSISTENCE_CONCLUSION_v0: TOE_CK_CLASS_COMPATIBILITY_v0_RETAINED`
- Bounded interpretation: the cycle02 discharge surface narrows to the retained compatibility tag without widening the tranche beyond Class `B`.

Cycle02 bounded retention transport corollary
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_RETENTION_TRANSPORT_STATUS_v0: EXPLICIT_BOUNDED_v0_NONCLAIM`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_RETENTION_TRANSPORT_NAME_v0: COMPATIBILITY_AND_NO_SHORTCUT_TAGS_TRANSPORT_TOGETHER`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_RETENTION_TRANSPORT_THEOREM_v0: formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean#gr_qm_cycle02_retention_transport_contract`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_RETENTION_TRANSPORT_DEPENDS_ON_v0: gr_qm_cycle02_compatibility_tag_persistence`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_RETENTION_TRANSPORT_HYPOTHESES_v0: CYCLE02_DISCHARGE_SURFACE_ESTABLISHED`
- `GR_QM_CLASS_B_PROMOTION_CYCLE02_RETENTION_TRANSPORT_CONCLUSION_v0: COMPATIBILITY_AND_NO_SHORTCUT_TAGS_RETAINED`
- Bounded interpretation: the cycle02 discharge contract transports the retained compatibility tag and the pinned no-shortcut tag as one bounded witness package without widening into class-flip semantics.

Exit posture (cycle02)
- `GR_QM_CLASS_B_PROMOTION_CLASS_v0: B_RETAINED_v0`
- Any `B -> A` move remains gated by the full promotion completion rule in `TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`.