# Derivation Target: EM-QFT Class-B Seam Promotion Cycle01 v0

Spec ID:
- `DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0`

Classification:
- `P-POLICY`

Purpose:
- Execute the first pilot tranche for Class-B to Class-A seam promotion.
- Target seam: `SEAM-EM-QFT` under compatibility constraints.
- Pin witness-package and gate requirements before any class-status flip.

Non-claim boundary:
- promotion-plan surface only.
- no class-status flip by itself.
- no theorem promotion by itself.
- no empirical adjudication by itself.

Pilot seam token:
- `TOE_CLASS_B_PROMOTION_PILOT_SEAM_v0: SEAM-EM-QFT`
- `TOE_CLASS_B_PROMOTION_PILOT_CLASS_v0: TOE_CK_CLASS_COMPATIBILITY_v0`

Required promotion bundle (cycle01)
1. Witness package pointer:
- `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean`

2. Seam inventory pointer:
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`

3. Registry pointer:
- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`

4. Pilot gate pointer:
- `formal/python/tests/test_toe_master_action_class_b_inventory_gate.py`

5. Theorem pointer:
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle01_theorem_pointer`

6. Theorem gate pointer:
- `formal/python/tests/test_em_qft_seam_promotion_cycle01_theorem_gate.py`

5. Existing seam closure evidence anchors:
- `formal/output/em_m4_seam_closure_promotion_cycle01_v0.json`
- `formal/output/qft_m4_seam_closure_promotion_cycle01_v0.json`

Cycle01 deliverables
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-01_v0: CLASS_B_INVENTORY_ROW_PINNED`
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-02_v0: WITNESS_PACKAGE_SCHEMA_PINNED`
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-03_v0: NO_SHORTCUT_PROMOTION_CHECKLIST_PINNED`
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-04_v0: THEOREM_POINTER_AND_GATE_PINNED`

Cycle01 theorem pointer lock
- `EM_QFT_CLASS_B_PROMOTION_CYCLE01_THEOREM_STATUS_v0: THEOREM_POINTER_PINNED_v0_NONCLAIM`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE01_THEOREM_POINTER_v0: formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle01_theorem_pointer`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE01_THEOREM_GATE_v0: formal/python/tests/test_em_qft_seam_promotion_cycle01_theorem_gate.py`

Cycle01 exit posture
- `EM_QFT_CLASS_B_PROMOTION_CYCLE01_STATUS_v0: THEOREM_POINTER_PINNED_PENDING_PROOF_DISCHARGE`
- Class status remains `B` until theorem pointer + executable gate evidence are both pinned.
