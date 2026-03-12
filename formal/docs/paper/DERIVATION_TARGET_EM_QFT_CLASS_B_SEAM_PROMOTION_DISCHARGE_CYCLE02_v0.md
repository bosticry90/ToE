# Derivation Target: EM-QFT Class-B Seam Promotion Discharge Cycle02 v0

Spec ID:
- `DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0`

Classification:
- `P-POLICY`

Purpose:
- Discharge the bounded theorem obligation for the already pinned EM-QFT cycle01 theorem pointer.
- Preserve `SEAM-EM-QFT` as Class `B` during this tranche.
- Record auditable discharge posture prior to any class-flip request.

Non-claim boundary:
- bounded proof-discharge surface only.
- no Class-A promotion by itself.
- no registry class flip by itself.
- no full-derivation inevitability claim.
- no empirical adjudication by itself.

Cycle02 lineage anchors:
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md`

Cycle02 discharge bundle (bounded)
1. Witness package pointer:
- `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean`

2. Theorem pointer surface:
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle01_theorem_pointer`

3. Discharge theorem pointer surface:
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle02_discharge_proof`

4. No-shortcut / anti-circularity seam tag requirement:
- `NO_SHORTCUT_PROMOTION_CHECKLIST_PINNED_v0`

5. Discharge gate pointer:
- `formal/python/tests/test_em_qft_seam_promotion_cycle02_discharge_gate.py`

6. Explicitly excluded from cycle02:
- registry class flip (`B -> A`).

Cycle02 deliverables
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-DISCHARGE-01_v0: CYCLE02_TARGET_PINNED`
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-DISCHARGE-02_v0: BOUNDED_DISCHARGE_THEOREM_PINNED`
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-DISCHARGE-03_v0: DISCHARGE_GATE_PINNED`
- `DELIVERABLE-EM-QFT-SEAM-PROMOTION-DISCHARGE-04_v0: CLASS_B_RETENTION_PINNED`

Cycle02 discharge posture
- `EM_QFT_CLASS_B_PROMOTION_CYCLE02_STATUS_v0: PROOF_DISCHARGED_CLASS_B_PENDING_CLASS_FLIP_v0`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE02_THEOREM_STATUS_v0: DISCHARGED_BOUNDED_v0_NONCLAIM`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE02_DISCHARGE_THEOREM_v0: formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle02_discharge_proof`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE02_DISCHARGE_GATE_v0: formal/python/tests/test_em_qft_seam_promotion_cycle02_discharge_gate.py`

Exit posture (cycle02)
- `EM_QFT_CLASS_B_PROMOTION_CLASS_v0: B_RETAINED_v0`
- Any `B -> A` move remains gated by the full promotion completion rule in `TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`.
