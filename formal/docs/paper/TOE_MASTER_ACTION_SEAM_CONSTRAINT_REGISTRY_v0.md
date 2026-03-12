# ToE Master Action Seam Constraint Registry v0

Spec ID:
- `TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0`

Classification:
- `P-POLICY`

Purpose:
- Enumerate seam-constraint classes `C_k` for the working-form master action.
- Make cross-pillar compatibility requirements auditable.
- Separate theorem-linked constraints from policy-level placeholders.

Non-claim boundary:
- registry/control artifact only.
- no theorem promotion by itself.
- no canonical action promotion by itself.
- no empirical adequacy claim.

Canonical anchors:
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md`
- `formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_EXECUTION_PLAN_v0.md`
- `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean`
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean`
- `formal/python/tests/test_toe_master_action_seam_registry_gate.py`
- `formal/python/tests/test_toe_master_action_assumption_classification_gate.py`
- `formal/python/tests/test_toe_master_action_class_b_inventory_gate.py`
- `formal/python/tests/test_em_qft_seam_promotion_cycle01_theorem_gate.py`
- `formal/python/tests/test_em_qft_seam_promotion_cycle02_discharge_gate.py`
- `formal/python/tests/test_em_qft_seam_promotion_cycle03_class_flip_gate.py`

Registry posture token:
- `TOE_MASTER_ACTION_SEAM_REGISTRY_STATUS_v0: SCAFFOLD_PINNED_NONCLAIM`

## Seam constraint classes (C_k)

1. Compatibility constraints:
- token: `TOE_CK_CLASS_COMPATIBILITY_v0`
- meaning: enforce admissible cross-pillar object compatibility and interface contracts.

2. Bridge admissibility constraints:
- token: `TOE_CK_CLASS_BRIDGE_ADMISSIBILITY_v0`
- meaning: require witness/constructor route validity from variation surfaces to operator surfaces.

3. Transport consistency constraints:
- token: `TOE_CK_CLASS_TRANSPORT_CONSISTENCY_v0`
- meaning: preserve operator obligations under allowed transport theorem routes.

4. Regime-interface boundedness constraints:
- token: `TOE_CK_CLASS_REGIME_INTERFACE_BOUNDEDNESS_v0`
- meaning: preserve bounded validity assumptions when taking regime limits.

## Per-pillar mapping scaffold (v0)

QM lane mapping:
- compatibility surface pointer: `formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md`
- M3 lane pointer: `formal/docs/paper/DERIVATION_TARGET_QM_M3_COMPLETION_PROMOTION_v0.md`

GR lane mapping:
- compatibility surface pointer: `formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md`
- M3 lane pointer: `formal/docs/paper/DERIVATION_TARGET_GR_M3_COMPLETION_PROMOTION_v0.md`

STAT lane mapping:
- compatibility surface pointer: `formal/docs/paper/DERIVATION_TARGET_STAT_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- M3 lane pointer: `formal/docs/paper/DERIVATION_TARGET_STAT_M3_COMPLETION_PROMOTION_v0.md`

COSMO lane mapping:
- compatibility surface pointer: `formal/docs/paper/DERIVATION_TARGET_COSMO_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- M3 lane pointer: `formal/docs/paper/DERIVATION_TARGET_COSMO_M3_COMPLETION_PROMOTION_v0.md`

EM lane mapping:
- compatibility surface pointer: `formal/docs/paper/DERIVATION_TARGET_EM_M4_SEAM_CLOSURE_PROMOTION_v0.md`
- M3 lane pointer: `formal/docs/paper/DERIVATION_TARGET_EM_M3_COMPLETION_PROMOTION_v0.md`

QFT lane mapping:
- compatibility surface pointer: `formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md`
- M3 lane pointer: `formal/docs/paper/DERIVATION_TARGET_QFT_M3_COMPLETION_PROMOTION_v0.md`

SR lane mapping:
- compatibility surface pointer: `formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md`
- M3 lane pointer: `formal/docs/paper/DERIVATION_TARGET_SR_M3_COMPLETION_PROMOTION_v0.md`

## Assumption classification and minimization delta log (v0)

Assumption classification token:
- `TOE_MASTER_ACTION_ASSUMPTION_CLASSIFICATION_STATUS_v0: SCAFFOLD_PINNED_NONCLAIM`

Class A (theorem-linked constraints):
- explicit theorem/target-linked assumptions already pinned in lane authority docs.
- minimization stance: preserve theorem signatures; reduce duplicate narrative assumptions.
- class token for promoted seam rows: `TOE_CK_CLASS_THEOREM_LINKED_v0`.

Class B (policy-level placeholders):
- seam constraints still described by policy names only.
- minimization stance: convert policy labels to theorem-linked objects when witness routes are available.

Class C (speculative scaffolds):
- statistical/information term interfaces with no unified theorem body yet.
- minimization stance: remain bounded and non-canonical until route-level proof surfaces exist.

Delta objectives:
1. Reduce duplicated policy assumptions across lane docs.
2. Promote Class B entries to Class A only with explicit theorem witness pointers.
3. Keep Class C entries explicit and non-promoted until bridge and transport closure exists.

## Class-B promotion tranche (cycle01)

Class-B inventory pointer:
- `formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md`

Pilot promotion target pointer:
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CYCLE01_v0.md`

Witness package schema pointer:
- `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean`

Theorem pointer (cycle01):
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle01_theorem_pointer`

Theorem gate pointer (cycle01):
- `formal/python/tests/test_em_qft_seam_promotion_cycle01_theorem_gate.py`

Discharge target pointer (cycle02):
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_DISCHARGE_CYCLE02_v0.md`

Discharge theorem pointer (cycle02):
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle02_discharge_proof`

Discharge gate pointer (cycle02):
- `formal/python/tests/test_em_qft_seam_promotion_cycle02_discharge_gate.py`

Class-flip target pointer (cycle03):
- `formal/docs/paper/DERIVATION_TARGET_EM_QFT_CLASS_B_SEAM_PROMOTION_CLASS_FLIP_CYCLE03_v0.md`

Class-flip authorization theorem pointer (cycle03):
- `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean#em_qft_seam_cycle03_class_flip_authorization`

Class-flip gate pointer (cycle03):
- `formal/python/tests/test_em_qft_seam_promotion_cycle03_class_flip_gate.py`

Cycle01 pilot lock:
- `TOE_CLASS_B_PROMOTION_PILOT_SEAM_v0: SEAM-EM-QFT`
- `TOE_CLASS_B_PROMOTION_PILOT_CLASS_v0: TOE_CK_CLASS_COMPATIBILITY_v0`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE01_STATUS_v0: THEOREM_POINTER_PINNED_v0_COMPLETE`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE02_STATUS_v0: PROOF_DISCHARGED_CLASS_B_PENDING_CLASS_FLIP_v0`
- `EM_QFT_CLASS_B_PROMOTION_CYCLE03_STATUS_v0: CLASS_A_PROMOTED_v0_NONCLAIM`
