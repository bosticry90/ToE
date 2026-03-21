# WS-10 T06 Supersede by QFT-GR Reactivation Decision v0

Decision ID:
- `WS_10_T06_SUPERSEDE_BY_QFT_GR_REACTIVATION_DECISION_v0`

Classification:
- `R-DECISION`

Purpose:
- Resolve `WS-10-T06_GR_QM_POST_COMPLETION_HANDOFF_BOUNDARY` by explicit supersession.
- Activate QFT-GR seam reactivation as the next authorized non-GR-QM lane.

Resolution statement:
- GR-QM completion remains canonically closed.
- T06 handoff boundary is resolved by supersession, not by additional GR-QM completion-lane theorem work.
- The newly authorized successor lane is `WS-10-T07_QFT_GR_SEAM_REACTIVATION_AUTHORIZATION_BOUNDARY`.

Bounded invariance constraints:
1. Scalar freeze remains unchanged.
2. Workflow-simplification line remains closed.
3. Packet42 hold remains unchanged.
4. No GR-QM completion theorem-surface edits are authorized in this supersede slice.

Pinned successor anchor:
- `formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md`

Pinned successor science question:
- `stress_energy_to_weak_curvature_handoff_strengthening`

Required parity surfaces:
- `formal/docs/release/WS_10_THEORY_RESTART_PILOT_PLAN_v0.md`
- `formal/docs/release/REPO_REMEDIATION_MASTER_TRACKER_v0.md`
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`

Validation ladder (Slice A):
1. `./py.ps1 -m pytest -q formal/python/tests/test_state_theory_dag.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
3. `./py.ps1 -m pytest -q formal/python/tests/test_toe_seam_status_split_gate.py`
4. `./py.ps1 -m pytest -q formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py formal/python/tests/test_toe_master_action_class_b_inventory_gate.py formal/python/tests/test_toe_master_action_seam_registry_gate.py`
5. `./py.ps1 -m pytest -q formal/python/tests/test_toe_qft_gr_seam_reactivation_objective_gate.py`

Status tokens:
- `WS_10_T06_SUPERSEDE_DECISION_STATUS_v0: COMPLETE_VALIDATED_BOUNDED_v0`
- `WS_10_T06_SUPERSEDE_OUTCOME_v0: SUPERSEDE_TO_QFT_GR_REACTIVATION`
- `WS_10_T06_SUPERSEDE_PACKET42_HOLD_STATUS_v0: UNCHANGED_HOLD`
- `WS_10_T06_SUPERSEDE_SCALAR_FREEZE_STATUS_v0: UNCHANGED`
- `WS_10_T06_SUPERSEDE_WORKFLOW_STATUS_v0: CLOSED_UNCHANGED`

Validation evidence:
- `SLICE_A_SUPERSEDE_VALIDATION_v0: 14_PASSED_IN_5_87S`

Non-claim boundary:
- This decision does not lift Packet42 hold.
- This decision does not claim QFT-GR seam closure.
- This decision does not authorize broader speculative physics claims.
