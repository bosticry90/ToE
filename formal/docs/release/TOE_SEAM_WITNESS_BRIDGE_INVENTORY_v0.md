# TOE Seam Witness Bridge Inventory v0

Inventory ID:
- `TOE_SEAM_WITNESS_BRIDGE_INVENTORY_v0`

Scope:
- bounded inventory of active seam witness bridges.
- intended for governance traceability and parity checks.

## Row schema
- `bridge_id`
- `lean_surface`
- `cycle_scope`
- `python_gates`
- `example_artifact`
- `status`

## Rows

- `bridge_id: BRIDGE_GR_QM_CLASS_B`
- `lean_surface: formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`
- `cycle_scope: CYCLE01_TO_CYCLE03`
- `python_gates: test_gr_qm_seam_promotion_cycle01_theorem_gate.py;test_gr_qm_seam_promotion_cycle02_discharge_gate.py;test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`
- `example_artifact: formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json`
- `status: ACTIVE_BOUNDED_NONCLAIM`

- `bridge_id: BRIDGE_EM_QFT_CLASS_B`
- `lean_surface: formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean`
- `cycle_scope: CYCLE01_TO_CYCLE03`
- `python_gates: test_em_qft_seam_promotion_cycle01_theorem_gate.py;test_em_qft_seam_promotion_cycle02_discharge_gate.py;test_em_qft_seam_promotion_cycle03_class_flip_gate.py`
- `example_artifact: formal/output/qft_m4_seam_closure_promotion_cycle01_v0.json`
- `status: ACTIVE_BOUNDED_NONCLAIM`

- `bridge_id: BRIDGE_BR01_DISPERSION_TO_METRIC`
- `lean_surface: formal/toe_formal/ToeFormal/Bridges/BR01_DispersionToMetric.lean`
- `cycle_scope: CYCLE01`
- `python_gates: test_br01_front_door_enforced.py`
- `example_artifact: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json`
- `status: ACTIVE_BOUNDED_NONCLAIM`
