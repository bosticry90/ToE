# TOE Formal Verification Authority Surface v0

Surface ID:
- `TOE_FORMAL_VERIFICATION_AUTHORITY_SURFACE_v0`

Purpose:
- provide one bounded authority surface for active formal theorem-bearing seams.
- mirror canonical Lean bridge files to Python gate and artifact surfaces.
- preserve non-claim posture while improving formal-to-operational traceability.

Non-claim boundary:
- this surface does not assert external truth.
- this surface does not promote class status beyond bounded governance semantics.

## Active formal bridge surfaces

1. GR-QM Class-B seam promotion bridge
- Lean surface: `formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean`
- Cycle01 gate: `formal/python/tests/test_gr_qm_seam_promotion_cycle01_theorem_gate.py`
- Cycle02 gate: `formal/python/tests/test_gr_qm_seam_promotion_cycle02_discharge_gate.py`
- Cycle03 gate: `formal/python/tests/test_gr_qm_seam_promotion_cycle03_class_flip_gate.py`
- Example artifact surface: `formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json`

2. EM-QFT Class-B seam promotion bridge
- Lean surface: `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean`
- Cycle01 gate: `formal/python/tests/test_em_qft_seam_promotion_cycle01_theorem_gate.py`
- Cycle02 gate: `formal/python/tests/test_em_qft_seam_promotion_cycle02_discharge_gate.py`
- Cycle03 gate: `formal/python/tests/test_em_qft_seam_promotion_cycle03_class_flip_gate.py`
- Example artifact surface: `formal/output/qft_m4_seam_closure_promotion_cycle01_v0.json`

3. BR01 dispersion-to-metric bridge
- Lean surface: `formal/toe_formal/ToeFormal/Bridges/BR01_DispersionToMetric.lean`
- Bridge gate: `formal/python/tests/test_br01_front_door_enforced.py`
- Example artifact surface: `formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json`

## Operational parity gate
- Parity gate: `formal/python/tests/test_formal_python_bridge_parity_gate.py`
- Gate objective: ensure bridge surfaces, exemplar artifacts, and gate paths stay resolvable.
