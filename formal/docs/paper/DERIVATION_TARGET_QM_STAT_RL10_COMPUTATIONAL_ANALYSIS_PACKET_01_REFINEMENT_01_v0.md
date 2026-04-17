# Derivation Target: QM-STAT RL10 Computational Analysis Packet 01 Refinement 01 v0

Spec ID:
- `DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_v0`

Target ID:
- `TARGET-QM-STAT-RL10-COMPUTATIONAL-ANALYSIS-PACKET-01-REFINEMENT-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Run exactly one bounded Packet-01 refinement under the already-recorded `REFINE_v0` decision.
- Preserve the auxiliary computational-analysis authorization class and the forced packet-level `INCONCLUSIVE_v0` ceiling.
- Change only one narrow comparator-sensitivity control parameter so the refinement is directly comparable to the baseline.

Non-claim boundary:
- bounded refinement surface only.
- no Packet-02 authorization.
- no restart implication.
- no blocker-movement claim.
- no lane reopen claim.
- no external-truth claim.

Refinement bundle:
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_AUTHORIZATION_CLASS_v0: AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_DECISION_v0: INCONCLUSIVE_v0`
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_ARTIFACT_v0: qm_stat_rl10_computational_analysis_packet_01_refinement_01_v0`
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_GATE_v0: formal/python/tests/test_qm_stat_rl10_computational_analysis_packet_01_refinement_01_gate.py`
- artifact path: `formal/output/qm_stat_rl10_computational_analysis_packet_01_refinement_01_v0.json`

Single allowed variation:
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_VARIATION_ID_v0: COMPARATOR_MARGIN_TIGHTENING_v0`
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_PARAMETER_v0: COMPARATOR_SENSITIVITY_MARGIN_FLOOR`
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_BASELINE_VALUE_v0: 0.00`
- `QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_REFINED_VALUE_v0: 0.06`

Refinement rule:
- all Packet-01 assumptions, model objects, observables, and discriminator semantics remain fixed.
- only the comparator-sensitivity margin floor is tightened.
- no additional comparator, probe path, state-space expansion, or second refinement is authorized.

Executed refinement surface:
- report tool: `formal/python/tools/qm_stat_rl10_computational_analysis_packet_01_refinement_01_report.py`
- report path: `formal/output/reports/qm_stat_rl10_computational_analysis_packet_01_refinement_01_20260416_v0.json`

Closeout surface:
- decision record: `formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_DECISION_RECORD_v0.md`
- decision report tool: `formal/python/tools/qm_stat_rl10_computational_analysis_packet_01_refinement_closeout_decision_report.py`
- decision report path: `formal/output/reports/qm_stat_rl10_computational_analysis_packet_01_refinement_closeout_20260416_v0.json`

Canonical pointers:
- baseline packet target: `formal/docs/paper/DERIVATION_TARGET_QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md`
- baseline executed report: `formal/output/reports/qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json`
- baseline decision report: `formal/output/reports/qm_stat_rl10_computational_analysis_packet_01_decision_20260416_v0.json`
- refinement gate: `formal/python/tests/test_qm_stat_rl10_computational_analysis_packet_01_refinement_01_gate.py`

Execution guardrails:
- one refinement only.
- same auxiliary authorization class only.
- same forced `INCONCLUSIVE_v0` packet ceiling only.
- no Packet-02 pointer.
- no restart or blocker semantics.