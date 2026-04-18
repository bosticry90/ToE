# Derivation Target: ToE Master Action Computational Analysis Packet 01 Refinement 01 v0

Spec ID:
- `DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_v0`

Target ID:
- `TARGET-TOE-MASTER-ACTION-COMPUTATIONAL-ANALYSIS-PACKET-01-REFINEMENT-01-v0`

Classification:
- `P-POLICY`

Purpose:
- Run exactly one bounded Packet-01 refinement under the already-recorded `REFINE_v0` decision.
- Preserve the auxiliary computational-analysis authorization class and the forced packet-level `INCONCLUSIVE_v0` ceiling.
- Change only one narrow perturbation-window control so the refinement remains directly comparable to the baseline.

Non-claim boundary:
- bounded refinement surface only.
- no Packet-02 authorization.
- no GPU backend authorization.
- no lane reopen claim.
- no blocker-movement claim.
- no external-truth claim.

Refinement bundle:
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM`
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_AUTHORIZATION_CLASS_v0: AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_DECISION_v0: INCONCLUSIVE_v0`
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_ARTIFACT_v0: toe_master_action_computational_analysis_packet_01_refinement_01_v0`
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_GATE_v0: formal/python/tests/test_toe_master_action_computational_analysis_packet_01_refinement_01_gate.py`
- artifact path: `formal/output/toe_master_action_computational_analysis_packet_01_refinement_01_v0.json`

Single allowed variation:
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_VARIATION_ID_v0: PERTURBATION_WINDOW_TIGHTENING_v0`
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_PARAMETER_v0: MAX_PERTURBATION_MAGNITUDE`
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_BASELINE_VALUE_v0: 0.03`
- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_REFINED_VALUE_v0: 0.02`

Refinement rule:
- all Packet-01 assumptions, model object, local state support, observables, and discriminator semantics remain fixed.
- only the perturbation-window ceiling is tightened from `0.03` to `0.02` while preserving the same three-point schedule shape.
- no second operator family, no residual-map substitution, no comparator-lane expansion, no second refinement, and no backend change are authorized.

Executed refinement surface:
- report tool: `formal/python/tools/toe_master_action_computational_analysis_packet_01_refinement_01_report.py`
- report path: `formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json`

Closeout surface:
- decision record: `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_CLOSEOUT_DECISION_RECORD_v0.md`
- decision report tool: `formal/python/tools/toe_master_action_computational_analysis_packet_01_refinement_closeout_decision_report.py`
- decision report path: `formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_closeout_20260417_v0.json`

Canonical pointers:
- baseline packet target: `formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md`
- baseline packet artifact: `formal/output/toe_master_action_computational_analysis_packet_01_v0.json`
- baseline executed report: `formal/output/reports/toe_master_action_computational_analysis_packet_01_20260417_v0.json`
- baseline decision report: `formal/output/reports/toe_master_action_computational_analysis_packet_01_decision_20260417_v0.json`
- refinement gate: `formal/python/tests/test_toe_master_action_computational_analysis_packet_01_refinement_01_gate.py`

Execution guardrails:
- one refinement only.
- same auxiliary authorization class only.
- same forced `INCONCLUSIVE_v0` packet ceiling only.
- no Packet-02 pointer.
- no GPU or quantum-native execution.
- no lane reopen or blocker semantics.