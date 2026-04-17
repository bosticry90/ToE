# SCIENCE_DORMANCY_RESTART_PLAYBOOK_20260412_v0

Status: ACTIVE_NONLIVE_NONCLAIM

Purpose:
- Preserve controlled dormancy as the default operating mode after P76.
- Define the only authorized restart front door and sequencing.

Canonical anchors:
- Frontier stop-state decision commit: 1a2c1ac
- Frontier stop-state summary commit: f8fc4bd
- Restart trigger contract commit: ba04a71
- Controlled dormancy protocol commit: e190f98
- Dormancy preservation audit operational capstone commit: 92f33e3
- Latest clarification checkpoint commit: 7729065

Clarification status:
- 92f33e3 remains the P77 operational capstone.
- 7729065 is a documentation clarification checkpoint only, not a new policy layer.

Package status:
- The current P77 playbook plus audit declaration, audit tool, audit gate, and canonical audit report form the canonical dormancy enforcement package.

Standard restart package order:
1. SCIENCE_FRONTIER_STOP_STATE_SUMMARY_20260412_v0.md
2. State_of_the_Theory.md
3. SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json
4. SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_20260412_v0.json
5. SCIENCE_DORMANCY_RESTART_PLAYBOOK_20260412_v0.md
6. SCIENCE_DORMANCY_PRESERVATION_AUDIT_20260412_v0.json

Minimum restart-entry sequence:
1. SCIENCE_FRONTIER_STOP_STATE_SUMMARY_20260412_v0.md
2. State_of_the_Theory.md
3. SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json
4. SCIENCE_DORMANCY_PRESERVATION_AUDIT_20260412_v0.json

Dormancy operating rule:
- No active lane work.
- No packet execution.
- No candidate-specific execution tranches.
- External evidence monitoring and bounded ideation are allowed.

Restart sequencing rule:
1. Start at P75 restart trigger contract.
2. Ask: is there a valid trigger family?
3. If no, remain in governed stop-state and preserve dormancy.
4. Use the minimum restart-entry sequence before any restart discussion or escalation.
5. Require both P75 trigger-family legality and P77 dormancy-preservation audit clearance before any lane reopen or packet authorization.
6. If both clear, open at most one bounded pre-screening gate with no direct execution authorization.
7. Lane reopen decisions can only occur after trigger-family legality is established through the restart front door and the dormancy preservation audit remains passing.

Forbidden sequencing:
- Do not start restart by selecting a lane.
- Do not bypass trigger-family checks.
- Do not authorize direct execution from dormancy.

Non-claim boundary:
- Operational governance playbook only; no scientific adequacy claim.
