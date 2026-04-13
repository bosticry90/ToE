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

Dormancy operating rule:
- No active lane work.
- No packet execution.
- No candidate-specific execution tranches.
- External evidence monitoring and bounded ideation are allowed.

Restart sequencing rule:
1. Start at P75 restart trigger contract.
2. Ask: is there a valid trigger family?
3. If no, remain in governed stop-state and preserve dormancy.
4. If yes, open at most one bounded pre-screening gate with no direct execution authorization.
5. Lane reopen decisions can only occur after trigger-family legality is established through the restart front door.

Forbidden sequencing:
- Do not start restart by selecting a lane.
- Do not bypass trigger-family checks.
- Do not authorize direct execution from dormancy.

Non-claim boundary:
- Operational governance playbook only; no scientific adequacy claim.
