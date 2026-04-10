# Repo Promote/Archive/Prune Checklist v0

Document ID: REPO_PROMOTE_ARCHIVE_PRUNE_CHECKLIST_v0
Owner: Governance
Status: Active
Last-Updated: 2026-03-11

Purpose:
- Record explicit disposition decisions for repository surfaces relative to the canonical ToE governance and physics workflow.
- Reduce ambiguity between active canonical surfaces and intentionally disconnected retention/exploration surfaces.

Non-claim boundary:
- bookkeeping and workflow hygiene only.
- no theorem promotion.
- no matrix-status promotion.
- no empirical claim.

## Decision Table

1. Keep disconnected by policy (no promotion planned):
- archive/
- backup/
- scratch/
- formal/quarantine/
- formal/tooling_snapshots/

Rationale:
- these are retention/exploration scopes with explicit governance boundaries.
- they must not become active import or adjudication surfaces without explicit promotion workflow.

2. Archive/reference hold (outdated or exploratory):
- archive/docs/Deepening.txt (moved from repo root as reference-only)
- GOVERNANCE_VERSION_v1.lock (historical lock; superseded by GOVERNANCE_VERSION_v2.lock)
- formal/aristotle/claim_registry.yaml (exploratory hold unless Aristotle lane is reactivated)

3. Advisory documents (keep as non-canonical planning aids unless explicitly promoted):
- Action Plan.txt
- Integration Proposal.txt
- Viability Roadmap.txt
- Legacy_Reintegration_Register.md

Promotion requirement for advisory/exploratory docs:
- explicit State_of_the_Theory.md pointer and bounded role statement,
- formal/docs canonicalization under formal/docs/paper or formal/docs/release,
- at least one corresponding governance gate in formal/python/tests when behavior/enforcement is implied.

4. Active canonical governance/tooling infrastructure (do not prune):
- State_of_the_Theory.md
- formal/docs/paper/PHYSICS_ROADMAP_v0.md
- governance_suite.ps1
- py.ps1
- ARCHITECTURE_SCHEMA_v1.json (schema_id ARCHITECTURE_SCHEMA_v2)
- GOVERNANCE_VERSION_v2.lock

## Immediate Actions Completed

- Deepening.txt archived to archive/docs/Deepening.txt with reference-only posture.
- Governance v1 lock marked historical in state surface; v2 remains canonical lock authority.
- Aristotle claim registry marked exploratory hold pending explicit reactivation workflow.

## Future Promotion Trigger (Aristotle Lane)

If Aristotle lane is reactivated, minimum entry criteria:
1. Add bounded inventory entry in State_of_the_Theory.md with explicit non-claim status.
2. Add one front-door policy/gate test under formal/python/tests.
3. Add canonical pointers in PHYSICS_ROADMAP_v0.md and state surface.

Canonical pointers:
- state surface: State_of_the_Theory.md
- roadmap surface: formal/docs/paper/PHYSICS_ROADMAP_v0.md
- retention policy: formal/docs/release/REPOSITORY_RETENTION_POLICY_v0.md
- legacy register: Legacy_Reintegration_Register.md
