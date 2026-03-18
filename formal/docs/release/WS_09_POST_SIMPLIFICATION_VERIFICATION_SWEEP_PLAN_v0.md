# WS_09_POST_SIMPLIFICATION_VERIFICATION_SWEEP_PLAN_v0

## Workstream
- ID: WS-09
- Name: Post-Simplification Verification Sweep
- Status: ACTIVE
- Priority: PRIMARY

## Objective
Close CE-05 with bounded, evidence-backed verification that relevant governance and seam checks pass after consolidation changes.

## Scope
In scope:
- reconcile compact state checkpoint fields with tracker authority.
- define bounded CE-05 validation matrix and command set.
- execute targeted checks and governance suite in controlled order.
- record CE-05 closure evidence in a single checkpoint artifact.

Out of scope during WS-09:
- CE-06 anti-regrowth guardrail implementation.
- theorem-route expansion.
- broad refactors outside verification and evidence surfaces.

## CE-05 Checkpoint Artifact Target
- `formal/docs/release/CE_05_POST_SIMPLIFICATION_VERIFICATION_CHECKPOINT_v0.md`

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-09-T01 | Align compact state surface with tracker checkpoint fields | DONE | none | Tracker/state alignment for primary workstream, active task, and checkpoint wording | Bounded tracker+state diff evidence |
| WS-09-T02 | Define bounded CE-05 validation matrix | ACTIVE | WS-09-T01 | Validation matrix mapped to architecture/growth, authority, simplified seam families, governance suite | Matrix section with explicit command set |
| WS-09-T03 | Run targeted post-simplification checks | TODO | WS-09-T02 | Targeted check results with pass counts | Command outputs recorded in CE-05 checkpoint artifact |
| WS-09-T04 | Run governance suite checkpoint | TODO | WS-09-T03 | Governance suite result record | Command output and return status recorded in CE-05 checkpoint artifact |
| WS-09-T05 | Record CE-05 closure checkpoint | TODO | WS-09-T04 | CE-05 marked DONE in tracker with evidence | Tracker CE-05 row updated with artifact and commit chain |

## Evidence Log
- 2026-03-18 WS-09-T01: Aligned compact state checkpoint fields in `State_of_the_Theory.md` with tracker authority and activated WS-09 slice in `formal/docs/release/REPO_REMEDIATION_MASTER_TRACKER_v0.md`.

## Exit Criteria
- CE-05 validation matrix is explicit and bounded.
- Targeted checks and governance suite are executed with evidence.
- CE-05 row is set to DONE with artifact and commit-chain evidence.

## Notes
- WS-09 starts after WS-08 closure checkpoint commit `5e59c9b`.
- CE-06 remains a separate bounded slice after CE-05 completion.
