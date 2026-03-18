# WS_09_POST_SIMPLIFICATION_VERIFICATION_SWEEP_PLAN_v0

## Workstream
- ID: WS-09
- Name: Post-Simplification Verification Sweep
- Status: DONE
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
| WS-09-T02 | Define bounded CE-05 validation matrix | DONE | WS-09-T01 | Validation matrix mapped to architecture/growth, authority, simplified seam families, governance suite | Matrix section with explicit command set |
| WS-09-T03 | Run targeted post-simplification checks | DONE | WS-09-T02 | Targeted check results with pass counts | Command outputs recorded in CE-05 checkpoint artifact |
| WS-09-T04 | Run governance suite checkpoint | DONE | WS-09-T03 | Governance suite result record | Command output and return status recorded in CE-05 checkpoint artifact |
| WS-09-T05 | Record CE-05 closure checkpoint | DONE | WS-09-T04 | CE-05 marked DONE in tracker with evidence | Tracker CE-05 row updated with artifact and commit chain |

## WS-09-T04 Remediation Subtasks
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-09-T04A | Create failing-governance-tranche triage note | DONE | none | Failure inventory, grouped root causes, remediation order, verification commands | Triage note committed and linked in tracker/plan |
| WS-09-T04B | Remediate smallest shared root-cause family first | DONE | WS-09-T04A | Family-B pillar/status consistency fix slice | Remaining failing subset decreases from 3 to <=1 with bounded diff evidence |
| WS-09-T04C | Re-run failing subset then canonical governance suite | DONE | WS-09-T04B | Green subset + green canonical governance suite | Command outputs recorded in CE-05 checkpoint artifact |

## CE-05 Bounded Validation Matrix (WS-09-T02)
| Lane | Scope | Command |
| --- | --- | --- |
| Architecture/growth guard | Architecture schema + state DAG guardrails | `./py.ps1 -m pytest -q formal/python/tests/test_architecture_schema_enforcement.py formal/python/tests/test_state_theory_dag.py` |
| Authority consistency | Residency-model consistency checkpoints | `./py.ps1 -m pytest -q formal/python/tests/test_pillar_deep_maturity_program_gate.py formal/python/tests/test_pillar_deep_maturity_m2_completion_gate.py` |
| Simplified seam representatives | WS-06 reduced helper/registry family representatives | `./py.ps1 -m pytest -q formal/python/tests/test_qft_full_derivation_token_flip_dryrun_representative_cycles37_50_gate.py formal/python/tests/test_qft_full_derivation_token_flip_dryrun_remaining_cycles38_49_gate.py` |
| Governance suite | End-to-end governance suite script | `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1` |

Execution contract:
- Run targeted lanes (first three rows) before governance suite.
- Record exact command text, pass counts, and exit status in `formal/docs/release/CE_05_POST_SIMPLIFICATION_VERIFICATION_CHECKPOINT_v0.md`.
- Do not mark CE-05 DONE until all four lanes succeed.

## Evidence Log
- 2026-03-18 WS-09-T01: Aligned compact state checkpoint fields in `State_of_the_Theory.md` with tracker authority and activated WS-09 slice in `formal/docs/release/REPO_REMEDIATION_MASTER_TRACKER_v0.md`.
- 2026-03-18 WS-09-T02: Added bounded CE-05 validation matrix and explicit command set spanning architecture/growth guard, authority consistency, simplified seam representatives, and governance suite.
- 2026-03-18 WS-09-T03: Ran bounded targeted checks and recorded `51 passed in 4.19s` in `formal/docs/release/CE_05_POST_SIMPLIFICATION_VERIFICATION_CHECKPOINT_v0.md`.
- 2026-03-18 WS-09-T04: First governance suite invocation failed at divergence guardrail (`ahead_count=24`, limit `20`); after divergence resolution and rerun, canonical suite still failed at governance pytest tranche (`14 failed, 408 passed`), recorded in CE-05 checkpoint artifact and run log.
- 2026-03-18 WS-09-T04A: Added `formal/docs/release/WS_09_T04A_FAILING_GOVERNANCE_TRANCHE_TRIAGE_NOTE_v0.md` with exact 14 failing tests, grouped failure families, remediation order, and expected verification commands.
- 2026-03-18 WS-09-T04B (Family-A slice): Restored required authority/state parity `ID` and `GapID` blocks in `State_of_the_Theory.md`; Family-A validation subset passed (`12 passed in 5.61s`) and was recorded in `formal/docs/release/CE_05_POST_SIMPLIFICATION_VERIFICATION_CHECKPOINT_v0.md`.
- 2026-03-18 WS-09-T04B full failing-tranche rerun (post commit `c677152`): exact 14-node subset returned `11 passed, 3 failed`; residual failures split into Family-B (2) and Family-C (1). Next bounded slice opened: Family-B.
- 2026-03-18 WS-09-T04B (Family-B slice): Family-B subset passed (`2 passed in 0.82s`) and bounded failing-tranche rerun reduced to single residual (`1 failed, 18 passed in 7.66s`), leaving Family-C conftest/signature stability as the only blocker.
- 2026-03-18 WS-09-T04C (Family-C + governance closure): conftest signature parity fixed in `formal/docs/release/CONFTEST_STABILITY_PROTOCOL_v0.md`; failing-tranche rerun passed (`19 passed in 7.21s`); first unchanged governance rerun surfaced 2 residual non-tranche gates, both remediated with bounded state/archive parity edits; final unchanged governance rerun passed (`422 passed in 141.30s`).

## Exit Criteria
- CE-05 validation matrix is explicit and bounded.
- Targeted checks and governance suite are executed with evidence.
- CE-05 row is set to DONE with artifact and commit-chain evidence.

## Notes
- WS-09 starts after WS-08 closure checkpoint commit `5e59c9b`.
- CE-06 remains a separate bounded slice after CE-05 completion.
