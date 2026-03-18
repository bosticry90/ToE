# WS_06_REPETITION_REDUCTION_PHASE2_PLAN_v0

## Workstream
- ID: WS-06
- Name: Repetition Reduction Phase 2
- Status: DONE
- Priority: PRIMARY

## Objective
Consolidate one large repeated gate family using shared helper logic and/or registry-driven parametrization while preserving bounded governance rigor.

## Scope
In scope:
- selection of one repeated gate family for reduction.
- baseline clone-surface measurement for selected family.
- extraction of shared helper and/or parametrized coverage path.
- bounded validation against representative and family-level tests.

Out of scope during WS-06:
- new theorem-route expansion.
- new packet-family expansion unrelated to repetition reduction.
- broad multi-family refactors in a single commit.

## Selected Family and Baseline (WS-06-T01)
- Selected family pattern: `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_*_cycle*_gate.py`
- Baseline file count: 14 files.
- Rationale: highly repetitive cycle-labeled gates with near-identical structure and token assertions.
- Candidate reduction strategy:
  - shared helper module for common path/token checks.
  - parametrized test over cycle metadata (cycle id, token tuple, artifact key).
- T02 mapping and interface contract pointer:
  - `formal/docs/release/WS_06_DRYRUN_TOKEN_FLIP_FAMILY_MAPPING_v0.md`

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-06-T01 | Select repeated family and baseline clone surface | DONE | none | Family selection + baseline count in this plan | File commit + tracker linkage |
| WS-06-T02 | Define reduction contract and helper interface | DONE | WS-06-T01 | Helper API and parametrization contract | Draft helper + mapping table |
| WS-06-T03 | Implement shared helper and representative parametrized gate | DONE | WS-06-T02 | First reduced slice committed | Targeted pytest output |
| WS-06-T04 | Fold remaining selected family members to reduced pattern | DONE | WS-06-T03 | Family reduction committed | Family-level pytest output |
| WS-06-T05 | Record WS-06 completion checkpoint | DONE | WS-06-T04 | WS-06 closure row in master tracker | Exit criteria all satisfied |

## Evidence Log
- 2026-03-18 WS-06-T01: Selected dryrun token-flip family (`test_qft_full_derivation_token_flip_dryrun_*_cycle*_gate.py`) with baseline clone surface count = 14 files.
- 2026-03-18 WS-06-T02: Drafted helper API and full cycle mapping contract in `formal/docs/release/WS_06_DRYRUN_TOKEN_FLIP_FAMILY_MAPPING_v0.md` for cycles 37 through 50.
- 2026-03-18 WS-06-T03: Added shared helper module `formal/python/tests/qft_full_derivation_token_flip_dryrun_helpers.py` and representative parametrized gate `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_representative_cycles37_50_gate.py`; targeted pytest passed (`6 passed in 0.73s`).
- 2026-03-18 WS-06-T04: Added reduced-pattern remaining-cycles gate `formal/python/tests/test_qft_full_derivation_token_flip_dryrun_remaining_cycles38_49_gate.py`; bounded family-level reduced-path pytest passed (`42 passed in 1.68s`).
- 2026-03-18 WS-06-T05: Closure checkpoint recorded in master tracker with completion evidence chain (`e96adbb`, `dd9bb12`, `8fecd0e`).

## Exit Criteria
- Selected repeated family is reduced to shared helper and/or parametrized form.
- Family-level validation passes in bounded runs.
- Tracker reflects reduced surface with evidence.

## Notes
- WS-06 starts from WS-05 closure checkpoint commit `3bf1350`.
- Unrelated existing working-tree drift remains out of scope.
