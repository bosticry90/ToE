# WS_02_SURFACE_REDUCTION_PLAN_v0

## Workstream
- ID: WS-02
- Name: Surface Reduction
- Status: DONE
- Priority: COMPLETED

## Objective
Reduce duplicated gate and test surface while preserving bounded governance semantics.

## Task Plan
| ID | Task | Status | Blocked By | Deliverable | Evidence Required |
| --- | --- | --- | --- | --- | --- |
| WS-02-T01 | Create quarantine register | DONE | WS-01-T06 | Quarantine register file | File path + initial entries |
| WS-02-T02 | Create seam packet registry | DONE | WS-02-T01 | Registry file | File path + packet coverage summary |
| WS-02-T03 | Identify one repeated gate family to parametrize | DONE | none | Selected family declaration | Before-count snapshot |
| WS-02-T04 | Extract shared helpers | DONE | WS-02-T03 | Shared helper module(s) | Diff + call sites updated |
| WS-02-T05 | Replace one cloned family with parametrized tests | DONE | WS-02-T04 | Consolidated test family | Before and after duplication count |
| WS-02-T06 | Define future filename shortening convention | DONE | WS-02-T05 | Naming convention section | Convention text committed |

## Evidence Log
- 2026-03-17 WS-02-T01: `formal/docs/release/QUARANTINE_REGISTER_v0.md` exists with active rows `QR-0001` and `QR-0002`.
- 2026-03-17 WS-02-T02: `formal/docs/paper/QFT_GR_SEAM_PACKET_REGISTRY_v0.json` exists with scope `PACKET42_TO_PACKET54`.
- 2026-03-17 WS-02-T03: repeated family selected as `formal/python/tests/test_toe_qft_gr_seam_packet(4[2-9]|5[0-4]).*_gate.py`; baseline measured at `91` files.
- 2026-03-17 WS-02-T04: `formal/python/tests/qft_gr_seam_registry_helpers.py` confirmed present; representative validation run `c:/Users/psboy/Documents/ToE/.venv/Scripts/python.exe -m pytest -q formal/python/tests/test_toe_qft_gr_seam_packet42_eligibility_review_gate.py` -> `1 passed in 0.71s`.
- 2026-03-17 WS-02-T05: consolidated family artifacts confirmed: `formal/python/tests/qft_gr_seam_packet_eligibility_review_checks.py` and `formal/python/tests/test_toe_qft_gr_seam_packet_eligibility_review_parametrized_gate.py`; validation run over parametrized plus packet42/43/44 wrappers -> `6 passed in 2.70s`.
- 2026-03-17 WS-02-T05 duplication delta snapshot: selected family baseline `91` files; packet42/43/44 wrapper after-state combined line count `21` lines.
- 2026-03-17 WS-02-T06: filename convention documented in section `Filename Convention (WS-02-T06)`.

## Blockers
- none

## Filename Convention (WS-02-T06)
- Apply to new files by default; avoid renaming historical files solely for style alignment.
- Use `pNN` packet tokens in new filenames (for example, `p42`, `p54`) when practical.
- Prefer compact semantic topic tokens (`elig_review`, `hold_fork`, `threshold`, `convergence`, `authz`).
- Gate tests end with `_gate.py`; shared checks modules end with `_checks.py`; helper modules end with `_helpers.py`.
- Target filename length (without extension): 64 characters or fewer.

## Exit Criteria
- Quarantine register exists.
- Seam packet registry exists.
- One repeated family is consolidated with parametrized tests.
- Duplication count is reduced measurably and recorded.
