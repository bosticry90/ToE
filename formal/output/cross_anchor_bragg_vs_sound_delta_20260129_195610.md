# Cross-anchor Bragg↔Sound report delta (numeric_only vs justified_only)

Date: 2026-01-29

Inputs
- numeric_only report: `formal/output/cross_anchor_bragg_vs_sound_20260129_195622_413176.md`
- justified_only report (with suppressed shown): `formal/output/cross_anchor_bragg_vs_sound_20260129_195622_645030.md`

Summary
- numeric_only:
  - comparisons evaluated: 4
  - tol check distribution (tolerance=0.15 rel_err): PASS=2, FAIL=2
- justified_only:
  - JUSTIFIED=0, SUPPRESSED=4, TOTAL=4

Suppression reasons histogram (justified_only)
- AUDIT_COMPARABILITY_NOT_PRESENT: 4
- OVBR_SND01_BLOCKED: 4
- NO_BRAGG_SOUND_MAPPING_TUPLE: 4

Interpretation
- The numeric signal exists (2 PASS / 2 FAIL under the pinned tolerance), but the justified pipeline correctly refuses to treat any of it as a valid cross-anchor comparison given the current evidentiary gate state.
