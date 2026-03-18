# WS_08_GOVERNANCE_SUITE_SIMPLIFICATION_CANDIDATES_v0

## Purpose
Record bounded governance-suite simplification candidates that reduce maintenance overhead without weakening rigor controls.

## Baseline Evidence Snapshot
- `governance_suite.ps1` currently carries a large inline pytest tranche argument list (`governance_suite_test_args_count=245`).
- `tooling_smoke.ps1` is a thin wrapper around `tooling_validate.ps1`.
- `governance_suite.ps1` already composes preflight + tooling validation + pytest tranche, indicating command-shape duplication can be reduced by extraction rather than behavior change.

## Candidate Matrix
| Candidate ID | Surface | Current Friction | Proposed Simplification | Bounded Adoption Criteria | Risk Control |
| --- | --- | --- | --- | --- | --- |
| GSC-01 | `governance_suite.ps1` pytest tranche list | Very long inline test argument block is hard to review and maintain. | Move governance pytest targets into a manifest file consumed by the script (read-only selection list). | Script executes same ordered target set from manifest and yields equivalent pass/fail behavior on a bounded sample run. | Keep default manifest frozen in repo; require explicit PR diff for target changes. |
| GSC-02 | `tooling_smoke.ps1` and `tooling_validate.ps1` relationship | Two entry points effectively execute the same validation lane. | Keep one canonical implementation and make the other an explicit alias with documented contract. | Alias entry point produces identical exit code and terminal contract for success/failure paths. | Preserve both command names during transition; no caller breakage. |
| GSC-03 | `governance_suite.ps1` execution modes | Single full path forces heavy run even for quick pre-commit hygiene checks. | Add explicit mode switch (`smoke` vs `full`) with `full` as default. | `full` mode remains behavior-identical; `smoke` mode runs preflight + tooling validate only with clear labeling. | Default remains full to avoid silent rigor reduction. |
| GSC-04 | Script-level policy coupling visibility | Policy and script behavior links are implicit, increasing review overhead. | Add policy-pointer header block in governance scripts referencing WS-08 policy artifacts. | Each script includes current policy pointer lines with no runtime behavior changes. | Comments-only change; no command-path mutation. |

## Adoption Guardrails
1. No candidate may remove any existing gate without explicit retirement evidence in `DEPRECATED_GATE_RETIREMENT_POLICY_v0.md`.
2. Candidate rollout must be one bounded slice per commit with pre/post command-shape verification.
3. Any simplification that changes execution defaults must include an explicit rollback path.

## Notes
- This candidate matrix is a planning/control artifact and does not itself change runtime governance behavior.
