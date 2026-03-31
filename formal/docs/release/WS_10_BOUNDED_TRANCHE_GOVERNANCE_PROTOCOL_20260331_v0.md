# WS-10 Bounded Tranche Governance Protocol (2026-03-31)

## Overview

This document establishes the official bounded tranche execution protocol for all future work in the Theory of Everything project. It consolidates learnings from transcript-drift recovery and operationalizes the checkpoint ladder infrastructure.

## Protocol Status

**EFFECTIVE IMMEDIATELY**: All new work must follow this protocol starting from commit 6aa36f8.

## Mandatory Workflow

Every bounded tranche follows exactly 7 phases in sequence:

### Phase A: Baseline Lock
- Document the current commit hash before any changes
- Verify working tree is clean (`git status --short` shows no output)
- Record baseline in mental checkpoint or notes

### Phase B: Tranche Design
- Define exactly one bounded objective
- List files allowed to change (in-scope boundary)
- List files explicitly excluded (out-of-scope boundary)
- Define success criteria before touching any code

### Phase C: Single-Tranche Implementation
- Apply changes only to files in scope
- Stop immediately if drift appears in out-of-scope files
- Do not pack multiple unrelated changes into one tranche
- Do not do opportunistic refactors outside scope

### Phase D: Mandatory Four-Step Ladder (In Exact Order)

Execute:
```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1
```

This runs:
1. `renderer apply/verify`
2. `test_state_core_generation_integrity_gate.py`
3. `test_state_core_compression_yield_gate.py`
4. `governance_suite.ps1` (full 626+ test suite)

**Critical**: Do not skip steps. Do not reorder steps. All four must pass.

### Phase E: Post-Run Hygiene

After the ladder completes:
1. Check `git status --short` for untracked or modified files
2. If generated outputs changed, the ladder script restores them automatically
3. Verify working tree is clean: `git status --short` should show no output

### Phase F: Failure Handling

If ANY of the four ladder steps fail:
- **DO NOT** continue to the next tranche
- **DO NOT** try to fix in-place
- Revert the bounded tranche changes completely
- Recover to the last known good migration tag
- Re-run the full four-step ladder on the recovered point
- Only resume work when the ladder passes on recovered state

### Phase G: Continuation Gate

Only proceed to the next tranche when ALL conditions hold:
1. All four ladder steps report PASS
2. Working tree is clean (no uncommitted changes)
3. Generated outputs are restored as needed
4. Current commit represents completed, tested work

## Enforcement

- **Mandatory tool**: Use `checkpoint_ladder.ps1` (do not manually run the four steps)
- **No exceptions**: All work must follow phases A-G in order
- **No chaining**: Do not commit multiple tranches without running the ladder between them
- **No continuations**: If any step fails, stop and recover before resuming

## Tool Documentation

- Tool script: [`checkpoint_ladder.ps1`](../../checkpoint_ladder.ps1)
- Tool behavior: Executes four-step ladder in order, restores generated outputs, reports final status
- Example usage: `pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1`

## Control References

- Transcript drift rejection: [`WS_10_TRANSCRIPT_DRIFT_REJECTION_BASELINE_CLOSEOUT_20260331_v0.md`](WS_10_TRANSCRIPT_DRIFT_REJECTION_BASELINE_CLOSEOUT_20260331_v0.md)
- Closeout note update: [`WS_10_TRANSCRIPT_DRIFT_REJECTION_BASELINE_CLOSEOUT_20260331_v0.md`](WS_10_TRANSCRIPT_DRIFT_REJECTION_BASELINE_CLOSEOUT_20260331_v0.md)
- Checkpoint ladder adoption: [`WS_10_CHECKPOINT_LADDER_STANDARD_ADOPTION_20260331_v0.md`](WS_10_CHECKPOINT_LADDER_STANDARD_ADOPTION_20260331_v0.md)

## Effective Date

**2026-03-31**

## Status

Adopted and in effect. All future work begins from commit 6aa36f8 using this protocol.

---

**Protocol Owner**: ToE Governance  
**Review Cycle**: Every 5 tranches or 2 weeks, whichever comes first  
**Escalation**: If ladder fails, contact governance authority before recovery
