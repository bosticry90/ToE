# WS-10 Checkpoint Ladder Standard Adoption (2026-03-31)

## Decision

The `checkpoint_ladder.ps1` automation tool is now the **mandatory standard** for all post-tranche verification in the ToE project.

## Rationale

* Codifies the exact four-step verification sequence established in the transcript-drift rejection closeout
* Reduces operator variance in gate execution
* Automatically preserves generated-output hygiene
* Enables consistent, repeatable verification across all bounded tranches

## Mandatory Usage

After any bounded tranche completes, execute:

```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1
```

Do not proceed to the next tranche unless all four steps report PASS.

## Verification Steps (In Order)

1. Renderer apply/verify
2. State-core integrity gate
3. Compression/yield gate
4. Full governance suite (626+ tests)

## Tool Location

* [`checkpoint_ladder.ps1`](../../checkpoint_ladder.ps1)

## Documentation

Refer to [`README.md`](../../README.md) for usage details and example invocations.

---

**Effective Date:** 2026-03-31  
**Status:** Adopted and operational  
**Referenced Control:** WS_10_TRANSCRIPT_DRIFT_REJECTION_BASELINE_CLOSEOUT_20260331_v0.md
