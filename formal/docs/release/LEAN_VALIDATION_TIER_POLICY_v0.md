# Lean Validation Tier Policy v0

This policy governs routine packet validation after the QFT-GR provisional
scalar source-admissibility review.

## Tiers

1. Tier 1: touched Lean marker or module.
   Example: `formal/toe_formal/lake.ps1 env lean ToeFormal/Derivation/<Module>.lean`

2. Tier 2: smallest affected Lake target.
   Example: `./run_lean.ps1 -Target ToeFormal.Derivation.<Module> -TimeoutSeconds 300`

3. Tier 3: lane-level aggregate when available.
   Examples:
   - `./run_lean.ps1 -Target ToeFormal.Derivation.QFTGRScalarSandbox -TimeoutSeconds 600`
   - `./run_lean.ps1 -Target ToeFormal.Derivation.CurrentTarget -TimeoutSeconds 600`
   - `./run_lean.ps1 -Target ToeFormal.Release.CurrentAuthority -TimeoutSeconds 600`

4. Tier 4: full `ToeFormal` aggregate.
   Example: `./run_lean.ps1 -Target ToeFormal -TimeoutSeconds 1800`

## Interpretation

A full aggregate timeout with steady build progress is incomplete validation,
not mathematical failure.

If a packet updates `ToeFormal.lean`, the preservation record must state whether
full aggregate validation was completed, incomplete due to timeout, or deferred.

Routine packets should use the smallest relevant tier. Full aggregate validation
is reserved for release, preservation, or authority-surface synchronization.
