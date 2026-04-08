# Gate Quality Tier Schema v0

Schema ID:
- `GATE_QUALITY_TIER_SCHEMA_v0`

Purpose:
- classify governance tests by operational criticality.
- support tier-aware manifest selection without changing release-gate truth.

Tier definitions:
1. `TIER_CRITICAL`
- failures block execution immediately.
- examples: state integrity, architecture parity, release-lane contract invariants.

2. `TIER_INTEGRITY`
- failures block governance acceptance.
- examples: authority mirrors, lock contracts, cross-surface parity checks.

3. `TIER_OPERATIONAL`
- failures indicate degraded lane health; treated as blocking in canonical governance suite.
- examples: bounded lane execution and synthesis checkpoint gates.

4. `TIER_MONITORING`
- advisory confidence signals; may be included in CI smoke lanes.
- examples: orchestration/reporting observations that do not redefine release truth.

Manifest integration guidance:
- continue using `groups.governance_pytests.tests` as canonical execution set.
- optional `test_tiers` map in manifest can annotate each test path with a tier token.
- tier-aware tooling should default unannotated tests to `UNSPECIFIED` and remain backward-compatible.

Non-claim boundary:
- tier labels classify process criticality only.
- tier labels do not promote scientific or theorem claim status.