# GR01 Pillar Package v0

Package ID:
- `GR01_PILLAR_PACKAGE_v0`

Classification:
- `P-POLICY`

Package freeze token:
- `GR01_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED`

Reopen policy token:
- `GR01_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION`

Reopen triggers (any trigger reopens hardening adjudication review):
- `REOPEN_TRIGGER_CANONICAL_TOKEN_DRIFT_v0`
- `REOPEN_TRIGGER_ROBUSTNESS_NEGCTRL_REGRESSION_v0`
- `REOPEN_TRIGGER_RESOLUTION_TREND_BREAK_v0`

Required package contents:
- one-page summary:
  - `formal/docs/paper/TOE_GR01_PILLAR_SUMMARY_v0.md`
- assumption ledger:
  - `formal/markdown/locks/policy/GR01_ASSUMPTION_LEDGER_v0.md`
- canonical theorem chain map:
  - `formal/docs/paper/TOE_GR01_CANONICAL_CHAIN_MAP_v0.md`
- robustness record:
  - `formal/markdown/locks/policy/GR01_ROBUSTNESS_RECORD_v0.md`
- negative-control record:
  - `formal/markdown/locks/policy/GR01_NEGATIVE_CONTROL_RECORD_v0.md`
- resolution trend record:
  - `formal/markdown/locks/policy/GR01_RESOLUTION_TREND_RECORD_v0.md`

Known limitations token block:
- `LIMIT_NO_CONTINUUM_GR_CLAIM_v0`
- `LIMIT_NO_BLACK_HOLE_CLAIM_v0`
- `LIMIT_NO_UNIQUENESS_INFINITE_DOMAIN_CLAIM_v0`

Synchronization pointers:
- Hardening target: `formal/docs/paper/DERIVATION_TARGET_GR01_HARDENING_v0.md`
- State checkpoint: `State_of_the_Theory.md`
