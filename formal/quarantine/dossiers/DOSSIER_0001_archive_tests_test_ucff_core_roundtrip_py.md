# DOSSIER 0001: archive/tests/test_ucff_core_roundtrip.py

## Source

- Path: archive/tests/test_ucff_core_roundtrip.py
- SHA256: c1d1fcc3d35cde24f8b75acaebc19c32c27eb744f9e667a73bda15b81f846659
- Bytes: 5025
- Kind: python

## Why It Scored High

- Total: 148
- Breakdown: base=50 tests=50 keywords=20 equations=8 refs=20 family=0 feasibility=0 penalty=0
- Keyword hits: dispersion, equation, sympy, ucff
- Reference hits: ov-
- Equation signals: 2
- Doc family key: archive/tests/test_ucff_core_roundtrip.py

## Candidate Classification

- Classification: diagnostic_candidate

## Proposed Reintegration Target

- Existing canonical surface (if any): None identified (no non-archive `equations.ucff_core` or equivalent UCFF core front door).
- Dependency observed (legacy): imports `equations.ucff_core` and asserts EOM↔dispersion consistency in a restricted baseline regime.
- Prerequisite (if reintegrating): intentionally introduce a non-archive UCFF symbolic/core front door (clean-room) and then restate this invariant against that surface.

## Validation Plan

- Symbolic: Treat the legacy test as a *spec for invariants*; port the plane-wave substitution residual check once a canonical UCFF EOM/dispersion surface exists.
- Numeric: Not required for the legacy invariant itself (purely symbolic); numeric verification belongs in OV-UCFF audit lanes.
- Locks/tests: When a UCFF core front door exists, re-home a rewritten version under `formal/python/tests/` targeting only non-archive modules.

## Exit Condition

- Accepted / Rejected / Reference-only: Resolved (bounded evidence only; does not upgrade physical truth claims).

Resolved when (explicit rule):

1. A non-archive canonical UCFF front door exists and is referenced as the target surface.
2. At least 2 non-overlapping bounded invariants, rewritten clean-room, are passing against the front door.
3. Each invariant has a pytest evidence pointer recorded in this dossier (node id + file).
4. The tests are deterministic (no randomness, no time integration drift, no hidden I/O) and remain quarantine-compliant (no archive imports; no archive path reliance at runtime).

Update (2026-02-01): A non-archive UCFF core/front-door exists at formal/python/toe/ucff/core_front_door.py (typed inputs + deterministic JSON report; no archive imports).

Progress (2026-02-01): Two bounded roundtrip-family invariants are now ported clean-room against the front door and are passing:
- formal/python/tests/test_ucff_core_front_door_roundtrip.py::test_ucff_core_front_door_report_json_roundtrip_is_deterministic
- formal/python/tests/test_ucff_core_front_door_roundtrip.py::test_ucff_core_front_door_json_payload_roundtrip_recomputes_omega2

Closure criteria met (2026-02-01): A non-archive UCFF core/front-door exists and multiple deterministic roundtrip-family invariants are now locked against it.
