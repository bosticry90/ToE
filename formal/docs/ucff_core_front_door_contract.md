# UCFF Core Front Door — Surface Contract (bounded)

Last updated: 2026-02-01

## Purpose

Define a tiny, stable **surface contract** for the UCFF core front door: typed inputs, deterministic report schema, and the bounded invariants currently in-scope.

This is a governance/scaffolding contract. It does **not** promote any physical truth claim.

## Canonical surface

- Implementation: `formal/python/toe/ucff/core_front_door.py`

## Input contract

### `UcffCoreInput`

- `k: List[float]`
  - Interpreted as a 1D sample grid for $k$.
  - Ordering is preserved into the report.
- `params: UcffCoreParams`
  - `rho0: float`
  - `g: float`
  - `lam: float`
  - `beta: float`
- `config_tag: str`
  - Defaults to `UCFF/core_front_door_report/v1`.
  - Treated as metadata only.

## Report contract

### `UcffCoreReport`

- `schema: "UCFF/core_front_door_report/v1"`
- `config_tag: str`
- `params: Dict[str, float]` (keys: `rho0`, `g`, `lam`, `beta`)
- `k: List[float]`
- `omega2: List[float]`
- `fingerprint: str`
  - Deterministic SHA-256 of the JSON payload (sorted keys, stable separators).

## Determinism / non-I/O policy

- No implicit file I/O.
- For identical inputs, the report is byte-stable under `dumps_ucff_core_report()`.

## In-scope invariants (bounded; test-backed)

The following invariants are considered **in-scope** for this surface. They are bounded checks against the report-only API.

- JSON roundtrip determinism (schema + fingerprint stability)
  - Evidence: `formal/python/tests/test_ucff_core_front_door_roundtrip.py`
- Semantic recomputation: `omega2` equals a recomputation from `(k, params)`
  - Evidence: `formal/python/tests/test_ucff_core_front_door_roundtrip.py`
- Coefficient recovery from bounded samples (symbolic, report-only)
  - Evidence: `formal/python/tests/test_ucff_core_front_door_symbolic_invariant_01.py`
- Monotonicity check on a deterministic grid (symbolic, report-only)
  - Evidence: `formal/python/tests/test_ucff_core_front_door_symbolic_invariant_02.py`

## Out-of-scope (explicit)

- Any claim of empirical fit or external truth.
- Any implicit coupling to archived code or archived artifacts.
- Any non-deterministic sampling or runtime discovery.
