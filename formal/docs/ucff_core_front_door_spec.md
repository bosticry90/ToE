# UCFF Core Front Door (Spec)

Status: Draft, bounded.

## Scope (bounded)

This spec defines a minimal non-archive UCFF "core/front-door" surface for deterministic bookkeeping of a UCFF-like dispersion polynomial.

- No implicit file I/O.
- Typed inputs.
- Deterministic outputs (stable JSON with a fingerprint).
- No imports from `archive/`.

## Inputs

- `UcffCoreInput`
  - `k`: explicit k-grid (list of floats)
  - `params`: `UcffCoreParams` carrying `rho0`, `g`, `lam`, `beta`
  - `config_tag`: free string label

## Outputs

- `UcffCoreReport` JSON (`UCFF/core_front_door_report/v1`) containing:
  - parameters (echoed)
  - k-grid (echoed)
  - `omega2` values computed deterministically by:

$$
\omega^2(k) = (k^2/2)^2 + (g\,\rho_0)k^2 + \lambda\,k^4 + \beta\,k^6.
$$

## Notes / limits

This front door is a software governance primitive only. It does not assert UCFF physical correctness.
