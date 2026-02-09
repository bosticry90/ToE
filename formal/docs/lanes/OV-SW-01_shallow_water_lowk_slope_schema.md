# Axis C schema: OV-SW-01 — Shallow-water low-k slope (schema-only)

Date: 2026-01-25

Status: schema proposal (no implementation yet)

Purpose

- Define a third, independent lane (Axis C) that is structurally analogous to existing low-k slope / speed observables.
- Provide a governance-safe record shape that can be locked deterministically.
- Make **no physics comparability claims** and introduce **no cross-lane pairing**.

Non-claims

- This record does not assert any physical equivalence to Bragg, sound, or any other lane.
- This record does not assert the correctness of a shallow-water model.
- This record does not imply admissibility gates are enabled or sufficient.

---

## Canonical schema ID

- `OV-SW-01_shallow_water_lowk_slope/v1`

This is a lane-local observable schema. Any cross-lane audit must be a separate observable and must be admissibility-gated.

---

## Record shape (parallel to existing lane observables)

Top-level keys follow the existing pattern seen in e.g. `OV-SND-02_*` and `OV-BR-04A_*` locks:

```json
{
  "schema": "OV-SW-01_shallow_water_lowk_slope/v1",
  "date": "YYYY-MM-DD",
  "observable_id": "OV-SW-01",

  "input_dataset": {
    "csv_relpath": "formal/external_evidence/<TBD>/ovsw01_digitization/omega_over_2pi_vs_k_lowk.csv",
    "csv_sha256": "sha256-hex",
    "row_count": 0,
    "source_digitization_id": "OV-SW-01N",
    "source_observable_id": "OV-SW-01"
  },

  "method": {
    "primary": {
      "name": "ols_through_origin",
      "model": "f_hz = slope_hz_per_m * k_m_inv",
      "rationale": "Pinned conservative estimator; avoids free intercept choice."
    },
    "uncertainty": {
      "type": "slope_standard_error",
      "assumptions": ["homoscedastic_residuals", "independent_points"]
    }
  },

  "results": {
    "primary": {
      "slope_hz_per_m": 0.0,
      "se_hz_per_m": 0.0,

      "c_m_per_s": 0.0,
      "se_m_per_s": 0.0
    }
  },

  "conversion_chain": {
    "rule_id": "OV-SW-01_unit_chain_v1",
    "input_units": {
      "k": "m^-1",
      "f": "s^-1",
      "slope": "(s^-1)/(m^-1)"
    },
    "pinned_identity": "1 (s^-1)/(m^-1) = 1 (m/s)",
    "output_units": {
      "c": "m/s"
    },
    "notes": "Pure unit identity only; no physical equivalence claim."
  },

  "scope_limits": [
    "derived_from_frozen_points_only",
    "pinned_slope_rule",
    "no_cross_lane_claim",
    "non_decisive_by_design"
  ],

  "status": {
    "blocked": false,
    "blockers": []
  },

  "units": {
    "k": "m_inv",
    "f": "s_inv",
    "slope": "hz_per_m",
    "c": "m_per_s"
  },

  "non_claims": {
    "not_asserting_physical_model_validity": true,
    "not_asserting_cross_lane_equivalence": true,
    "not_asserting_pairing_exists": true,
    "not_asserting_gate_sufficiency_or_enablement": true
  },

  "fingerprint": "sha256-hex"
}
```

---

## Pinned units and invariants

Pinned units (canonical for this lane)

- `k`: `m^-1`
- `f = ω/(2π)`: `s^-1` (Hz)
- slope: `(s^-1)/(m^-1)`
- derived `c`: `m/s`

Required invariants

- `results.primary.c_m_per_s == results.primary.slope_hz_per_m` (exact; unit-identity export)
- `results.primary.se_m_per_s == results.primary.se_hz_per_m`
- `conversion_chain.pinned_identity` must match exactly: `1 (s^-1)/(m^-1) = 1 (m/s)`
- All `non_claims.*` flags must be present and `true`.
- `fingerprint` computed from canonical JSON serialization (sorted keys; newline-terminated) consistent with existing lock style.

---

## Notes on data sourcing (deferred)

- This schema does not require external evidence yet; it supports synthetic or digitized inputs.
- If external evidence is later used, it must be pinned via `csv_relpath` + `csv_sha256` under `formal/external_evidence/`.

---

## Next step (not executed here)

- Create an `OV-SW-01N` digitization record (frozen points) and a computed lock generator that emits `OV-SW-01` using this schema.
- Create a cross-lane audit observable (e.g., SW↔SND or SW↔BR) that is admissibility-gated and expected to emit `blocked` with `rows: []` under current gate-disable posture.
