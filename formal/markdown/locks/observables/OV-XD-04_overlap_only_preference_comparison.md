# OV-XD-04 — Overlap-only preferred-fit-family comparison (OV-04x vs OV-03x)

Scope / limits
- Overlap-only bookkeeping record
- No continuity claim
- No averaging across regimes
- β not inferred / β-null posture

Record (computed)

```json
{
  "agreement": false,
  "decisiveness": "one-decisive",
  "high_observable_id": "OV-03x",
  "high_preference": {
    "adequacy_policy": "DQ-01_v1",
    "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
    "lock_payload_fingerprint": "78f15afb7ee964f0efb8e43b5525fa3dea2fa8fa10f5c9a6b65f46a7e8cf7c7b",
    "observable_id": "OV-03x",
    "prefer_curved": false,
    "report_fingerprint": "78f15afb7ee964f0efb8e43b5525fa3dea2fa8fa10f5c9a6b65f46a7e8cf7c7b",
    "robustness_failed": true
  },
  "high_preferred_family": "undecided",
  "low_observable_id": "OV-04x",
  "low_preference": {
    "adequacy_policy": "DQ-01_v1",
    "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
    "lock_payload_fingerprint": "f562944bc70ff2f892d571cb70627aa2e749dc6ef18dd031358eb17e54930915",
    "observable_id": "OV-04x",
    "prefer_curved": true,
    "report_fingerprint": "f562944bc70ff2f892d571cb70627aa2e749dc6ef18dd031358eb17e54930915",
    "robustness_failed": false
  },
  "low_preferred_family": "curved",
  "notes": "Overlap-only bookkeeping record: compares robustness-only preferred-fit-family outcomes only within the OV-XD-03 overlap band; no continuity claim; no averaging across regimes; \u03b2 not inferred / \u03b2-null posture.",
  "overlap_band": [
    3.33842,
    4.45157988663
  ],
  "provenance": {
    "overlap_band": {
      "ovxd03_fingerprint": "e50a44d369d0ff9c4f56fc6756456df5ceaf9818a2632a6da56167ac551c674d",
      "ovxd03_schema": "OV-XD-03/v2",
      "source": "OV-XD-03"
    },
    "policy": {
      "curved_fit_adequacy_policy": "DQ-01_v1",
      "q_threshold": 0.9
    },
    "preferences": {
      "high": {
        "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
        "observable_id": "OV-03x",
        "source": "lock"
      },
      "low": {
        "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
        "observable_id": "OV-04x",
        "source": "lock"
      }
    }
  },
  "schema": "OV-XD-04/v1"
}
```

Record fingerprint: `bc57a4634d303f601ce705a0f47b8db3c039499c1d7e5d19e914859c4930e77d`
