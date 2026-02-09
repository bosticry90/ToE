# OV-XD-04 — Overlap-only preferred-fit-family comparison (OV-04x vs OV-03x)

Scope / limits
- Overlap-only bookkeeping record
- No continuity claim
- No averaging across regimes
- β not inferred / β-null posture

Record (computed)

```json
{
  "agreement": true,
  "decisiveness": "both-decisive",
  "high_observable_id": "OV-03x",
  "high_preference": {
    "adequacy_policy": "DQ-01_v2",
    "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset_DQ-01_v2.md",
    "lock_payload_fingerprint": "f91cdb2b743de43903a1e28b0503d7ac4da8eea713e56682b79db54a2b4ce0bb",
    "observable_id": "OV-03x",
    "prefer_curved": true,
    "report_fingerprint": "f91cdb2b743de43903a1e28b0503d7ac4da8eea713e56682b79db54a2b4ce0bb",
    "robustness_failed": false
  },
  "high_preferred_family": "curved",
  "low_observable_id": "OV-04x",
  "low_preference": {
    "adequacy_policy": "DQ-01_v2",
    "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk_DQ-01_v2.md",
    "lock_payload_fingerprint": "14a9a4a87fa9291cc716756eac28cc0794ad2940dd5215c5c4ebd450af4769e8",
    "observable_id": "OV-04x",
    "prefer_curved": true,
    "report_fingerprint": "14a9a4a87fa9291cc716756eac28cc0794ad2940dd5215c5c4ebd450af4769e8",
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
      "curved_fit_adequacy_policy": "DQ-01_v2",
      "q_threshold": 1.05
    },
    "preferences": {
      "high": {
        "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset_DQ-01_v2.md",
        "observable_id": "OV-03x",
        "source": "lock"
      },
      "low": {
        "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk_DQ-01_v2.md",
        "observable_id": "OV-04x",
        "source": "lock"
      }
    }
  },
  "schema": "OV-XD-04/v1"
}
```

Record fingerprint: `a3e8603c2dcffa9d904c799a7349d328089ffc1bccf39a3e2a074bc83e92bf31`
