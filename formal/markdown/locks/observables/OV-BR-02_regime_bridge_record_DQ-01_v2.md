# OV-BR-02 — Regime bridge record (OV-04x ↔ OV-03x) (computed)

This record does not assert continuity; it records regime-separated results and their k-band overlap/gap only. No averaging.

Scope / limits
- split into sub-bands
- evaluated separately
- overlap-only comparability
- no averaging across regimes
- no continuity claim
- β not inferred / β-null posture

Record (computed)

```json
{
  "comparability_statement": "Overlap exists; comparison is meaningful only within the OV-XD-03 overlap band. This record does not assert continuity; it records regime-separated results and band geometry only. No averaging across regimes.",
  "gap": null,
  "gap_width": null,
  "high_band": [
    3.33842,
    8.28312
  ],
  "high_preference": {
    "adequacy_policy": "DQ-01_v2",
    "curved_adequacy_passes": true,
    "failure_reasons": [],
    "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset_DQ-01_v2.md",
    "lock_payload_fingerprint": "f91cdb2b743de43903a1e28b0503d7ac4da8eea713e56682b79db54a2b4ce0bb",
    "observable_id": "OV-03x",
    "prefer_curved": true,
    "q_ratio": 1.0241440175459013,
    "q_threshold": 1.05,
    "report_fingerprint": "f91cdb2b743de43903a1e28b0503d7ac4da8eea713e56682b79db54a2b4ce0bb",
    "robustness_failed": false
  },
  "low_band": [
    0.006351039261,
    4.45157988663
  ],
  "low_preference": {
    "adequacy_policy": "DQ-01_v2",
    "curved_adequacy_passes": true,
    "failure_reasons": [],
    "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk_DQ-01_v2.md",
    "lock_payload_fingerprint": "14a9a4a87fa9291cc716756eac28cc0794ad2940dd5215c5c4ebd450af4769e8",
    "observable_id": "OV-04x",
    "prefer_curved": true,
    "q_ratio": 0.8060220497327952,
    "q_threshold": 1.05,
    "report_fingerprint": "14a9a4a87fa9291cc716756eac28cc0794ad2940dd5215c5c4ebd450af4769e8",
    "robustness_failed": false
  },
  "notes": "Bookkeeping only; split into sub-bands; evaluated separately; overlap-only comparability; no averaging across regimes; no continuity claim; \u03b2 not inferred / \u03b2-null posture.",
  "overlap": [
    3.33842,
    4.45157988663
  ],
  "provenance": {
    "bands": {
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
        "source": "lock"
      },
      "low": {
        "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk_DQ-01_v2.md",
        "source": "lock"
      }
    }
  },
  "schema": "OV-BR-02/v1"
}
```

Record fingerprint: `f2acf9f426e580dcf9265b238b5d611344baed22c4061e8c5701a11dcfb54d32`
