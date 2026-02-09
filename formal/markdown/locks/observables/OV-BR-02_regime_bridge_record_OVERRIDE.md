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
    "adequacy_policy": "DQ-01_v1",
    "curved_adequacy_passes": true,
    "failure_reasons": [
      "q_ratio_above_threshold"
    ],
    "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
    "lock_payload_fingerprint": "78f15afb7ee964f0efb8e43b5525fa3dea2fa8fa10f5c9a6b65f46a7e8cf7c7b",
    "observable_id": "OV-03x",
    "prefer_curved": false,
    "q_ratio": 1.0241440175459013,
    "q_threshold": 0.9,
    "report_fingerprint": "78f15afb7ee964f0efb8e43b5525fa3dea2fa8fa10f5c9a6b65f46a7e8cf7c7b",
    "robustness_failed": true
  },
  "low_band": [
    0.006351039261,
    4.45157988663
  ],
  "low_preference": {
    "adequacy_policy": "DQ-01_v1",
    "curved_adequacy_passes": true,
    "failure_reasons": [],
    "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
    "lock_payload_fingerprint": "f562944bc70ff2f892d571cb70627aa2e749dc6ef18dd031358eb17e54930915",
    "observable_id": "OV-04x",
    "prefer_curved": true,
    "q_ratio": 0.8060220497327952,
    "q_threshold": 0.9,
    "report_fingerprint": "f562944bc70ff2f892d571cb70627aa2e749dc6ef18dd031358eb17e54930915",
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
      "curved_fit_adequacy_policy": "DQ-01_v1",
      "q_threshold": 0.9
    },
    "preferences": {
      "high": {
        "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
        "source": "lock"
      },
      "low": {
        "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
        "source": "lock"
      }
    }
  },
  "schema": "OV-BR-02/v1"
}
```

Record fingerprint: `3bb051329ae22c1f9649cca702f26c4cbe4adf8adcbc84cf0d9e79f880e5e8ac`
