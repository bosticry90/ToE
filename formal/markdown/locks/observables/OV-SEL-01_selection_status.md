# OV-SEL-01 — Selection status narrative (active DQ-01 policy; computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- No continuity claim; no averaging across regimes
- β not inferred / β-null posture
- Computed from locks; does not change policy thresholds

Narrative (operational)

Selection status under active DQ-01 policy=DQ-01_v2 (robustness-only; no physics claim):
- Baseline policy remains pinned: DQ-01_v1 (q_threshold=0.9).
- OV-04x (DS-02 low-k): selection_status=decisive_curved (prefer_curved=True, robustness_failed=False, q_ratio=0.806022 <= q_threshold=1.05).
- OV-03x (B1): selection_status=decisive_curved (curved_adequacy_passes=True, q_ratio=1.02414 > q_threshold=1.05; failure_reasons=[]).
- Overlap band (OV-XD-03): non_empty=True, k=[3.33842, 4.45158].
- Overlap-only comparison (OV-XD-04): decisiveness=both-decisive, agreement=True.
No continuity claim; no averaging across regimes; β not inferred / β-null posture.

Record (computed)

```json
{
  "fingerprint": "14c4c9d4c49bf9f89c2f9f5e3418439d129b98e70f1d0b4d6006e5ed4f2cd5ed",
  "narrative": "Selection status under active DQ-01 policy=DQ-01_v2 (robustness-only; no physics claim):\n- Baseline policy remains pinned: DQ-01_v1 (q_threshold=0.9).\n- OV-04x (DS-02 low-k): selection_status=decisive_curved (prefer_curved=True, robustness_failed=False, q_ratio=0.806022 <= q_threshold=1.05).\n- OV-03x (B1): selection_status=decisive_curved (curved_adequacy_passes=True, q_ratio=1.02414 > q_threshold=1.05; failure_reasons=[]).\n- Overlap band (OV-XD-03): non_empty=True, k=[3.33842, 4.45158].\n- Overlap-only comparison (OV-XD-04): decisiveness=both-decisive, agreement=True.\nNo continuity claim; no averaging across regimes; \u03b2 not inferred / \u03b2-null posture.",
  "ov03x": {
    "adequacy_policy": "DQ-01_v2",
    "curved_adequacy_passes": true,
    "failure_reasons": [],
    "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset_DQ-01_v2.md",
    "lock_payload_fingerprint": "f91cdb2b743de43903a1e28b0503d7ac4da8eea713e56682b79db54a2b4ce0bb",
    "observable_id": "OV-03x",
    "prefer_curved": true,
    "q_ratio": 1.0241440175459013,
    "q_threshold": 1.05,
    "r_max_curved": 0.6107718647646012,
    "r_max_linear": 0.596373024009025,
    "report_fingerprint": "f91cdb2b743de43903a1e28b0503d7ac4da8eea713e56682b79db54a2b4ce0bb",
    "robustness_failed": false,
    "selection_status": "decisive_curved"
  },
  "ov04x": {
    "adequacy_policy": "DQ-01_v2",
    "curved_adequacy_passes": true,
    "failure_reasons": [],
    "lock_path": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk_DQ-01_v2.md",
    "lock_payload_fingerprint": "14a9a4a87fa9291cc716756eac28cc0794ad2940dd5215c5c4ebd450af4769e8",
    "observable_id": "OV-04x",
    "prefer_curved": true,
    "q_ratio": 0.8060220497327952,
    "q_threshold": 1.05,
    "r_max_curved": 0.7172088910074628,
    "r_max_linear": 0.8898129911523203,
    "report_fingerprint": "14a9a4a87fa9291cc716756eac28cc0794ad2940dd5215c5c4ebd450af4769e8",
    "robustness_failed": false,
    "selection_status": "decisive_curved"
  },
  "ovxd03_overlap_band": {
    "lock_path": "formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
    "overlap": {
      "k_max": 4.45157988663,
      "k_min": 3.33842,
      "non_empty": true
    },
    "record_fingerprint": "e50a44d369d0ff9c4f56fc6756456df5ceaf9818a2632a6da56167ac551c674d",
    "schema": "OV-XD-03/v2"
  },
  "ovxd04_overlap_only_comparison": {
    "agreement": true,
    "decisiveness": "both-decisive",
    "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
    "overlap_band": [
      3.33842,
      4.45157988663
    ],
    "record_fingerprint": "a3e8603c2dcffa9d904c799a7349d328089ffc1bccf39a3e2a074bc83e92bf31",
    "schema": "OV-XD-04/v1"
  },
  "schema": "OV-SEL-01_selection_status/v1",
  "status_date": "2026-01-23"
}
```

Record fingerprint: `14c4c9d4c49bf9f89c2f9f5e3418439d129b98e70f1d0b4d6006e5ed4f2cd5ed`
