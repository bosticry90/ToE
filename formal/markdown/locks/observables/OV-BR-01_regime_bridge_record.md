# OV-BR-01 — Regime bridge record (computed)

This record does not assert continuity; it records regime-separated results and their k-band overlap/gap only. No averaging.

Scope / limits
- split into sub-bands
- evaluated separately
- no averaging across regimes
- no continuity claim
- β not inferred / β-null posture

Record (computed)

```json
{
  "comparability_statement": "Overlap exists; comparison is meaningful only within the overlap band. This record does not assert continuity; it records regime-separated results and band geometry only. No averaging across regimes.",
  "gap": null,
  "gap_width": null,
  "high_band": [
    3.33842,
    8.28312
  ],
  "high_preference": {
    "adequacy_policy": "DQ-01_v1",
    "lock_payload_fingerprint": "78f15afb7ee964f0efb8e43b5525fa3dea2fa8fa10f5c9a6b65f46a7e8cf7c7b",
    "observable_id": "OV-03x",
    "prefer_curved": false,
    "report_fingerprint": "78f15afb7ee964f0efb8e43b5525fa3dea2fa8fa10f5c9a6b65f46a7e8cf7c7b",
    "robustness_failed": true
  },
  "low_band": [
    0.41847843636,
    14.589675116826
  ],
  "low_preference": {
    "adequacy_policy": "DQ-01_v1",
    "observable_id": "OV-01g",
    "prefer_curved": true,
    "report_fingerprint": "e623da03ade00b2be16c6fe3a6ef04a6d7743969ddda7e080b65be7c7459c011",
    "robustness_failed": false
  },
  "notes": "Bookkeeping only; split into sub-bands; evaluated separately; no averaging across regimes; no continuity claim; \u03b2 not inferred / \u03b2-null posture.",
  "overlap": [
    3.33842,
    8.28312
  ],
  "provenance": {
    "bands": {
      "ovxd03_fingerprint": "e50a44d369d0ff9c4f56fc6756456df5ceaf9818a2632a6da56167ac551c674d",
      "ovxd03_provenance": {
        "OV-01g": {
          "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv",
          "csv_sha256": "a31e3440c1847c590eeeb72e32dbc28b912463622d1edba7e708e239919f0fcf"
        },
        "OV-02x": {
          "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv",
          "csv_sha256": "a31e3440c1847c590eeeb72e32dbc28b912463622d1edba7e708e239919f0fcf"
        },
        "OV-03x": {
          "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv",
          "csv_sha256": "088acb258716352bb141eae080fdc22fc5e4ab52f10ee2ebf2c94ba14538f216"
        },
        "OV-04x": {
          "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv",
          "csv_sha256": "f6d620fb7da9ec199953bed628dc72a98c74d0baa5bb52e78744ea398a2b8b9b"
        }
      },
      "ovxd03_schema": "OV-XD-03/v2",
      "source": "OV-XD-03"
    },
    "preferences": {
      "high": {
        "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
        "note": "Evaluated separately (no averaging across regimes); \u03b2 not inferred / \u03b2-null posture.",
        "source": "lock"
      },
      "low": {
        "module": "formal/python/toe/observables/ov01_fit_family_robustness.py",
        "note": "Evaluated separately (no averaging across regimes); \u03b2 not inferred / \u03b2-null posture.",
        "source": "computed"
      }
    }
  },
  "schema": "OV-BR-01/v1"
}
```

Record fingerprint: `400ad6423125d8cf9892fb04cbc4e6c6c419ac1f805bb00ba4a827ef198c39ad`
