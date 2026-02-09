# OV-BR-05 — Bragg low-k slope summary (computed)

Scope / limits
- Summary-only table derived from locked OV-BR-04A/04B
- Bookkeeping only; no physics claim
- No refitting performed

Record (computed)

```json
{
  "date": "2026-01-25",
  "fingerprint": "093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1",
  "inputs": {
    "condition_A": {
      "diagnostic": {
        "a_kHz": 0.5002998447566884,
        "dof": 3,
        "n": 5,
        "r2": 0.3468337663215413,
        "residual_rms_kHz": 0.27926004059505455,
        "s_kHz_per_um_inv": 0.6498074713077385,
        "se_a_kHz": 0.29688715512047714,
        "se_kHz_per_um_inv": 0.5148435185105142
      },
      "primary": {
        "c_mm_per_s": 1.3783106701297123,
        "dof": 4,
        "n": 5,
        "residual_rms_kHz": 0.3896231606578541,
        "s_kHz_per_um_inv": 1.3783106701297123,
        "se_kHz_per_um_inv": 0.3378303093727233,
        "se_mm_per_s": 0.3378303093727233
      }
    },
    "condition_B": {
      "diagnostic": {
        "a_kHz": 0.028116128062588515,
        "dof": 4,
        "n": 6,
        "r2": 0.5962500724155817,
        "residual_rms_kHz": 0.19948705048925205,
        "s_kHz_per_um_inv": 0.9284219111168761,
        "se_a_kHz": 0.21329149953704213,
        "se_kHz_per_um_inv": 0.38199474817111057
      },
      "primary": {
        "c_mm_per_s": 0.9729313348425234,
        "dof": 5,
        "n": 6,
        "residual_rms_kHz": 0.19991988089318824,
        "s_kHz_per_um_inv": 0.9729313348425234,
        "se_kHz_per_um_inv": 0.16012340869413266,
        "se_mm_per_s": 0.16012340869413266
      }
    }
  },
  "observable_id": "OV-BR-05",
  "rows": [
    {
      "c_mm_per_s": 1.3783106701297123,
      "condition_key": "condition_A",
      "condition_semantic": "filled circles",
      "dof": 4,
      "n": 5,
      "residual_rms_kHz": 0.3896231606578541,
      "s_kHz_per_um_inv": 1.3783106701297123,
      "se_kHz_per_um_inv": 0.3378303093727233,
      "se_mm_per_s": 0.3378303093727233
    },
    {
      "c_mm_per_s": 0.9729313348425234,
      "condition_key": "condition_B",
      "condition_semantic": "open circles",
      "dof": 5,
      "n": 6,
      "residual_rms_kHz": 0.19991988089318824,
      "s_kHz_per_um_inv": 0.9729313348425234,
      "se_kHz_per_um_inv": 0.16012340869413266,
      "se_mm_per_s": 0.16012340869413266
    }
  ],
  "schema": "OV-BR-05_bragg_lowk_slope_summary/v1",
  "scope_limits": [
    "summary_only",
    "derived_from_locked_records_only",
    "no_refitting",
    "bookkeeping_only_no_physics_claim"
  ],
  "selection": {},
  "status": {
    "admissibility_manifest": {
      "path": "formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json",
      "version": 5
    },
    "blocked": false,
    "debug": {
      "manifest_input_path": "C:\\Users\\psboy\\Documents\\ToE\\formal\\markdown locks\\gates\\admissibility_manifest_ENABLED_OVERRIDE.json",
      "manifest_resolved_path": "formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json",
      "manifest_sha256": "2f9c1aa1dbcc30451ac0740cb09d85c1d12b6490efb02d449e453cc0de94c13f",
      "manifest_version": 5
    },
    "reasons": [],
    "required_gates": [
      "CT01",
      "SYM01",
      "CAUS01"
    ]
  }
}
```

Record fingerprint: `093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1`
