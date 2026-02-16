# CT-07 - External Anchor Dispersion Low-k Slice Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-07 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- Explicitly non-independent from CT-06 (`non_independent_of_CT06`)
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct07_external_anchor_dispersion_lowk_front_door`
- Outputs: `formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01/ct07_reference_report.json`, `formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01/ct07_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct07_external_anchor_dispersion_lowk_slice_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-10",
  "domain_id": "CT-DOMAIN-07",
  "fingerprint": "64a9f4a9e5d670c9f60335acafe8322f4b490f83b0279ad3414e32567417b6c8",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01",
    "candidate_artifact": "formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01/ct07_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct07_external_anchor_dispersion_lowk_domain_01/ct07_reference_report.json"
  },
  "observable_id": "CT-07",
  "rows": [
    {
      "artifact_id": "CT07_EXTERNAL_ANCHOR_LOWK_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6",
        "reference_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6"
      },
      "input_data_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6",
      "input_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6",
      "metric_vector": {
        "alpha_kHz2_um4": 0.0009043145499500443,
        "c_s2_kHz2_um2": 0.11126833980953973,
        "c_s2_scale": 1.0,
        "eps_max_abs_error_kHz": 0.2,
        "eps_reduced_chi2": 1.0,
        "eps_rmse_kHz": 0.1,
        "max_abs_error_kHz": 0.0652116948241594,
        "model_tag": "bogoliubov_proxy_fit_lowk_slice",
        "n_points": 7,
        "reduced_chi2": 0.2546506296979282,
        "rmse_kHz": 0.04264895156121561
      },
      "passed": true,
      "reason_codes": [
        "ct07_external_anchor_lowk_fit_ok"
      ],
      "source": {
        "candidate_config_tag": "ct07_external_anchor_dispersion_lowk_slice_v0",
        "candidate_regime_tag": "CT07_External_Anchor_Dispersion_LowK_Slice",
        "candidate_schema": "CT-07/external_anchor_dispersion_lowk_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct07_external_anchor_dispersion_lowk_slice_v0",
        "reference_regime_tag": "CT07_External_Anchor_Dispersion_LowK_Slice",
        "reference_schema": "CT-07/external_anchor_dispersion_lowk_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT07_EXTERNAL_ANCHOR_LOWK_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6",
        "reference_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6"
      },
      "input_data_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6",
      "input_fingerprint": "96ec74f0009713d7ccbaa8a280f1dba2631509cf6121aef9cab250651de538d6",
      "metric_vector": {
        "alpha_kHz2_um4": 0.0009043145499500443,
        "c_s2_kHz2_um2": 0.22253667961907947,
        "c_s2_scale": 2.0,
        "eps_max_abs_error_kHz": 0.2,
        "eps_reduced_chi2": 1.0,
        "eps_rmse_kHz": 0.1,
        "max_abs_error_kHz": 0.35517099078687264,
        "model_tag": "bogoliubov_proxy_cs2_scaled_lowk_slice",
        "n_points": 7,
        "reduced_chi2": 7.137758960660207,
        "rmse_kHz": 0.22579635199919496
      },
      "passed": true,
      "reason_codes": [
        "ct07_external_anchor_lowk_failure_detected"
      ],
      "source": {
        "candidate_config_tag": "ct07_external_anchor_dispersion_lowk_slice_v0",
        "candidate_regime_tag": "CT07_External_Anchor_Dispersion_LowK_Slice",
        "candidate_schema": "CT-07/external_anchor_dispersion_lowk_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control_model_break",
        "reference_config_tag": "ct07_external_anchor_dispersion_lowk_slice_v0",
        "reference_regime_tag": "CT07_External_Anchor_Dispersion_LowK_Slice",
        "reference_schema": "CT-07/external_anchor_dispersion_lowk_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-07_external_anchor_dispersion_lowk_slice_comparator/v0",
  "scope_limits": [
    "front_door_only",
    "typed_artifacts_only",
    "deterministic_record_only",
    "discriminative_candidate",
    "within_rep_only",
    "external_anchor",
    "non_independent_of_CT06",
    "no_external_truth_claim"
  ],
  "status": {
    "blocked": false,
    "reasons": []
  },
  "summary": {
    "artifacts": {
      "fail": [],
      "pass": [
        "CT07_EXTERNAL_ANCHOR_LOWK_POSITIVE",
        "CT07_EXTERNAL_ANCHOR_LOWK_NEGATIVE"
      ]
    },
    "counts": {
      "fail": 0,
      "pass": 2
    }
  },
  "tolerance_profile": "pinned"
}
```

Record fingerprint: `64a9f4a9e5d670c9f60335acafe8322f4b490f83b0279ad3414e32567417b6c8`
