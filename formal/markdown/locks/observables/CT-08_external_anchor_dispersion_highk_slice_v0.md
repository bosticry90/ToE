# CT-08 - External Anchor Dispersion High-k Slice Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-08 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- Explicitly non-independent from CT-06 (`non_independent_of_CT06`)
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct08_external_anchor_dispersion_highk_front_door`
- Outputs: `formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/ct08_reference_report.json`, `formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/ct08_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-10",
  "domain_id": "CT-DOMAIN-08",
  "fingerprint": "48081e7702164922f01cfb6b253cbee13dc109d452c78ccf5d1b196d479bf9e4",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01",
    "candidate_artifact": "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/ct08_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/ct08_reference_report.json"
  },
  "observable_id": "CT-08",
  "rows": [
    {
      "artifact_id": "CT08_EXTERNAL_ANCHOR_HIGHK_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe",
        "reference_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe"
      },
      "input_data_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe",
      "input_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe",
      "metric_vector": {
        "alpha_kHz2_um4": 0.003278502426357671,
        "alpha_scale": 1.0,
        "c_s2_kHz2_um2": 0.1423655101110897,
        "eps_max_abs_error_kHz": 0.5,
        "eps_reduced_chi2": 4.0,
        "eps_rmse_kHz": 0.25,
        "max_abs_error_kHz": 0.18425970657582025,
        "model_tag": "bogoliubov_proxy_fit_highk_slice",
        "n_points": 7,
        "reduced_chi2": 2.3117260525332464,
        "rmse_kHz": 0.12998203147630327
      },
      "passed": true,
      "reason_codes": [
        "ct08_external_anchor_highk_fit_ok"
      ],
      "source": {
        "candidate_config_tag": "ct08_external_anchor_dispersion_highk_slice_v0",
        "candidate_regime_tag": "CT08_External_Anchor_Dispersion_HighK_Slice",
        "candidate_schema": "CT-08/external_anchor_dispersion_highk_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct08_external_anchor_dispersion_highk_slice_v0",
        "reference_regime_tag": "CT08_External_Anchor_Dispersion_HighK_Slice",
        "reference_schema": "CT-08/external_anchor_dispersion_highk_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT08_EXTERNAL_ANCHOR_HIGHK_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe",
        "reference_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe"
      },
      "input_data_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe",
      "input_fingerprint": "8f7b34fa5128fc3a57831c41b3ee16e5bd6faf0afedf951ebfd365c8c378ebbe",
      "metric_vector": {
        "alpha_kHz2_um4": 0.0016392512131788355,
        "alpha_scale": 0.5,
        "c_s2_kHz2_um2": 0.1423655101110897,
        "eps_max_abs_error_kHz": 0.5,
        "eps_reduced_chi2": 4.0,
        "eps_rmse_kHz": 0.25,
        "max_abs_error_kHz": 3.1417312687688597,
        "model_tag": "bogoliubov_proxy_alpha_scaled_highk_slice",
        "n_points": 7,
        "reduced_chi2": 25.49778652239275,
        "rmse_kHz": 1.3258537121896636
      },
      "passed": true,
      "reason_codes": [
        "ct08_external_anchor_highk_failure_detected"
      ],
      "source": {
        "candidate_config_tag": "ct08_external_anchor_dispersion_highk_slice_v0",
        "candidate_regime_tag": "CT08_External_Anchor_Dispersion_HighK_Slice",
        "candidate_schema": "CT-08/external_anchor_dispersion_highk_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control_model_break",
        "reference_config_tag": "ct08_external_anchor_dispersion_highk_slice_v0",
        "reference_regime_tag": "CT08_External_Anchor_Dispersion_HighK_Slice",
        "reference_schema": "CT-08/external_anchor_dispersion_highk_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-08_external_anchor_dispersion_highk_slice_comparator/v0",
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
        "CT08_EXTERNAL_ANCHOR_HIGHK_POSITIVE",
        "CT08_EXTERNAL_ANCHOR_HIGHK_NEGATIVE"
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

Record fingerprint: `48081e7702164922f01cfb6b253cbee13dc109d452c78ccf5d1b196d479bf9e4`
