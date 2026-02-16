# CT-06 - External Anchor Dispersion Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-06 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct06_external_anchor_dispersion_front_door`
- Outputs: `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_reference_report.json`, `formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct06_external_anchor_dispersion_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-10",
  "domain_id": "CT-DOMAIN-06",
  "fingerprint": "01bb28c2660f67a4ea8bf79d142a56100af53565d6b5dcf49664623d269228ec",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct06_external_anchor_dispersion_domain_01",
    "candidate_artifact": "formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct06_external_anchor_dispersion_domain_01/ct06_reference_report.json"
  },
  "observable_id": "CT-06",
  "rows": [
    {
      "artifact_id": "CT06_EXTERNAL_ANCHOR_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26",
        "reference_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26"
      },
      "input_data_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26",
      "input_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26",
      "metric_vector": {
        "alpha_kHz2_um4": 0.003279769977220575,
        "c_s2_kHz2_um2": 0.14211244565541276,
        "eps_max_abs_error_kHz": 0.5,
        "eps_reduced_chi2": 4.0,
        "eps_rmse_kHz": 0.25,
        "max_abs_error_kHz": 0.1831786371161921,
        "model_tag": "bogoliubov_proxy_fit",
        "n_points": 13,
        "reduced_chi2": 1.4374778508971995,
        "rmse_kHz": 0.11123142658613483
      },
      "passed": true,
      "reason_codes": [
        "ct06_external_anchor_fit_ok"
      ],
      "source": {
        "candidate_config_tag": "ct06_external_anchor_dispersion_v0",
        "candidate_regime_tag": "CT06_External_Anchor_Dispersion",
        "candidate_schema": "CT-06/external_anchor_dispersion_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct06_external_anchor_dispersion_v0",
        "reference_regime_tag": "CT06_External_Anchor_Dispersion",
        "reference_schema": "CT-06/external_anchor_dispersion_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT06_EXTERNAL_ANCHOR_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26",
        "reference_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26"
      },
      "input_data_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26",
      "input_fingerprint": "313e51532491ae89723f0f907cacb06d2b795ad66d27108e09566b4a761c6d26",
      "metric_vector": {
        "alpha_kHz2_um4": 0.0016398849886102875,
        "c_s2_kHz2_um2": 0.14211244565541276,
        "eps_max_abs_error_kHz": 0.5,
        "eps_reduced_chi2": 4.0,
        "eps_rmse_kHz": 0.25,
        "max_abs_error_kHz": 3.1429610871508125,
        "model_tag": "bogoliubov_proxy_alpha_scaled",
        "n_points": 13,
        "reduced_chi2": 11.952007749007816,
        "rmse_kHz": 0.9749376535328318
      },
      "passed": true,
      "reason_codes": [
        "ct06_external_anchor_failure_detected"
      ],
      "source": {
        "candidate_config_tag": "ct06_external_anchor_dispersion_v0",
        "candidate_regime_tag": "CT06_External_Anchor_Dispersion",
        "candidate_schema": "CT-06/external_anchor_dispersion_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control_model_break",
        "reference_config_tag": "ct06_external_anchor_dispersion_v0",
        "reference_regime_tag": "CT06_External_Anchor_Dispersion",
        "reference_schema": "CT-06/external_anchor_dispersion_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-06_external_anchor_dispersion_comparator/v0",
  "scope_limits": [
    "front_door_only",
    "typed_artifacts_only",
    "deterministic_record_only",
    "discriminative_candidate",
    "within_rep_only",
    "external_anchor",
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
        "CT06_EXTERNAL_ANCHOR_POSITIVE",
        "CT06_EXTERNAL_ANCHOR_NEGATIVE"
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

Record fingerprint: `01bb28c2660f67a4ea8bf79d142a56100af53565d6b5dcf49664623d269228ec`
