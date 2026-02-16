# CT-09 - Independent External Anchor Sound-Speed Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted CT-09 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- Independent external-anchor lane only
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.ct09_independent_external_anchor_sound_speed_front_door`
- Outputs: `formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_reference_report.json`, `formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_ct09_independent_external_anchor_sound_speed_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-11",
  "domain_id": "CT-DOMAIN-09",
  "fingerprint": "de83adfd2b4ca8715d56ba2fd1cc09b8a478daf6625f6c38645a61593d26900b",
  "inputs": {
    "artifact_dir": "formal/external_evidence/ct09_independent_sound_speed_domain_01",
    "candidate_artifact": "formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_candidate_report.json",
    "reference_artifact": "formal/external_evidence/ct09_independent_sound_speed_domain_01/ct09_reference_report.json"
  },
  "observable_id": "CT-09",
  "rows": [
    {
      "artifact_id": "CT09_INDEPENDENT_ANCHOR_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9",
        "reference_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9"
      },
      "input_data_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9",
      "input_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9",
      "metric_vector": {
        "c_um_per_ms": 0.48225601845841276,
        "eps_max_abs_error_um": 50.0,
        "eps_reduced_chi2": 2.8,
        "eps_rmse_um": 30.0,
        "intercept_um": 45.677025560591936,
        "max_abs_error_um": 48.557720149926055,
        "model_tag": "linear_speed_fit",
        "n_points": 11,
        "reduced_chi2": 2.6127876776572343,
        "rmse_um": 29.241992904921144
      },
      "passed": true,
      "reason_codes": [
        "ct09_independent_anchor_fit_ok"
      ],
      "source": {
        "candidate_config_tag": "ct09_independent_external_anchor_sound_speed_v0",
        "candidate_regime_tag": "CT09_Independent_External_Anchor_Sound_Speed",
        "candidate_schema": "CT-09/independent_external_anchor_sound_speed_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "ct09_independent_external_anchor_sound_speed_v0",
        "reference_regime_tag": "CT09_Independent_External_Anchor_Sound_Speed",
        "reference_schema": "CT-09/independent_external_anchor_sound_speed_front_door_report/v1"
      }
    },
    {
      "artifact_id": "CT09_INDEPENDENT_ANCHOR_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9",
        "reference_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9"
      },
      "input_data_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9",
      "input_fingerprint": "d42f594ec6ded12102a74c49b6f2e93c3da554d93863eb59ef0d5552eac747c9",
      "metric_vector": {
        "c_um_per_ms": 0.24112800922920638,
        "eps_max_abs_error_um": 50.0,
        "eps_reduced_chi2": 2.8,
        "eps_rmse_um": 30.0,
        "intercept_um": 45.677025560591936,
        "max_abs_error_um": 53.798140969169644,
        "model_tag": "linear_speed_scaled",
        "n_points": 11,
        "reduced_chi2": 2.932775195103008,
        "rmse_um": 30.98091891114862
      },
      "passed": true,
      "reason_codes": [
        "ct09_independent_anchor_failure_detected"
      ],
      "source": {
        "candidate_config_tag": "ct09_independent_external_anchor_sound_speed_v0",
        "candidate_regime_tag": "CT09_Independent_External_Anchor_Sound_Speed",
        "candidate_schema": "CT-09/independent_external_anchor_sound_speed_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control_model_break",
        "reference_config_tag": "ct09_independent_external_anchor_sound_speed_v0",
        "reference_regime_tag": "CT09_Independent_External_Anchor_Sound_Speed",
        "reference_schema": "CT-09/independent_external_anchor_sound_speed_front_door_report/v1"
      }
    }
  ],
  "schema": "CT-09_independent_external_anchor_sound_speed_comparator/v0",
  "scope_limits": [
    "front_door_only",
    "typed_artifacts_only",
    "deterministic_record_only",
    "discriminative_candidate",
    "within_rep_only",
    "external_anchor_only",
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
        "CT09_INDEPENDENT_ANCHOR_POSITIVE",
        "CT09_INDEPENDENT_ANCHOR_NEGATIVE"
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

Record fingerprint: `de83adfd2b4ca8715d56ba2fd1cc09b8a478daf6625f6c38645a61593d26900b`
