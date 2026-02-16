# OV-RL-09 - Dispersion-Topology Bridge Comparator v0 (front-door, deterministic)

Scope / limits
- Deterministic comparator record only
- Typed/fingerprinted RL09 report artifacts only
- Expectation-aware pass semantics for positive/negative controls
- No external truth claim

Reproduce (pinned)
- Command: `.\py.ps1 -m formal.python.tools.rl09_dispersion_topology_bridge_front_door`
- Outputs: `formal/external_evidence/rl09_dispersion_topology_bridge_domain_01/rl09_reference_report.json`, `formal/external_evidence/rl09_dispersion_topology_bridge_domain_01/rl09_candidate_report.json`
- Verify: `.\py.ps1 -m pytest formal/python/tests/test_rl09_dispersion_topology_bridge_v0_lock.py -q`

Record (computed)

```json
{
  "comparator_role": "discriminative_candidate",
  "date": "2026-02-09",
  "domain_id": "DRBR-DOMAIN-RL-09",
  "fingerprint": "d7197c3fe14acc2534d3cd24a90ab7d960107f656e9d54eb9aa12e99bb1309b5",
  "inputs": {
    "artifact_dir": "formal/external_evidence/rl09_dispersion_topology_bridge_domain_01",
    "candidate_artifact": "formal/external_evidence/rl09_dispersion_topology_bridge_domain_01/rl09_candidate_report.json",
    "reference_artifact": "formal/external_evidence/rl09_dispersion_topology_bridge_domain_01/rl09_reference_report.json"
  },
  "observable_id": "OV-RL-09",
  "rows": [
    {
      "artifact_id": "RL09_TOPOLOGY_POSITIVE",
      "diagnostics": {
        "candidate_fingerprint": "9932a8e69b1e8926e6242a45d81de5d954ff3f5181330d764ece5c55f39b4ed4",
        "k_count_candidate": 256,
        "k_count_reference": 256,
        "k_grid_aligned": true,
        "k_grid_order_candidate": true,
        "k_grid_order_reference": true,
        "reference_fingerprint": "bb1ffef24e6e4cf35979cf7a29356a3832e78c98b4717665a600f7b132a3dc0f"
      },
      "input_data_fingerprint": "9932a8e69b1e8926e6242a45d81de5d954ff3f5181330d764ece5c55f39b4ed4",
      "input_fingerprint": "9932a8e69b1e8926e6242a45d81de5d954ff3f5181330d764ece5c55f39b4ed4",
      "metric_vector": {
        "abs_err": 4.440892098500626e-16,
        "min_energy": 0.5,
        "target_winding": 1.0,
        "winding_raw": 1.0000000000000004,
        "winding_rounded": 1
      },
      "passed": true,
      "reason_codes": [
        "rl09_winding_target_satisfied"
      ],
      "source": {
        "candidate_config_tag": "rl09-cand-pinned",
        "candidate_regime_tag": "rl09-dispersion-topology",
        "candidate_schema": "RL/dispersion_topology_front_door_report/v1",
        "case_id": "POSITIVE",
        "case_kind": "positive_control",
        "reference_config_tag": "rl09-ref-pinned",
        "reference_regime_tag": "rl09-dispersion-topology",
        "reference_schema": "RL/dispersion_topology_front_door_report/v1"
      }
    },
    {
      "artifact_id": "RL09_TOPOLOGY_NEGATIVE",
      "diagnostics": {
        "candidate_fingerprint": "9932a8e69b1e8926e6242a45d81de5d954ff3f5181330d764ece5c55f39b4ed4",
        "k_count_candidate": 256,
        "k_count_reference": 256,
        "k_grid_aligned": true,
        "k_grid_order_candidate": true,
        "k_grid_order_reference": true,
        "reference_fingerprint": "bb1ffef24e6e4cf35979cf7a29356a3832e78c98b4717665a600f7b132a3dc0f"
      },
      "input_data_fingerprint": "9932a8e69b1e8926e6242a45d81de5d954ff3f5181330d764ece5c55f39b4ed4",
      "input_fingerprint": "9932a8e69b1e8926e6242a45d81de5d954ff3f5181330d764ece5c55f39b4ed4",
      "metric_vector": {
        "abs_err": 2.8271597168564594e-16,
        "min_energy": 0.5,
        "target_winding": 0.0,
        "winding_raw": 2.8271597168564594e-16,
        "winding_rounded": 0
      },
      "passed": true,
      "reason_codes": [
        "rl09_winding_target_satisfied"
      ],
      "source": {
        "candidate_config_tag": "rl09-cand-pinned",
        "candidate_regime_tag": "rl09-dispersion-topology",
        "candidate_schema": "RL/dispersion_topology_front_door_report/v1",
        "case_id": "NEGATIVE",
        "case_kind": "negative_control",
        "reference_config_tag": "rl09-ref-pinned",
        "reference_regime_tag": "rl09-dispersion-topology",
        "reference_schema": "RL/dispersion_topology_front_door_report/v1"
      }
    }
  ],
  "schema": "OV-RL-09_dispersion_topology_bridge_comparator/v0",
  "scope_limits": [
    "front_door_only",
    "typed_artifacts_only",
    "deterministic_record_only",
    "discriminative_candidate",
    "within_rep_only",
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
        "RL09_TOPOLOGY_POSITIVE",
        "RL09_TOPOLOGY_NEGATIVE"
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

Record fingerprint: `d7197c3fe14acc2534d3cd24a90ab7d960107f656e9d54eb9aa12e99bb1309b5`
