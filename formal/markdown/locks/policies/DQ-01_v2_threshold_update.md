# OV-DQ-02 — DQ-01_v2 threshold update (computed policy lock)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- Documents a proposed / parallel policy definition; does not mutate canonical selection

Narrative (operational)

DQ-01_v2 threshold update (diagnostic evidence-based; no physics claim):
- Delta: q_threshold 0.9 -> 1.05 only (selection gate clause).
- Evidence: C:/Users/psboy/Documents/ToE/formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json (fingerprint=df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871).
- Observed impact set in evaluated suite: ['OV-03x'].
- Scope statement: within OV-01g/OV-02x/OV-03x/OV-04x as evaluated, only OV-03x changes; others are unchanged.

Record (computed)

```json
{
  "date": "2026-01-23",
  "delta": {
    "changed_fields": [
      "q_threshold"
    ],
    "note": "Threshold-only delta at the OV-01g family-selection gate layer; curved-fit adequacy policy is unchanged in this proposal.",
    "q_threshold_from": 0.9,
    "q_threshold_to": 1.05
  },
  "evidence_artifact_fingerprint": "df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871",
  "evidence_artifact_relpath": "formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json",
  "fingerprint": "21674be85a5469750ce041a994281aea3529e21910d15a5795189f7a73ea20d0",
  "from_policy": "DQ-01_v1",
  "impact_set": [
    "OV-03x"
  ],
  "narrative": "DQ-01_v2 threshold update (diagnostic evidence-based; no physics claim):\n- Delta: q_threshold 0.9 -> 1.05 only (selection gate clause).\n- Evidence: C:/Users/psboy/Documents/ToE/formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json (fingerprint=df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871).\n- Observed impact set in evaluated suite: ['OV-03x'].\n- Scope statement: within OV-01g/OV-02x/OV-03x/OV-04x as evaluated, only OV-03x changes; others are unchanged.",
  "per_observable": {
    "OV-01g": {
      "changed": false,
      "row_from": {
        "blocking_reasons": [],
        "q_threshold": 0.9,
        "robustness_failed": false,
        "would_prefer_curved": true
      },
      "row_q_threshold_from": 0.9,
      "row_q_threshold_to": 1.05,
      "row_to": {
        "blocking_reasons": [],
        "q_threshold": 1.05,
        "robustness_failed": false,
        "would_prefer_curved": true
      }
    },
    "OV-02x": {
      "changed": false,
      "row_from": {
        "all_scenarios_match_baseline": true,
        "baseline_prefer_curved": true,
        "blocking_reasons": [],
        "q_threshold": 0.9,
        "report_fingerprint": "cf84ad95aa67d81701c716f80309250ea0265beb3cfff4a962d2388391f614cc",
        "robustness_failed": false
      },
      "row_q_threshold_from": 0.9,
      "row_q_threshold_to": 1.05,
      "row_to": {
        "all_scenarios_match_baseline": true,
        "baseline_prefer_curved": true,
        "blocking_reasons": [],
        "q_threshold": 1.05,
        "report_fingerprint": "f165fb2d01fae46656eed377b3b6ac6f097d7f3a057453c3880146b04a0b1662",
        "robustness_failed": false
      }
    },
    "OV-03x": {
      "changed": true,
      "row_from": {
        "blocking_reasons": [
          "q_ratio_above_threshold"
        ],
        "q_threshold": 0.9,
        "robustness_failed": true,
        "would_prefer_curved": false
      },
      "row_q_threshold_from": 0.9,
      "row_q_threshold_to": 1.05,
      "row_to": {
        "blocking_reasons": [],
        "q_threshold": 1.05,
        "robustness_failed": false,
        "would_prefer_curved": true
      }
    },
    "OV-04x": {
      "changed": false,
      "row_from": {
        "blocking_reasons": [],
        "q_threshold": 0.9,
        "robustness_failed": false,
        "would_prefer_curved": true
      },
      "row_q_threshold_from": 0.9,
      "row_q_threshold_to": 1.05,
      "row_to": {
        "blocking_reasons": [],
        "q_threshold": 1.05,
        "robustness_failed": false,
        "would_prefer_curved": true
      }
    }
  },
  "q_threshold_from": 0.9,
  "q_threshold_to": 1.05,
  "schema": "OV-DQ-02_dq01_v2_threshold_update/v1",
  "to_policy": "DQ-01_v2"
}
```

Record fingerprint: `21674be85a5469750ce041a994281aea3529e21910d15a5795189f7a73ea20d0`
