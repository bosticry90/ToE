# OV-SEL-02 — Selection status under DQ-01_v1 vs DQ-01_v2 (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- Evaluated set limited to OV-01g/OV-02x/OV-03x/OV-04x as represented in OV-DQ-01 policy sensitivity

Narrative (operational)

Selection status comparison (robustness-only; no physics claim):
- DQ-01_v1 uses q_threshold=0.9.
- DQ-01_v2 uses q_threshold=1.05.
- Evidence: C:/Users/psboy/Documents/ToE/formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json (fingerprint=df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871).
- Under v1: {'OV-01g': 'decisive_curved', 'OV-02x': 'decisive_curved', 'OV-03x': 'undecided', 'OV-04x': 'decisive_curved'}.
- Under v2: {'OV-01g': 'decisive_curved', 'OV-02x': 'decisive_curved', 'OV-03x': 'decisive_curved', 'OV-04x': 'decisive_curved'}.
- Delta: changed_observables=['OV-03x'] (expected: ['OV-03x']).
No continuity claim; no averaging across regimes; β not inferred / β-null posture.

Record (computed)

```json
{
  "delta": {
    "changed_observables": [
      "OV-03x"
    ],
    "v1": {
      "OV-01g": "decisive_curved",
      "OV-02x": "decisive_curved",
      "OV-03x": "undecided",
      "OV-04x": "decisive_curved"
    },
    "v2": {
      "OV-01g": "decisive_curved",
      "OV-02x": "decisive_curved",
      "OV-03x": "decisive_curved",
      "OV-04x": "decisive_curved"
    }
  },
  "evidence_artifact_fingerprint": "df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871",
  "evidence_artifact_relpath": "formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json",
  "fingerprint": "b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac",
  "narrative": "Selection status comparison (robustness-only; no physics claim):\n- DQ-01_v1 uses q_threshold=0.9.\n- DQ-01_v2 uses q_threshold=1.05.\n- Evidence: C:/Users/psboy/Documents/ToE/formal/python/artifacts/diagnostics/OV-DQ-01/OV-DQ-01_policy_sensitivity.json (fingerprint=df99ac9b86229135f2876be1a56d7abf0c730afe714ecee12d86fb9b7b50d871).\n- Under v1: {'OV-01g': 'decisive_curved', 'OV-02x': 'decisive_curved', 'OV-03x': 'undecided', 'OV-04x': 'decisive_curved'}.\n- Under v2: {'OV-01g': 'decisive_curved', 'OV-02x': 'decisive_curved', 'OV-03x': 'decisive_curved', 'OV-04x': 'decisive_curved'}.\n- Delta: changed_observables=['OV-03x'] (expected: ['OV-03x']).\nNo continuity claim; no averaging across regimes; \u03b2 not inferred / \u03b2-null posture.",
  "q_threshold_v1": 0.9,
  "q_threshold_v2": 1.05,
  "schema": "OV-SEL-02_selection_status_policy_compare/v1",
  "status_date": "2026-01-23",
  "v1": {
    "per_observable": {
      "OV-01g": {
        "changed": false,
        "observable_id": "OV-01g",
        "row_v1": {
          "blocking_reasons": [],
          "q_threshold": 0.9,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "row_v2": {
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "selection_status_v1": "decisive_curved",
        "selection_status_v2": "decisive_curved"
      },
      "OV-02x": {
        "changed": false,
        "observable_id": "OV-02x",
        "row_v1": {
          "all_scenarios_match_baseline": true,
          "baseline_prefer_curved": true,
          "blocking_reasons": [],
          "q_threshold": 0.9,
          "report_fingerprint": "cf84ad95aa67d81701c716f80309250ea0265beb3cfff4a962d2388391f614cc",
          "robustness_failed": false
        },
        "row_v2": {
          "all_scenarios_match_baseline": true,
          "baseline_prefer_curved": true,
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "report_fingerprint": "f165fb2d01fae46656eed377b3b6ac6f097d7f3a057453c3880146b04a0b1662",
          "robustness_failed": false
        },
        "selection_status_v1": "decisive_curved",
        "selection_status_v2": "decisive_curved"
      },
      "OV-03x": {
        "changed": true,
        "observable_id": "OV-03x",
        "row_v1": {
          "blocking_reasons": [
            "q_ratio_above_threshold"
          ],
          "q_threshold": 0.9,
          "robustness_failed": true,
          "would_prefer_curved": false
        },
        "row_v2": {
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "selection_status_v1": "undecided",
        "selection_status_v2": "decisive_curved"
      },
      "OV-04x": {
        "changed": false,
        "observable_id": "OV-04x",
        "row_v1": {
          "blocking_reasons": [],
          "q_threshold": 0.9,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "row_v2": {
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "selection_status_v1": "decisive_curved",
        "selection_status_v2": "decisive_curved"
      }
    },
    "summary": {
      "OV-01g": "decisive_curved",
      "OV-02x": "decisive_curved",
      "OV-03x": "undecided",
      "OV-04x": "decisive_curved"
    }
  },
  "v2": {
    "per_observable": {
      "OV-01g": {
        "changed": false,
        "observable_id": "OV-01g",
        "row_v1": {
          "blocking_reasons": [],
          "q_threshold": 0.9,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "row_v2": {
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "selection_status_v1": "decisive_curved",
        "selection_status_v2": "decisive_curved"
      },
      "OV-02x": {
        "changed": false,
        "observable_id": "OV-02x",
        "row_v1": {
          "all_scenarios_match_baseline": true,
          "baseline_prefer_curved": true,
          "blocking_reasons": [],
          "q_threshold": 0.9,
          "report_fingerprint": "cf84ad95aa67d81701c716f80309250ea0265beb3cfff4a962d2388391f614cc",
          "robustness_failed": false
        },
        "row_v2": {
          "all_scenarios_match_baseline": true,
          "baseline_prefer_curved": true,
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "report_fingerprint": "f165fb2d01fae46656eed377b3b6ac6f097d7f3a057453c3880146b04a0b1662",
          "robustness_failed": false
        },
        "selection_status_v1": "decisive_curved",
        "selection_status_v2": "decisive_curved"
      },
      "OV-03x": {
        "changed": true,
        "observable_id": "OV-03x",
        "row_v1": {
          "blocking_reasons": [
            "q_ratio_above_threshold"
          ],
          "q_threshold": 0.9,
          "robustness_failed": true,
          "would_prefer_curved": false
        },
        "row_v2": {
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "selection_status_v1": "undecided",
        "selection_status_v2": "decisive_curved"
      },
      "OV-04x": {
        "changed": false,
        "observable_id": "OV-04x",
        "row_v1": {
          "blocking_reasons": [],
          "q_threshold": 0.9,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "row_v2": {
          "blocking_reasons": [],
          "q_threshold": 1.05,
          "robustness_failed": false,
          "would_prefer_curved": true
        },
        "selection_status_v1": "decisive_curved",
        "selection_status_v2": "decisive_curved"
      }
    },
    "summary": {
      "OV-01g": "decisive_curved",
      "OV-02x": "decisive_curved",
      "OV-03x": "decisive_curved",
      "OV-04x": "decisive_curved"
    }
  }
}
```

Record fingerprint: `b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac`
