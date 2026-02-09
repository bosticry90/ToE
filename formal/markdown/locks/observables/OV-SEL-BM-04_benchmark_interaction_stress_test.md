# OV-SEL-BM-04 — Benchmark interaction stress test (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- Stress-tests that benchmarks cannot affect regime logic or selection
- No fitting; no averaging; no continuity claim; no cross-observable inference

Narrative (operational)

Benchmark interaction stress-test (bookkeeping-only; no physics claim):
Forbidden behaviors enumerated and blocked by construction: infer_continuity_across_benchmark_and_dataset_regimes, average_across_regimes_or_overlap_bands, allow_benchmarks_to_participate_in_selection_logic, allow_benchmarks_to_flip_preferences_or_threshold_outcomes.
This record confirms that benchmark observables remain non-participating nodes: OV-XD/OV-BR/OV-SEL bookkeeping locks do not reference OV-BM-* and their computed payloads remain unchanged.

Self-checks (lock==computed + negative reference checks) all_ok=True.

Record (computed)

```json
{
  "checks": {
    "No benchmark refs in OV-BR-02 (v1)": {
      "forbidden_tokens_found": [],
      "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
      "ok": true
    },
    "No benchmark refs in OV-SEL-01": {
      "forbidden_tokens_found": [],
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true
    },
    "No benchmark refs in OV-SEL-02": {
      "forbidden_tokens_found": [],
      "lock_path": "formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
      "ok": true
    },
    "No benchmark refs in OV-XD-03": {
      "forbidden_tokens_found": [],
      "lock_path": "formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
      "ok": true
    },
    "No benchmark refs in OV-XD-04 (v1)": {
      "forbidden_tokens_found": [],
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md",
      "ok": true
    },
    "OV-BM-01 lock": {
      "lock_fingerprint": "1ee5c6899cb28c404b2ab6c0ae79a6751a2363ddd5fc8b12c6acd0c9c44353b3",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling.md",
      "ok": true
    },
    "OV-BM-01N lock": {
      "lock_fingerprint": "bed12796e7427943b998f80ad5eb7de37dbcb26dd11c902e119b5a88b6210eb3",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling_digitized.md",
      "ok": true
    },
    "OV-BM-02 lock": {
      "lock_fingerprint": "0e32eee80d2065f24f99ab1524c76cb5a8deeb7d4372ac9986651d75d5c38b4e",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition.md",
      "ok": true
    },
    "OV-BR-02 (DQ-01_v2) lock": {
      "lock_fingerprint": "f2acf9f426e580dcf9265b238b5d611344baed22c4061e8c5701a11dcfb54d32",
      "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record_DQ-01_v2.md",
      "ok": true
    },
    "OV-BR-02 (v1) compares datasets": {
      "high_pref_observable_id": "OV-03x",
      "low_pref_observable_id": "OV-04x",
      "ok": true
    },
    "OV-BR-02 (v1) lock": {
      "lock_fingerprint": "3bb051329ae22c1f9649cca702f26c4cbe4adf8adcbc84cf0d9e79f880e5e8ac",
      "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
      "ok": true
    },
    "OV-DQ-02 lock": {
      "lock_fingerprint": "21674be85a5469750ce041a994281aea3529e21910d15a5795189f7a73ea20d0",
      "lock_path": "formal/markdown/locks/policies/DQ-01_v2_threshold_update.md",
      "ok": true
    },
    "OV-SEL-01 lock": {
      "lock_fingerprint": "14c4c9d4c49bf9f89c2f9f5e3418439d129b98e70f1d0b4d6006e5ed4f2cd5ed",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true
    },
    "OV-SEL-02 lock": {
      "lock_fingerprint": "b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
      "ok": true
    },
    "OV-SEL-BM-01 lock": {
      "lock_fingerprint": "cadf0ffda3919ff1bbce2c73deb472c2bc51a06f831723fa26498ec8d75101f3",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-BM-01_benchmark_ingestion_stress_test.md",
      "ok": true
    },
    "OV-SEL-BM-02 lock": {
      "lock_fingerprint": "9e2443df1a6e047607710e8b53afb566620a80e1bb4db7f327e43174a281dd45",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-BM-02_numeric_benchmark_ingestion_audit.md",
      "ok": true
    },
    "OV-XD-03 band IDs are non-benchmark": {
      "allowed": [
        "OV-01g",
        "OV-02x",
        "OV-03x",
        "OV-04x"
      ],
      "included_band_ids": [
        "OV-01g",
        "OV-02x",
        "OV-03x",
        "OV-04x"
      ],
      "ok": true,
      "unexpected_ids": []
    },
    "OV-XD-03 lock": {
      "lock_fingerprint": "e50a44d369d0ff9c4f56fc6756456df5ceaf9818a2632a6da56167ac551c674d",
      "lock_path": "formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
      "ok": true
    },
    "OV-XD-04 (DQ-01_v2) lock": {
      "lock_fingerprint": "a3e8603c2dcffa9d904c799a7349d328089ffc1bccf39a3e2a074bc83e92bf31",
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true
    },
    "OV-XD-04 (v1) compares datasets": {
      "high_observable_id": "OV-03x",
      "low_observable_id": "OV-04x",
      "ok": true
    },
    "OV-XD-04 (v1) lock": {
      "lock_fingerprint": "bc57a4634d303f601ce705a0f47b8db3c039499c1d7e5d19e914859c4930e77d",
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md",
      "ok": true
    }
  },
  "fingerprint": "05a0804c8231d09cd3b9b9a35c79460ed765f85d90954ae65731e95e358b21d3",
  "forbidden_behaviors": [
    "infer_continuity_across_benchmark_and_dataset_regimes",
    "average_across_regimes_or_overlap_bands",
    "allow_benchmarks_to_participate_in_selection_logic",
    "allow_benchmarks_to_flip_preferences_or_threshold_outcomes"
  ],
  "narrative": "Benchmark interaction stress-test (bookkeeping-only; no physics claim):\nForbidden behaviors enumerated and blocked by construction: infer_continuity_across_benchmark_and_dataset_regimes, average_across_regimes_or_overlap_bands, allow_benchmarks_to_participate_in_selection_logic, allow_benchmarks_to_flip_preferences_or_threshold_outcomes.\nThis record confirms that benchmark observables remain non-participating nodes: OV-XD/OV-BR/OV-SEL bookkeeping locks do not reference OV-BM-* and their computed payloads remain unchanged.\n\nSelf-checks (lock==computed + negative reference checks) all_ok=True.",
  "schema": "OV-SEL-BM-04_benchmark_interaction_stress_test/v1",
  "status_date": "2026-01-23"
}
```

Record fingerprint: `05a0804c8231d09cd3b9b9a35c79460ed765f85d90954ae65731e95e358b21d3`
