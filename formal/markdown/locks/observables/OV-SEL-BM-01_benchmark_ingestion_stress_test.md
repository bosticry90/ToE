# OV-SEL-BM-01 — Benchmark ingestion stress test (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- Symbolic-only benchmarks; no digitization, no fitting
- No regime averaging; no continuity claim; no cross-observable inference

Narrative (operational)

Benchmark ingestion stress test (bookkeeping-only; no physics claim):
1) What changed? Added two symbolic-only benchmark observables OV-BM-01 and OV-BM-02 (Stenger 1999 reference provenance).
2) What did not change? No regime decisions, no preferences, no thresholds, no selection logic consequences.
3) Why? Benchmarks are non-decisive by design and are explicitly scope-fenced (no digitization, no fitting, no averaging, no continuity).

Self-checks (lock==computed) all_ok=True for canonical and DQ-01_v2-parallel downstream bookkeeping locks.

Record (computed)

```json
{
  "benchmarks": {
    "OV-BM-01": {
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-01_mean_field_line_shift_scaling.md",
      "non_decisive_by_design": true,
      "record_fingerprint": "1ee5c6899cb28c404b2ab6c0ae79a6751a2363ddd5fc8b12c6acd0c9c44353b3",
      "schema": "OV-BM-01_mean_field_line_shift_scaling_benchmark/v1",
      "symbolic_only": true
    },
    "OV-BM-02": {
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition.md",
      "non_decisive_by_design": true,
      "record_fingerprint": "0e32eee80d2065f24f99ab1524c76cb5a8deeb7d4372ac9986651d75d5c38b4e",
      "schema": "OV-BM-02_linewidth_quadrature_composition_benchmark/v1",
      "symbolic_only": true
    },
    "scope_fences": {
      "no_continuity_claim": true,
      "no_cross_observable_inference": true,
      "no_curve_fitting": true,
      "no_digitization": true,
      "no_regime_averaging": true
    }
  },
  "checks": {
    "OV-BR-02 (DQ-01_v2)": {
      "lock_fingerprint": "f2acf9f426e580dcf9265b238b5d611344baed22c4061e8c5701a11dcfb54d32",
      "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record_DQ-01_v2.md",
      "ok": true
    },
    "OV-BR-02 (v1)": {
      "lock_fingerprint": "3bb051329ae22c1f9649cca702f26c4cbe4adf8adcbc84cf0d9e79f880e5e8ac",
      "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
      "ok": true
    },
    "OV-DQ-02": {
      "lock_fingerprint": "21674be85a5469750ce041a994281aea3529e21910d15a5795189f7a73ea20d0",
      "lock_path": "formal/markdown/locks/policies/DQ-01_v2_threshold_update.md",
      "ok": true
    },
    "OV-SEL-01": {
      "lock_fingerprint": "14c4c9d4c49bf9f89c2f9f5e3418439d129b98e70f1d0b4d6006e5ed4f2cd5ed",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": true
    },
    "OV-SEL-02": {
      "lock_fingerprint": "b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
      "ok": true
    },
    "OV-XD-04 (DQ-01_v2)": {
      "lock_fingerprint": "a3e8603c2dcffa9d904c799a7349d328089ffc1bccf39a3e2a074bc83e92bf31",
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md",
      "ok": true
    },
    "OV-XD-04 (v1)": {
      "lock_fingerprint": "bc57a4634d303f601ce705a0f47b8db3c039499c1d7e5d19e914859c4930e77d",
      "lock_path": "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md",
      "ok": true
    }
  },
  "fingerprint": "cadf0ffda3919ff1bbce2c73deb472c2bc51a06f831723fa26498ec8d75101f3",
  "narrative": "Benchmark ingestion stress test (bookkeeping-only; no physics claim):\n1) What changed? Added two symbolic-only benchmark observables OV-BM-01 and OV-BM-02 (Stenger 1999 reference provenance).\n2) What did not change? No regime decisions, no preferences, no thresholds, no selection logic consequences.\n3) Why? Benchmarks are non-decisive by design and are explicitly scope-fenced (no digitization, no fitting, no averaging, no continuity).\n\nSelf-checks (lock==computed) all_ok=True for canonical and DQ-01_v2-parallel downstream bookkeeping locks.",
  "schema": "OV-SEL-BM-01_benchmark_ingestion_stress_test/v1",
  "status_date": "2026-01-23"
}
```

Record fingerprint: `cadf0ffda3919ff1bbce2c73deb472c2bc51a06f831723fa26498ec8d75101f3`
