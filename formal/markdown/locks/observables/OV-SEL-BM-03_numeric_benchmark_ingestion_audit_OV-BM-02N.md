# OV-SEL-BM-03 — Numeric benchmark ingestion audit (OV-BM-02N) (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- Benchmark-only numeric ingestion; no fitting; no averaging; no continuity claim

Narrative (operational)

Numeric benchmark ingestion audit (bookkeeping-only; no physics claim):
1) What changed? Added OV-BM-02N: a minimal numeric digitization (linewidth vs peak density) plus pinned CSV/metadata and a computed benchmark lock.
2) What did not change? No policy thresholds changed; no regime bridge behavior changed; no selection logic consequences; no continuity or averaging inferred.
3) Why? OV-BM-02N is explicitly benchmark-only and scope-fenced; it is not part of fit-family selection and is introduced solely to stress-test numeric ingestion determinism.

Self-checks (lock==computed + file existence) all_ok=False for OV-BM-02N and canonical/DQ-01_v2-parallel governance locks.

Record (computed)

```json
{
  "benchmark_numeric": {
    "benchmark_only": true,
    "csv_relpath": "formal/external_evidence/bec_bragg_stenger_1999/ovbm02_digitization/linewidth_vs_peak_density_triangles.csv",
    "csv_sha256": "5e65ee0d81e96ecbe3389db01e25c658e1e66f7e88062c8ed391d032733c7f76",
    "digitization_id": "OV-BM-02N",
    "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition_digitized.md",
    "observable_id": "OV-BM-02",
    "record_fingerprint": "1521fc3190d43b74d09e68616618e6987afec354570a65fe997fc90cd238432c",
    "schema": "OV-BM-02_linewidth_quadrature_composition_digitized/v1"
  },
  "checks": {
    "OV-BM-02N CSV exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_bragg_stenger_1999/ovbm02_digitization/linewidth_vs_peak_density_triangles.csv"
    },
    "OV-BM-02N lock": {
      "lock_fingerprint": "1521fc3190d43b74d09e68616618e6987afec354570a65fe997fc90cd238432c",
      "lock_path": "formal/markdown/locks/benchmarks/OV-BM-02_linewidth_quadrature_composition_digitized.md",
      "ok": true
    },
    "OV-BM-02N metadata exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_bragg_stenger_1999/ovbm02_digitization/linewidth_vs_peak_density_triangles.metadata.json"
    },
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
      "ok": false
    },
    "OV-SEL-01": {
      "lock_fingerprint": "14c4c9d4c49bf9f89c2f9f5e3418439d129b98e70f1d0b4d6006e5ed4f2cd5ed",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
      "ok": false
    },
    "OV-SEL-02": {
      "lock_fingerprint": "b1c55cab148727c9da2556ffe8d8a7cbe0dbd7304c373204cb57e12ca6d580ac",
      "lock_path": "formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
      "ok": false
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
  "fingerprint": "ea066b61f51ac89723e7d8faf5364513d083c42ed18c3d177d83dfc939362a61",
  "narrative": "Numeric benchmark ingestion audit (bookkeeping-only; no physics claim):\n1) What changed? Added OV-BM-02N: a minimal numeric digitization (linewidth vs peak density) plus pinned CSV/metadata and a computed benchmark lock.\n2) What did not change? No policy thresholds changed; no regime bridge behavior changed; no selection logic consequences; no continuity or averaging inferred.\n3) Why? OV-BM-02N is explicitly benchmark-only and scope-fenced; it is not part of fit-family selection and is introduced solely to stress-test numeric ingestion determinism.\n\nSelf-checks (lock==computed + file existence) all_ok=False for OV-BM-02N and canonical/DQ-01_v2-parallel governance locks.",
  "schema": "OV-SEL-BM-03_numeric_benchmark_ingestion_audit_OV-BM-02N/v1",
  "status_date": "2026-01-24"
}
```

Record fingerprint: `ea066b61f51ac89723e7d8faf5364513d083c42ed18c3d177d83dfc939362a61`
