# OV-SEL-CT10-01 - CT-10 independent anchor selection verdict (pre-activation)

Scope / limits
- Governance-only pre-activation admission gate
- external_anchor_only posture
- No comparator claims are permitted
- No external truth claim

Record (deterministic)

```json
{
  "candidate_id": "CT10_CAND_AIR_ACOUSTICS_TOF_v1",
  "checks": {
    "citation_declares_non_bec_and_independence": {
      "detail": "source citation must declare independence and non-BEC posture",
      "ok": true
    },
    "filter_doc_has_admission_gate_language": {
      "detail": "CT-10 filter doc must contain selection-filter admission-gate posture",
      "ok": true
    },
    "metadata_schema_v1": {
      "detail": "metadata schema must match CT-10 v1",
      "ok": true
    },
    "not_bec_derived": {
      "detail": "candidate must be explicitly non-BEC-derived",
      "ok": true
    },
    "observable_surface_independent": {
      "detail": "observable surface must differ from existing dispersion and distance-time anchors",
      "ok": true
    },
    "preprocessing_declares_no_shared_lineage": {
      "detail": "preprocessing notes must declare no shared lineage",
      "ok": true
    },
    "preprocessing_lineage_statement_present": {
      "detail": "preprocessing lineage independence statement must be explicit",
      "ok": true
    },
    "required_intake_files_present": {
      "detail": "metadata/citation/preprocessing/dataset files must all exist",
      "ok": true
    },
    "source_family_independent": {
      "detail": "source family must differ from CT-06/07/08 and CT-09 families",
      "ok": true
    },
    "source_lineage_statement_present": {
      "detail": "source lineage independence statement must be explicit",
      "ok": true
    }
  },
  "failed_checks": [],
  "fingerprint": "14b3c839471f919240a8aca37326e3b442db19ff2c75116504bf2cb1f6c7ff16",
  "fingerprints": {
    "dataset_sha256": "09c297935d98950badc269c75b94f9da7f155cd793a9ae8c45c5ec9a269fe9bd",
    "filter_doc_sha256": "142239de98e5322e3e0346e7b682c86873951b2688845f95624853d45cc651b9",
    "metadata_sha256": "fd8fd05aca0dbb393aa830031b025d32781c3a2fb0de8ac9c2c530a6d15afa61",
    "preprocessing_lineage_sha256": "8fd7b9f1703838a6dcf333af68adafb51a714ea746c0e2f2c6f6379658902853",
    "source_citation_sha256": "d50dda8facfad0a987d32bb0af01c55da2d5a552fdf31008023c7ef0b0e24693"
  },
  "notes": "CT-10 selection verdict is pre-activation governance only. No comparator claim, no lane activation, and no external truth claim.",
  "observable_surface_id": "air_time_of_flight_distance_time",
  "policy": {
    "filter_doc": "formal/docs/programs/CT10_independent_external_anchor_selection_filter_v0.md",
    "mode": "pre_activation_admission_gate_only",
    "scope_limit": "external_anchor_only"
  },
  "schema": "OV-SEL-CT10-01_independent_anchor_selection_verdict/v1",
  "source_family_id": "air_acoustics_impulse_response_open_dataset_v1",
  "status_date": "2026-02-12",
  "verdict": "admissible"
}
```

Record fingerprint: `14b3c839471f919240a8aca37326e3b442db19ff2c75116504bf2cb1f6c7ff16`
