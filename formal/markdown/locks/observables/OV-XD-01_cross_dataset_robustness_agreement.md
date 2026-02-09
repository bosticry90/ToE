# OV-XD-01 — Cross-dataset robustness agreement (OV-01g, OV-02x, OV-03x)

Purpose
- Single, auditable summary of cross-dataset robustness-only outcomes **without interpretation**: agreement or disagreement is recorded as-is.

Scope / limits
- Summary-only; does not add new data or new modeling.
- Must not be used for β inference; language remains compatible with β=0.

Included observables

## OV-01g (Steinhauer 2001/2002 Bragg ω(k))

- Status: Empirically Anchored (see State_of_the_Theory inventory)
- Core meaning: robustness-only curved-vs-linear preference under frozen Steinhauer digitization and declared window artifacts.

## OV-02x (Digitization / instrument invariance on Steinhauer)

- Status: Empirically Anchored (see State_of_the_Theory inventory)
- Core meaning: invariance of the OV-01g preference under bounded, deterministic digitization perturbations.

## OV-03x (Ernst et al., arXiv:0908.4242v1, Fig. 2a)

- Status: Empirically Anchored (see State_of_the_Theory inventory)
- External source: `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/0908.4242v1.pdf` (Fig. 2a)
- Frozen CSV: `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv`
- OV-03x lock: `formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md`
  - prefer_curved: false
  - robustness_failed: true
  - report fingerprint: `c0a37f03755abfe64850a802a43cec285026734f893397d5030b10298ec61aa4`

Agreement statement (operational)
- OV-01g and OV-02x record a curved-family preference under declared gates.
- OV-03x (with the current frozen Fig. 2a digitization + declared windows) records a negative result for that preference (robustness_failed=true), while remaining β-null (β not inferred / compatible with 0).
- This lock therefore records a cross-dataset disagreement at present; it is a bookkeeping snapshot, not an interpretation.
