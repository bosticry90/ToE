# EA-03a — Evaluation note for OV-03x (B1 second external dataset)

This is an **evidence-only** application record of the EA-03 adequacy gate to OV-03x.

Summary (intended)
- OV-03x will be scoped as a **robustness-only** fit-family preference evaluation on a second external dataset.
- **β is not inferred**; language must remain compatible with $\beta=0$ (see DR-β-02).

Status

Applied to dataset
- Source: Ernst et al., arXiv:0908.4242v1 (2009)
- Figure: Fig. 2a
- Frozen CSV: `formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv`
	- sha256: `088acb258716352bb141eae080fdc22fc5e4ab52f10ee2ebf2c94ba14538f216`

Result
- OV-03x computed under `DQ-01_v1` yields:
	- `prefer_curved = false`
	- `robustness_failed = true`
	- report fingerprint: `c0a37f03755abfe64850a802a43cec285026734f893397d5030b10298ec61aa4`

Interpretation constraints
- This is a robustness-only result; negative / non-preference outcomes are admissible and must be recorded.
- \u03b2 is not inferred; language remains compatible with \u03b2=0 (DR-\u03b2-02).

Evidence
- `formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md`
