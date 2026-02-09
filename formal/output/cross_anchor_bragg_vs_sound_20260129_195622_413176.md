# Cross-anchor comparison: Bragg low-k slope vs sound propagation

Generated: 2026-01-29 19:56:22

MODE=NUMERIC_ONLY
TOTAL=4

Scope / limits
- Bookkeeping-only: this report does not assert physical comparability.
- Uses locked derived values and a pinned unit conversion: Bragg $c_{\mathrm{mm/s}}$ → $c_{\mathrm{m/s}}$ via $1\,\mathrm{mm/s}=10^{-3}\,\mathrm{m/s}$.
- Any cross-lane pairing justification (comparability + mapping tuples) must come from OV-BR-SND-01/02 and explicit Bragg↔Sound pairing tuples; this report does not invent one.

Cross-lane audit context
- Audit lock: `formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit_OVERRIDE.md`
- comparability.status: `absent`
- criterion tolerance (relative error): 0.15
- comparability.reasons: CONVERSION_CHAIN_PINNED, CRITERION_DEFINED, NO_MAPPING_TUPLE, NO_JUSTIFIED_PAIRING

Gating inputs
- OV-BR-SND-01 lock: `formal/markdown/locks/observables/OV-BR-SND-01_sound_vs_bragg_lowk_comparability.md`
  - OV-BR-SND-01 comparability.status: `not_compared_quantitatively`
  - OV-BR-SND-01 current_blockers: OV-04x does not compute c, OV-SND-02 has no density calibration (no n inference)
  - OV-BR-SND-01 gate_ok: `False`
- OV-BR-SND-02 lock: `formal/markdown/locks/observables/OV-BR-SND-02_cross_source_density_mapping.md`
  - OV-BR-SND-02 mapping.status: `unblocked`
  - OV-BR-SND-02 mapping_tuples_count: 2
  - OV-BR-SND-02 gate_ok: `True`
- Bragg↔Sound pairing tuples: `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json`
  - mapping_tuples_count: 0

## Inputs (locks + fingerprints)
| Quantity | Lock | Fingerprint | Value | SE |
| --- | --- | --- | --- | --- |
| Bragg condition_A | formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md | 093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1 | 0.00137831 m/s | 0.00033783 |
| Bragg condition_B | formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md | 093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1 | 0.000972931 m/s | 0.000160123 |
| Sound OV-SND-02 | formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md | 1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe | 0.00142989 m/s | 0.000271131 |
| Sound OV-SND-02B | formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md | 20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810 | 0.00153835 m/s | 0.000169814 |

## Numeric comparisons (numeric-only; not a justified pairing)
| Bragg | Sound | Bragg (m/s) | SE_b | Sound (m/s) | SE_s | |Δ| (m/s) | rel_err | z | tol check |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Bragg condition_A | Sound OV-SND-02 | 0.00137831 | 0.00033783 | 0.00142989 | 0.000271131 | 5.15745e-05 | 0.036069 | -0.119061 | PASS |
| Bragg condition_A | Sound OV-SND-02B | 0.00137831 | 0.00033783 | 0.00153835 | 0.000169814 | 0.000160041 | 0.104034 | -0.423267 | PASS |
| Bragg condition_B | Sound OV-SND-02 | 0.000972931 | 0.000160123 | 0.00142989 | 0.000271131 | 0.000456954 | 0.319574 | -1.45118 | FAIL |
| Bragg condition_B | Sound OV-SND-02B | 0.000972931 | 0.000160123 | 0.00153835 | 0.000169814 | 0.00056542 | 0.367549 | -2.42252 | FAIL |

Interpretation notes
- In `MODE=NUMERIC_ONLY`, rows are bookkeeping-only and do not assert a justified physical pairing.
- A FAIL on `tol check` (if a tolerance is present) is not a physics contradiction by itself; it can reflect model/uncertainty gaps or an overly strict tolerance.
- Use OV-BR-SND-01/02 and the explicit Bragg↔Sound pairing tuples to justify whether a given Bragg condition and sound dataset should be compared at all.
