# Cross-anchor comparison: Bragg low-k slope vs sound propagation

Generated: 2026-01-29 19:37:05

Scope / limits
- Bookkeeping-only: this report does not assert physical comparability.
- Uses locked derived values and a pinned unit conversion: Bragg $c_{\mathrm{mm/s}}$ → $c_{\mathrm{m/s}}$ via $1\,\mathrm{mm/s}=10^{-3}\,\mathrm{m/s}$.
- Any cross-lane pairing justification (density mapping) must come from the BR↔SND mapping locks; this report does not invent one.

Cross-lane audit context
- Audit lock: `formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit_OVERRIDE.md`
- comparability.status: `absent`
- criterion tolerance (relative error): 0.15
- comparability.reasons: CONVERSION_CHAIN_PINNED, CRITERION_DEFINED, NO_MAPPING_TUPLE, NO_JUSTIFIED_PAIRING

## Inputs (locks + fingerprints)
| Quantity | Lock | Fingerprint | Value | SE |
| --- | --- | --- | --- | --- |
| Bragg condition_A | formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md | 093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1 | 0.00137831 m/s | 0.00033783 |
| Bragg condition_B | formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md | 093c40dcfc088f16b0b40b082c53aa6d9e7410f74294e256b1592861550675e1 | 0.000972931 m/s | 0.000160123 |
| Sound OV-SND-02 | formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md | 1e1e1f09907117e081fb9be9cab34d39884cf66acc8e2811d807e0a2db7a1dbe | 0.00142989 m/s | 0.000271131 |
| Sound OV-SND-02B | formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md | 20847369ccb9572fda4fac8101ed61937ad10ca9e245567fa9c27344aea04810 | 0.00153835 m/s | 0.000169814 |

## Numeric comparisons (no pairing asserted)
| Bragg | Sound | Bragg (m/s) | SE_b | Sound (m/s) | SE_s | |Δ| (m/s) | rel_err | z | tol check |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Bragg condition_A | Sound OV-SND-02 | 0.00137831 | 0.00033783 | 0.00142989 | 0.000271131 | 5.15745e-05 | 0.036069 | -0.119061 | PASS |
| Bragg condition_A | Sound OV-SND-02B | 0.00137831 | 0.00033783 | 0.00153835 | 0.000169814 | 0.000160041 | 0.104034 | -0.423267 | PASS |
| Bragg condition_B | Sound OV-SND-02 | 0.000972931 | 0.000160123 | 0.00142989 | 0.000271131 | 0.000456954 | 0.319574 | -1.45118 | FAIL |
| Bragg condition_B | Sound OV-SND-02B | 0.000972931 | 0.000160123 | 0.00153835 | 0.000169814 | 0.00056542 | 0.367549 | -2.42252 | FAIL |

Interpretation notes
- A FAIL on `tol check` (if a tolerance is present) is not a physics contradiction by itself; it can reflect absent/invalid cross-lane pairing prerequisites.
- Use the cross-lane mapping locks (e.g. OV-BR-SND-01/02) to justify whether a given Bragg condition and sound dataset should be compared at all.
