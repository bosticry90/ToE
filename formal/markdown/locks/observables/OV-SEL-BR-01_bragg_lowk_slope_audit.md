# OV-SEL-BR-01 — Bragg low-k slope audit (computed)

Scope / limits
- Bookkeeping / narrative only; no physics claim
- Pins selection rule + asserts lock==computed for Bragg digitization and derived slope records

Narrative (operational)

Bragg low-k slope audit (bookkeeping-only; no physics claim):
0) External anchor: formal/external_evidence/bec_bragg_shammass_2012/source.pdf (sha256=ef5416e243b0863dada51b68483b72edf83e3b3870bf417b9215b236ea61207c).
1) OV-BR-03N digitization is render-based (axis text is rasterized), so provenance is pinned to a deterministic PNG render.
2) OV-BR-04A/04B derive low-k slopes using lowk_window_v1 (k<=1.0, 0.1<=omega<=1.3) and pinned OLS slope rules.
3) Governance posture: lock==computed for OV-BR-03N and OV-BR-04A/04B; frozen artifacts must exist; selection parameters are pinned.

Self-checks all_ok=True.

Record (computed)

```json
{
  "checks": {
    "OV-BR-03N": {
      "lock_fingerprint": "42751965b20c1b6b2d5897bbfea088a04f0cc15cb74c5e1e27a4e3d0dc92701f",
      "lock_path": "formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md",
      "ok": true
    },
    "OV-BR-03N condition_A CSV exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/k_omega_conditionA.csv"
    },
    "OV-BR-03N condition_B CSV exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/k_omega_conditionB.csv"
    },
    "OV-BR-03N metadata exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/k_omega_digitization.metadata.json"
    },
    "OV-BR-03N source PDF exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_bragg_shammass_2012/source.pdf"
    },
    "OV-BR-03N source PNG exists": {
      "exists": true,
      "path": "formal/external_evidence/bec_bragg_shammass_2012/page_renders/page6_z4.png"
    },
    "OV-BR-04A": {
      "lock_fingerprint": "99b210f200598b688c7ee936c53cdc657809248d030665f8e7ddd891ae3d1caa",
      "lock_path": "formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
      "ok": true
    },
    "OV-BR-04B": {
      "lock_fingerprint": "4621de7eaf20453a337d34bd1933c9681cbbbfdb11f4b4976aa120471b6ae26c",
      "lock_path": "formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md",
      "ok": true
    },
    "lowk_window_v1 params (A)": {
      "actual": {
        "k_um_inv_max": 1.0,
        "omega_over_2pi_kHz_max": 1.3,
        "omega_over_2pi_kHz_min": 0.1
      },
      "expected": {
        "k_um_inv_max": 1.0,
        "omega_over_2pi_kHz_max": 1.3,
        "omega_over_2pi_kHz_min": 0.1
      },
      "label": "selection_parameters",
      "ok": true
    },
    "lowk_window_v1 params (B)": {
      "actual": {
        "k_um_inv_max": 1.0,
        "omega_over_2pi_kHz_max": 1.3,
        "omega_over_2pi_kHz_min": 0.1
      },
      "expected": {
        "k_um_inv_max": 1.0,
        "omega_over_2pi_kHz_max": 1.3,
        "omega_over_2pi_kHz_min": 0.1
      },
      "label": "selection_parameters",
      "ok": true
    }
  },
  "fingerprint": "d71cf0af07039c983bb646298661800047d60c5fb0a4915158013f0d1a7fd2c9",
  "narrative": "Bragg low-k slope audit (bookkeeping-only; no physics claim):\n0) External anchor: formal/external_evidence/bec_bragg_shammass_2012/source.pdf (sha256=ef5416e243b0863dada51b68483b72edf83e3b3870bf417b9215b236ea61207c).\n1) OV-BR-03N digitization is render-based (axis text is rasterized), so provenance is pinned to a deterministic PNG render.\n2) OV-BR-04A/04B derive low-k slopes using lowk_window_v1 (k<=1.0, 0.1<=omega<=1.3) and pinned OLS slope rules.\n3) Governance posture: lock==computed for OV-BR-03N and OV-BR-04A/04B; frozen artifacts must exist; selection parameters are pinned.\n\nSelf-checks all_ok=True.",
  "schema": "OV-SEL-BR-01_bragg_lowk_slope_audit/v1",
  "status_date": "2026-01-25"
}
```

Record fingerprint: `d71cf0af07039c983bb646298661800047d60c5fb0a4915158013f0d1a7fd2c9`
