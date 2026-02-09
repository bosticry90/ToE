# OV-SND-01 — Sound-speed scaling anchor (computed)

Scope / limits
- Symbolic-first anchor; dependency structure only; no physics validation claim
- No fitting; no parameter inference; no continuity/averaging across regimes

Record (computed)

```json
{
  "date": "2026-01-24",
  "fingerprint": "fd28690a5df536f9bbf17602e3ce28f5b35245dfb6bc2b80769279e4a5e6cbbf",
  "observable_id": "OV-SND-01",
  "schema": "OV-SND-01_sound_speed_scaling_anchor/v1",
  "scope_limits": [
    "symbolic_only",
    "no_fitting",
    "no_parameter_inference",
    "no_continuity_claim",
    "no_cross_regime_averaging",
    "non_decisive_by_design"
  ],
  "source": {
    "arxiv_pdf_relpath": "formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf",
    "arxiv_pdf_sha256": "d38a5d54cca6b4b7a4a71647c20d24bf72b434eca2e1ed943df62f981f3a7cc6",
    "citation": "Kavoulakis & Pethick (1997), arXiv:9711224v1 \u2014 Sound Propagation in Elongated Bose-Einstein Condensed Clouds (references Andrews et al. experiment)"
  },
  "statement": {
    "observable_definition": "Sound speed c inferred from propagation of a density disturbance along the long axis; anchor focuses on the dependency structure, not parameter extraction.",
    "regime": "phonon / hydrodynamic (low-k)",
    "scaling": {
      "c_proportional_to": "sqrt(n)",
      "canonical_relation": "c^2 = dP/d\u03c1 \u2248 n U0 / m (homogeneous, T\u22480)",
      "notes": "In an elongated trapped condensate, cross-section averaging can introduce geometric factors (e.g., average density ~ 1/2 of axial density for harmonic transverse confinement)."
    }
  }
}
```

Record fingerprint: `fd28690a5df536f9bbf17602e3ce28f5b35245dfb6bc2b80769279e4a5e6cbbf`
