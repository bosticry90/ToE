# DS-02 (low-k) external dataset — source citation

Selection rules (pre-registered)
- Must provide multiple ω(k) points near k→0 (target ≥10 low-k points).
- Must be independent of the Steinhauer and Ernst sources (different group/paper preferred).
- Must be freely accessible (arXiv PDF or equivalent).

Source
- Paper: I. Shammass et al., “The phonon dispersion relation of a Bose–Einstein condensate” (2012)
- arXiv: https://arxiv.org/abs/1207.3440v2
- Local PDF: `formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/1207.3440v2.pdf`

Authoritative figure for DS-02
- Figure: Fig. 2 (ω_k/2π in kHz vs k in μm⁻¹)

Dataset selection (initial, minimal scope)
- Series selection: Use Fig. 2 **filled circles** (higher chemical potential / higher sound speed) only. Ignore open circles.
- Select exactly one series from Fig. 2 for DS-02 initial anchoring (treat the other chemical-potential series as a future DS-02b/auxiliary packet if needed).
- Overlap requirement: ensure digitization includes points up to **k ≥ 3.33842 μm⁻¹** so overlap with OV-03x’s high-k band is non-empty.
- Low-k density requirement: include many low-k points near k→0 (target ≥10 points with k ≤ 1.5 μm⁻¹).

Notes
- This dataset is intended as an independent low-k anchor slot (not Steinhauer / not Ernst).
