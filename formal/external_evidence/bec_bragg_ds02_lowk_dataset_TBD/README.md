# DS-02 (low-k) dataset packet

This folder contains the DS-02 low-k external ω(k) dataset packet used as an independent low-k anchor.

Source
- Shammass et al. (2012), arXiv:1207.3440v2 (see `1207.3440v2.pdf`)
- Figure: Fig. 2 (ω_k/2π vs k)

Discipline
- Robustness-only usage (no physics claim).
- β-null posture: β not inferred / compatible with 0.

Next step (once `omega_k_data.csv` is populated)
- Optional: print a quick DS-02 summary (counts + computed DR04d minN5 cutoff): `python -m formal.python.tools.generate_ds02_dr_artifacts --report`
- Generate the four DS-02 DR window artifacts: `python -m formal.python.tools.generate_ds02_dr_artifacts`
