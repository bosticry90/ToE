# Data fingerprint (TBD)

This file should be updated once `omega_k_data.csv` is populated.

Required contents (when frozen)
- Canonical hash of `omega_k_data.csv` contents (e.g., sha256).
- Row count and basic schema confirmation.
- Any digitization tolerances or rounding rules.

Current state
- `omega_k_data.csv` populated (Ernst 2009 arXiv:0908.4242v1 Fig2a; single series).
- sha256: `088acb258716352bb141eae080fdc22fc5e4ab52f10ee2ebf2c94ba14538f216`
- rows: 17

Digitization protocol snapshot (for audit)
- Source: Ernst 2009 arXiv:0908.4242v1 Fig2a
- Series: single series only (digitized via strict-branch selection; no mixing)
- Point-picking rule: all visible markers between leftmost and rightmost on that series
- Axis calibration ticks:
	- kBragg: 0.0 and 1.0
	- ω/2π (kHz): 0.0 and 2.5
- Sigmas: placeholders (uniform; no mixing)
	- sigma_k_um_inv = 0.05
	- sigma_omega_over_2pi_kHz = 0.10

Strict-branch selection parameters (frozen)
- k-cluster-tol = 0.0005
- omega-nondecreasing-tol = 0.03
- omega-decrease-penalty = 5.0

## Local PDF fingerprint(s) (for provenance)

Primary intended B1 source (pending):
- `0908.4242v1.pdf` sha256: `27b533a0a510c5acf958031b56f9b9d0b426a12dbe1baa625a53f5e3e71d2736`

Audit note (previously reviewed, not used for B1 \u03c9(k)):
- `Stamper-Kurn_1999_PRL.pdf` sha256: `7444d8baa4f2e8531fc812eb7b90cc20382cc3bf626ef41cfc65efa46482b5fd`
