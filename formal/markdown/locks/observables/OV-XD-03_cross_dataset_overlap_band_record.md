# OV-XD-03 — Cross-dataset overlap band record (computed)

Purpose
- Deterministically compute per-dataset k-coverage bands for the datasets used by OV-XD bookkeeping and compute their overlap band.

Scope / limits
- Bookkeeping only; no physics claim.
- Must not be used for β inference.
- Computed overlap is the intersection of k-coverage bands (not a union).

Inclusion policy (v2)
- OV-04x (DS-02 low-k slot) is included only when DS-02 is populated; otherwise it is explicitly excluded with a reason.

Computation
- Module: `formal/python/toe/observables/ovxd03_overlap_band_record.py`
- Inputs: frozen CSVs in `formal/external_evidence/...`

Record (computed)

```json
{
  "bands": {
    "OV-01g": {
      "k_max": 14.589675116826,
      "k_min": 0.41847843636
    },
    "OV-02x": {
      "k_max": 14.589675116826,
      "k_min": 0.41847843636
    },
    "OV-03x": {
      "k_max": 8.28312,
      "k_min": 3.33842
    },
    "OV-04x": {
      "k_max": 4.45157988663,
      "k_min": 0.006351039261
    }
  },
  "excluded": {},
  "included_band_ids": [
    "OV-01g",
    "OV-02x",
    "OV-03x",
    "OV-04x"
  ],
  "notes": "Operational only; bookkeeping record; no physics claim. Overlap is computed as the intersection across included bands; excluded slots are listed explicitly.",
  "overlap": {
    "k_max": 4.45157988663,
    "k_min": 3.33842,
    "non_empty": true
  },
  "provenance": {
    "OV-01g": {
      "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv",
      "csv_sha256": "a31e3440c1847c590eeeb72e32dbc28b912463622d1edba7e708e239919f0fcf"
    },
    "OV-02x": {
      "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv",
      "csv_sha256": "a31e3440c1847c590eeeb72e32dbc28b912463622d1edba7e708e239919f0fcf"
    },
    "OV-03x": {
      "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv",
      "csv_sha256": "088acb258716352bb141eae080fdc22fc5e4ab52f10ee2ebf2c94ba14538f216"
    },
    "OV-04x": {
      "csv_path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv",
      "csv_sha256": "f6d620fb7da9ec199953bed628dc72a98c74d0baa5bb52e78744ea398a2b8b9b"
    }
  },
  "schema": "OV-XD-03/v2"
}
```

Record fingerprint: `e50a44d369d0ff9c4f56fc6756456df5ceaf9818a2632a6da56167ac551c674d`
