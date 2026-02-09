# OV-SND-01N2 — Propagation series split (computed)

Scope / limits
- Bookkeeping only; no physics claim
- Deterministic: remains blocked unless the pinned split rule produces two series with sufficient support

Record (computed)

```json
{
  "dataset": {
    "columns": [
      {
        "dtype": "float",
        "name": "time_ms",
        "unit": "ms"
      },
      {
        "dtype": "float",
        "name": "distance_um",
        "unit": "um"
      }
    ],
    "metadata_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares_series_split.metadata.json",
    "seriesA": {
      "csv_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares_seriesA.csv",
      "csv_sha256": "04364e769e94afd9e5906e683d671fb28c62516dfe2fefc5f2ff75f2920bb9a8",
      "label": "seriesA",
      "row_count": 13,
      "rows_preview": [
        {
          "distance_um": 59.157979,
          "time_ms": 8.914805
        },
        {
          "distance_um": 119.847634,
          "time_ms": 9.072752
        },
        {
          "distance_um": 104.330393,
          "time_ms": 11.520926
        },
        {
          "distance_um": 59.278268,
          "time_ms": 15.730389
        },
        {
          "distance_um": 89.502807,
          "time_ms": 16.3383
        },
        {
          "distance_um": 119.847634,
          "time_ms": 17.04906
        }
      ],
      "slope_fit": {
        "c_um_per_ms": 3.398985770236733,
        "dof": 12.0,
        "n": 13.0,
        "residual_rms_um": 45.67414053744355,
        "se_um_per_ms": 0.48386346164086375
      }
    },
    "seriesB": {
      "csv_relpath": "formal/external_evidence/bec_sound_andrews_1997/ovsnd01_digitization/distance_vs_time_squares_seriesB.csv",
      "csv_sha256": "9b8f88b829d5c3bcf1afbac48fc5a4c97c7327ab7cc6da3449ea0dd94d1127a6",
      "label": "seriesB",
      "row_count": 9,
      "rows_preview": [
        {
          "distance_um": 74.330393,
          "time_ms": 48.006612
        },
        {
          "distance_um": 134.675221,
          "time_ms": 50.375812
        },
        {
          "distance_um": 89.502807,
          "time_ms": 52.192199
        },
        {
          "distance_um": 59.157979,
          "time_ms": 58.1152
        },
        {
          "distance_um": 89.502807,
          "time_ms": 58.510067
        },
        {
          "distance_um": 89.623095,
          "time_ms": 63.43029
        }
      ],
      "slope_fit": {
        "c_um_per_ms": 1.5383520404498612,
        "dof": 8.0,
        "n": 9.0,
        "residual_rms_um": 29.343685021301575,
        "se_um_per_ms": 0.16981440395960395
      }
    },
    "split_rule": {
      "gap_index": 12,
      "largest_gap_ms": 8.268325719139568,
      "min_largest_gap_ms": 6.0,
      "min_points_per_series": 6,
      "rule_id": "largest_x_gap_v1"
    }
  },
  "date": "2026-01-24",
  "digitization_id": "OV-SND-01N2",
  "fingerprint": "f240dd5a72a73606ba3eceff50dd0b1e278143e5c960dc50d8c51082ff249fa5",
  "observable_id": "OV-SND-01N2",
  "schema": "OV-SND-01N2_sound_propagation_distance_time_digitized/v2",
  "scope_limits": [
    "bookkeeping_only",
    "no_physics_claim",
    "no_manual_clicking",
    "no_fitting",
    "non_decisive_by_design"
  ],
  "source": {
    "arxiv_pdf_relpath": "formal/external_evidence/bec_sound_andrews_1997/9711224v1.pdf",
    "arxiv_pdf_sha256": "d38a5d54cca6b4b7a4a71647c20d24bf72b434eca2e1ed943df62f981f3a7cc6",
    "citation": "Kavoulakis & Pethick (1997), arXiv:9711224v1 \u2014 Sound Propagation in Elongated Bose-Einstein Condensed Clouds",
    "extraction": {
      "hardcoded_crop_box": {
        "x0": 1121,
        "x1": 2440,
        "y0": 1143,
        "y1": 1762
      },
      "hardcoded_plot_box": {
        "bottom": 591,
        "left": 88,
        "right": 1101,
        "top": 11
      },
      "image_relpath": "formal/external_evidence/bec_sound_andrews_1997/page4_z4.png",
      "marker_signature": {
        "area": 43,
        "h": 11,
        "w": 12
      },
      "morphology": {
        "binary_opening": {
          "iterations": 1,
          "structure": [
            2,
            2
          ]
        }
      },
      "row_count": 22,
      "split": {
        "gap_index": 12,
        "largest_gap_ms": 8.268325719139568,
        "min_largest_gap_ms": 6.0,
        "rule_id": "largest_x_gap_v1",
        "seriesA_count": 13,
        "seriesB_count": 9
      },
      "threshold": {
        "dark_lt": 140
      }
    },
    "figure_png_relpath": "formal/external_evidence/bec_sound_andrews_1997/page4_z4.png",
    "figure_png_sha256": "0adb09bbc96a4c0338c60299285a83905e37a2a566cbd82c40d2ff38733ad105"
  },
  "status": {
    "blocked": false,
    "blockers": []
  }
}
```

Record fingerprint: `f240dd5a72a73606ba3eceff50dd0b1e278143e5c960dc50d8c51082ff249fa5`
