# OV-DQ-01 — DQ-01_v1 diagnostic record (computed)

Scope / limits
- Diagnostic/bookkeeping record only; no physics claim
- No continuity claim; no averaging across regimes
- β not inferred / β-null posture

Record (computed)

```json
{
  "adequacy_policy": "DQ-01_v1",
  "notes": "Deterministic diagnostic record for DQ-01 curved-fit adequacy and OV robustness summaries. Bookkeeping only; no physics claim; no continuity claim; \u03b2 not inferred / \u03b2-null posture.",
  "ov03x": {
    "curved_adequacy_passes": true,
    "curved_adequacy_summary": {
      "adequacy_aggregation": "all_windows",
      "fail_tags": [],
      "n_fail": 0,
      "n_pass": 4,
      "n_windows": 4
    },
    "curved_windows": [
      {
        "data_fingerprint": "46fa0869d138b29ff073b3c52382bbcc516595ada5e02499e54872453bf65138",
        "dq01": {
          "fingerprint": "4af8b1c33d3306dd73ab74a7b0552e7ddb79659f1dc1c959ed6000404cb77fd2",
          "input_fingerprint": "DR01_Ernst2009_Fig2a_kmax_7p79806_curved|u=0|c0=0.001949857004818731|beta=-1.98688890556482e-17|source_kind=csv|source_ref=Ernst et al. (2009) arXiv:0908.4242v1; Fig2a; C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv; window k<= 7.79806 um^-1; omega=2*pi*f (f in kHz)|fit_method=Fig2a curved omega/k = c0 + beta*k^2 on k<= 7.79806 um^-1; u fixed to 0|data_fingerprint=46fa0869d138b29ff073b3c52382bbcc516595ada5e02499e54872453bf65138|fit_quality_fingerprint=f733a109bd3d63aec52c900ece10b4b07c1b2598214d3ab6f91eae5c7362e5c8",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": -1.9868889055648197e-17,
            "beta_snr": 3.0285887672491483,
            "beta_stderr_s_per_m2": 6.560444676579517e-18,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 0.0002803034033802853,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 16.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 0.00037195139315562424,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 6.560444676579517e-18,
          "c0_stderr_m_per_s": 0.0002803034033802853,
          "n_points": 16,
          "r2_y_space": 0.39583166801536207,
          "rmse_omega_over_k_m_per_s": 0.00037195139315562424
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr01_fit_artifact_curved.json",
        "tag": "DR01_Ernst2009_Fig2a_kmax_7p79806_curved"
      },
      {
        "data_fingerprint": "567f8ce81c4ca99a35e653881db4601985c1c64e55392866b8c19e3ffca82b10",
        "dq01": {
          "fingerprint": "fd294b0a5314d66e5df845ed105038ff3763e99dd17192d4f44ee80314505b2e",
          "input_fingerprint": "DR03_Ernst2009_Fig2a_kmax_7p30071_curved|u=0|c0=0.00201933396850786|beta=-2.260377536744091e-17|source_kind=csv|source_ref=Ernst et al. (2009) arXiv:0908.4242v1; Fig2a; C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv; window k<= 7.30071 um^-1; omega=2*pi*f (f in kHz)|fit_method=Fig2a curved omega/k = c0 + beta*k^2 on k<= 7.30071 um^-1; u fixed to 0|data_fingerprint=567f8ce81c4ca99a35e653881db4601985c1c64e55392866b8c19e3ffca82b10|fit_quality_fingerprint=c61d3dc84459132fc7ef64ed45b5046319f41d9de49180f61da2a3510045884f",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": -2.2603775367440906e-17,
            "beta_snr": 3.0288361496083667,
            "beta_stderr_s_per_m2": 7.462858421827675e-18,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 0.0002853414582203176,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 13.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 0.00033782141435962276,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 7.462858421827675e-18,
          "c0_stderr_m_per_s": 0.0002853414582203176,
          "n_points": 13,
          "r2_y_space": 0.4547396326992118,
          "rmse_omega_over_k_m_per_s": 0.00033782141435962276
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr03_fit_artifact_curved.json",
        "tag": "DR03_Ernst2009_Fig2a_kmax_7p30071_curved"
      },
      {
        "data_fingerprint": "9e4a0ccb356f43b3fc73dcc847a1af2e49553016e5297ba82d87b50c9c0c66c9",
        "dq01": {
          "fingerprint": "c14684f501ed1a9169edddf5b3c73a5b363cd7a46fbd65d8918ed34176302aaf",
          "input_fingerprint": "DR04d_Ernst2009_Fig2a_kmax_5p49635_curved|u=0|c0=0.001259825120151492|beta=1.695746088993177e-17|source_kind=csv|source_ref=Ernst et al. (2009) arXiv:0908.4242v1; Fig2a; C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv; window k<= 5.49635 um^-1; omega=2*pi*f (f in kHz)|fit_method=Fig2a curved omega/k = c0 + beta*k^2 on k<= 5.49635 um^-1; u fixed to 0|data_fingerprint=9e4a0ccb356f43b3fc73dcc847a1af2e49553016e5297ba82d87b50c9c0c66c9|fit_quality_fingerprint=414cef1436fb4205def68e32d535d41d5c7f68a9cab1a841038331f2ae448848",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": 1.6957460889931774e-17,
            "beta_snr": 7.535486160513075,
            "beta_stderr_s_per_m2": 2.2503472939531186e-18,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 4.783315093238544e-05,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 5.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 2.6341626358363123e-05,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 2.2503472939531186e-18,
          "c0_stderr_m_per_s": 4.783315093238544e-05,
          "n_points": 5,
          "r2_y_space": 0.9498189733474756,
          "rmse_omega_over_k_m_per_s": 2.6341626358363123e-05
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr04d_fit_artifact_curved.json",
        "tag": "DR04d_Ernst2009_Fig2a_kmax_5p49635_curved"
      },
      {
        "data_fingerprint": "f134b5209e24ae507b13c1d9685a713e49b09ffaac095cc10630fe1be1b4cf8b",
        "dq01": {
          "fingerprint": "b322e50d2e920ec8d9e90dc8882f59859331c0f20e0353d78d37a5812b0a138b",
          "input_fingerprint": "DR05_Ernst2009_Fig2a_kmax_7p55491_curved|u=0|c0=0.00188837397455494|beta=-1.77445787720965e-17|source_kind=csv|source_ref=Ernst et al. (2009) arXiv:0908.4242v1; Fig2a; C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/omega_k_data.csv; window k<= 7.55491 um^-1; omega=2*pi*f (f in kHz)|fit_method=Fig2a curved omega/k = c0 + beta*k^2 on k<= 7.55491 um^-1; u fixed to 0|data_fingerprint=f134b5209e24ae507b13c1d9685a713e49b09ffaac095cc10630fe1be1b4cf8b|fit_quality_fingerprint=db090da7da988d0b4a6e093ae392ce29765ff8354d9fc1d0b1af128ec818e8a2",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": -1.7744578772096503e-17,
            "beta_snr": 2.5018100551471205,
            "beta_stderr_s_per_m2": 7.092696240303912e-18,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 0.00029250091883449954,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 15.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 0.0003740712179987719,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 7.092696240303912e-18,
          "c0_stderr_m_per_s": 0.00029250091883449954,
          "n_points": 15,
          "r2_y_space": 0.3249927902803823,
          "rmse_omega_over_k_m_per_s": 0.0003740712179987719
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr05_fit_artifact_curved.json",
        "tag": "DR05_Ernst2009_Fig2a_kmax_7p55491_curved"
      }
    ],
    "failure_reasons": [
      "q_ratio_above_threshold"
    ],
    "observable_id": "OV-03x",
    "prefer_curved": false,
    "q_ratio": 1.0241440175459013,
    "q_threshold": 0.9,
    "r_max_curved": 0.6107718647646012,
    "r_max_linear": 0.596373024009025,
    "robustness_failed": true,
    "robustness_report_fingerprint": "78f15afb7ee964f0efb8e43b5525fa3dea2fa8fa10f5c9a6b65f46a7e8cf7c7b"
  },
  "ov04x": {
    "curved_adequacy_passes": true,
    "curved_adequacy_summary": {
      "adequacy_aggregation": "all_windows",
      "fail_tags": [],
      "n_fail": 0,
      "n_pass": 4,
      "n_windows": 4
    },
    "curved_windows": [
      {
        "data_fingerprint": "7ef4974de39290dd4b11b5b1341cd628318d772c2898e2ada21084619aff65aa",
        "dq01": {
          "fingerprint": "fe31716097bcf122f24c02d4e932e398f9394bb51dad3834a1cef489bfcb9233",
          "input_fingerprint": "DR01_DS02_Fig2_filled_circles_kmax_3p33842_2026-01-23_curved|u=0|c0=0.0001055415867360566|beta=-1.635632733254177e-17|source_kind=csv|source_ref=Shammass et al. (2012) arXiv:1207.3440v2; Fig. 2 (filled circles series only); C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv; low-k window k<= 3.33842 um^-1; fit through origin; omega=2*pi*f; date 2026-01-23|fit_method=low-k curved omega/k = c0 + beta*k^2; u fixed to 0|data_fingerprint=7ef4974de39290dd4b11b5b1341cd628318d772c2898e2ada21084619aff65aa|fit_quality_fingerprint=b556219d7010f703e9981a53a5d88fb9ccba077109f91636f08c4a93a7fc6535",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": -1.635632733254177e-17,
            "beta_snr": 0.9167786357161167,
            "beta_stderr_s_per_m2": 1.7841086926906264e-17,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 6.844138988902175e-05,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 21.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 0.00023598918447934728,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 1.7841086926906264e-17,
          "c0_stderr_m_per_s": 6.844138988902175e-05,
          "n_points": 21,
          "r2_y_space": 0.042362026371597805,
          "rmse_omega_over_k_m_per_s": 0.00023598918447934728
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr01_fit_artifact_curved.json",
        "tag": "DR01_DS02_Fig2_filled_circles_kmax_3p33842_2026-01-23_curved"
      },
      {
        "data_fingerprint": "3776b46445dc6fae00f7bbf8186727060135a2c8b78d83405a8f372afd7c2f8a",
        "dq01": {
          "fingerprint": "6fd42868d4b56372fa6a61c042b9aca98d03388db4bc51a66f791506510aadba",
          "input_fingerprint": "DR03_DS02_Fig2_filled_circles_kmax_2p1_2026-01-23_curved|u=0|c0=0.0001393401555668269|beta=-5.507634269137029e-17|source_kind=csv|source_ref=Shammass et al. (2012) arXiv:1207.3440v2; Fig. 2 (filled circles series only); C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv; low-k window k<= 2.1 um^-1; fit through origin; omega=2*pi*f; date 2026-01-23|fit_method=low-k curved omega/k = c0 + beta*k^2; u fixed to 0|data_fingerprint=3776b46445dc6fae00f7bbf8186727060135a2c8b78d83405a8f372afd7c2f8a|fit_quality_fingerprint=9c5ae973c8b0b9239298133496d51a40f35cb6653ecc9ef59f187fc09ea03ed1",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": -5.507634269137029e-17,
            "beta_snr": 1.0026513826741774,
            "beta_stderr_s_per_m2": 5.493070038409148e-17,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 8.737499131242957e-05,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 17.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 0.00025725172295071005,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 5.493070038409148e-17,
          "c0_stderr_m_per_s": 8.737499131242957e-05,
          "n_points": 17,
          "r2_y_space": 0.06281101759625352,
          "rmse_omega_over_k_m_per_s": 0.00025725172295071005
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr03_fit_artifact_curved.json",
        "tag": "DR03_DS02_Fig2_filled_circles_kmax_2p1_2026-01-23_curved"
      },
      {
        "data_fingerprint": "21d5bfba8763eb449a37a724a1f51d5aebd198d390126e9ac12284f6b863c693",
        "dq01": {
          "fingerprint": "d8d8ce54864488b9dda544df24c64f2dfa9814dd70864bc21f3f638b5d6d0f36",
          "input_fingerprint": "DR04d_DS02_Fig2_filled_circles_kmax_1p167515_2026-01-23_curved|u=0|c0=0.0001984681144332602|beta=-2.101044879531753e-16|source_kind=csv|source_ref=Shammass et al. (2012) arXiv:1207.3440v2; Fig. 2 (filled circles series only); C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv; low-k window k<= 1.16752 um^-1; fit through origin; omega=2*pi*f; date 2026-01-23|fit_method=low-k curved omega/k = c0 + beta*k^2; u fixed to 0|data_fingerprint=21d5bfba8763eb449a37a724a1f51d5aebd198d390126e9ac12284f6b863c693|fit_quality_fingerprint=d4da809436db984090517ee9448b68ad80ca346200652e7de04d89cb61aa0683",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": -2.1010448795317526e-16,
            "beta_snr": 1.104877672048607,
            "beta_stderr_s_per_m2": 1.9016085967563303e-16,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 0.00011911266029229273,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 13.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 0.0002842407389466028,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 1.9016085967563303e-16,
          "c0_stderr_m_per_s": 0.00011911266029229273,
          "n_points": 13,
          "r2_y_space": 0.09989192182780438,
          "rmse_omega_over_k_m_per_s": 0.0002842407389466028
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr04d_fit_artifact_curved.json",
        "tag": "DR04d_DS02_Fig2_filled_circles_kmax_1p167515_2026-01-23_curved"
      },
      {
        "data_fingerprint": "c7726c8611ae01fbf38aeef1f2e79cb518bc4f02e15ad86188ab552fefbe65ee",
        "dq01": {
          "fingerprint": "9e2e25d2d440f6ceb837366cab3424423753d37c35c9ad22cf73a1d091ac49cc",
          "input_fingerprint": "DR05_DS02_Fig2_filled_circles_kmax_1p8_2026-01-23_curved|u=0|c0=0.0001645198947227385|beta=-1.053237337619835e-16|source_kind=csv|source_ref=Shammass et al. (2012) arXiv:1207.3440v2; Fig. 2 (filled circles series only); C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv; low-k window k<= 1.8 um^-1; fit through origin; omega=2*pi*f; date 2026-01-23|fit_method=low-k curved omega/k = c0 + beta*k^2; u fixed to 0|data_fingerprint=c7726c8611ae01fbf38aeef1f2e79cb518bc4f02e15ad86188ab552fefbe65ee|fit_quality_fingerprint=4500b5fbec0cf6efbb431b7190286a8cc6e334c64ef61b24e4c727b2bee9297a",
          "metrics": {
            "beta_identifiable": 1.0,
            "beta_s_per_m2": -1.0532373376198347e-16,
            "beta_snr": 1.0552474227680695,
            "beta_stderr_s_per_m2": 9.980951527529325e-17,
            "beta_stderr_small_max_s_per_m2": 2e-16,
            "beta_used_for_inference": 1.0,
            "c0_stderr_m_per_s": 0.00010095833559187205,
            "c0_stderr_max_m_per_s": 0.0003,
            "c0_stderr_max_m_per_s_strict_4pt": 0.00028,
            "n_points": 15.0,
            "n_points_min": 5.0,
            "policy": 0.0,
            "policy_variantA": 0.0,
            "rmse_omega_over_k_m_per_s": 0.00026987782153530476,
            "rmse_omega_over_k_max_m_per_s": 0.0004,
            "rmse_omega_over_k_max_m_per_s_strict_4pt": 0.00025,
            "snr_beta_min": 2.0
          },
          "passes": true,
          "reason_codes": []
        },
        "fit_quality": {
          "beta_stderr_s_per_m2": 9.980951527529325e-17,
          "c0_stderr_m_per_s": 0.00010095833559187205,
          "n_points": 15,
          "r2_y_space": 0.07889916783737261,
          "rmse_omega_over_k_m_per_s": 0.00026987782153530476
        },
        "path": "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr05_fit_artifact_curved.json",
        "tag": "DR05_DS02_Fig2_filled_circles_kmax_1p8_2026-01-23_curved"
      }
    ],
    "failure_reasons": [],
    "observable_id": "OV-04x",
    "prefer_curved": true,
    "q_ratio": 0.8060220497327952,
    "q_threshold": 0.9,
    "r_max_curved": 0.7172088910074628,
    "r_max_linear": 0.8898129911523203,
    "robustness_failed": false,
    "robustness_report_fingerprint": "f562944bc70ff2f892d571cb70627aa2e749dc6ef18dd031358eb17e54930915"
  },
  "provenance": {
    "curved_artifacts": {
      "ov03x": [
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr01_fit_artifact_curved.json",
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr03_fit_artifact_curved.json",
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr04d_fit_artifact_curved.json",
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_b1_second_dataset_TBD/dr05_fit_artifact_curved.json"
      ],
      "ov04x": [
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr01_fit_artifact_curved.json",
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr03_fit_artifact_curved.json",
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr04d_fit_artifact_curved.json",
        "C:/Users/psboy/Documents/ToE/formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/dr05_fit_artifact_curved.json"
      ]
    },
    "robustness_locks": {
      "ov03x": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
      "ov04x": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md"
    }
  },
  "schema": "OV-DQ-01/v1"
}
```

Record fingerprint: `7ff0df17887f779e5f4498e29e63e386e6be822fc9614f7281cd9ca744b16b42`
