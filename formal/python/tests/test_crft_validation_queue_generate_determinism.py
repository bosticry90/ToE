from __future__ import annotations

import json

from formal.python.tools.crft_validation_queue_generate import build_queue_payload


def test_crft_validation_queue_is_deterministic() -> None:
    claims_payload = {
        "schema_version": 1,
        "claims": [
            {"id": "CLM-0001", "section": "C6 — Demo", "kind": "equation", "text": "phi_t = i ..."},
            {"id": "CLM-0002", "section": "C7 — Demo", "kind": "equation", "text": "c_s2 = g_eff rho"},
        ],
        "validation_shortlist": [
            {
                "claim_id": "CLM-0001",
                "target_surface": "formal/python/crft/cp_nlse_2d.py",
                "plan": ["do A", "do B"],
                "exit_condition": "ok",
            },
            {
                "claim_id": "CLM-0002",
                "target_surface": "formal/python/crft/acoustic_metric.py",
                "plan": ["do C"],
                "exit_condition": "ok",
            },
        ],
    }

    q1 = build_queue_payload(claims_payload, source_path="formal/quarantine/claims/x.json", source_sha256="abc", max_items=3)
    q2 = build_queue_payload(claims_payload, source_path="formal/quarantine/claims/x.json", source_sha256="abc", max_items=3)

    assert json.dumps(q1, sort_keys=True) == json.dumps(q2, sort_keys=True)
    assert q1["items"][0]["claim_id"] == "CLM-0001"
    assert q1["source"]["path"] == "formal/quarantine/claims/x.json"

    # Evidence links are deterministic static strings.
    ev1 = q1["items"][0]["evidence"]
    assert q1["items"][0]["claim_family"] == "C6_CP_NLSE_2D"
    assert q1["items"][0]["evidence_strength"] == "bounded_multi"
    assert ev1["canonical_surface_refs"] == ["CP-NLSE-2D"]
    assert ev1["pytest_nodes"] == [
        "formal/python/crft/tests/test_c6_cp_nlse_2d_norm_drift.py::test_c6_cp_nlse_2d_norm_drift_is_small_for_plane_wave",
        "formal/python/crft/tests/test_c6_cp_nlse_2d_dispersion_eigenfunction.py::test_c6_cp_nlse_2d_plane_wave_is_rhs_eigenfunction_when_linear",
    ]

    ev2 = q1["items"][1]["evidence"]
    assert q1["items"][1]["claim_family"] == "C7_MT_01A"
    assert q1["items"][1]["evidence_strength"] == "bounded_multi"
    assert ev2["canonical_surface_refs"] == ["MT-01a"]
    assert "formal/python/tests/test_mt01_acoustic_metric_lock.py::test_mt01_acoustic_metric_1d_lock_identities" in ev2[
        "pytest_nodes"
    ]
