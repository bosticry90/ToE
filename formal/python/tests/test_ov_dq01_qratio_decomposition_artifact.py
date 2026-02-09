from __future__ import annotations

import json

from formal.python.toe.observables.ovdq01_qratio_decomposition_record import (
    default_artifact_path,
    ovdq01_qratio_decomposition_record,
)


def _max_pairwise_r(pairs: list[dict]) -> float:
    return float(max(float(p["r"]) for p in pairs))


def _max_window_contrib(contribs: list[dict]) -> float:
    return float(max(float(c["max_pairwise_r"]) for c in contribs))


def test_ov_dq01_qratio_decomposition_artifact_matches_computed() -> None:
    p = default_artifact_path()
    assert p.exists(), f"Missing canonical artifact: {p.as_posix()}"

    on_disk = json.loads(p.read_text(encoding="utf-8"))
    computed = ovdq01_qratio_decomposition_record().to_jsonable()

    assert on_disk["schema"] == "OV-DQ-01_qratio_decomposition/v1"
    assert isinstance(on_disk.get("fingerprint"), str)
    assert on_disk == computed


def test_ov_dq01_qratio_decomposition_invariants_hold() -> None:
    rec = ovdq01_qratio_decomposition_record().to_jsonable()

    for key in ("ov04x", "ov03x"):
        obs = rec[key]

        # Basic shape
        assert obs["observable_id"] in {"OV-04x", "OV-03x"}
        assert isinstance(obs["linear"]["windows"], list) and len(obs["linear"]["windows"]) >= 2
        assert isinstance(obs["curved"]["windows"], list) and len(obs["curved"]["windows"]) >= 2

        # Pairwise decomposition consistency
        lin_pairs = obs["linear"]["decomposition"]["pairwise_r"]
        curv_pairs = obs["curved"]["decomposition"]["pairwise_r"]
        assert len(lin_pairs) >= 1
        assert len(curv_pairs) >= 1

        lin_rmax = _max_pairwise_r(lin_pairs)
        curv_rmax = _max_pairwise_r(curv_pairs)
        assert abs(lin_rmax - float(obs["r_max_linear_recomputed"])) <= 1e-12
        assert abs(curv_rmax - float(obs["r_max_curved_recomputed"])) <= 1e-12

        # Window contributions: max contribution equals r_max.
        lin_contribs = obs["linear"]["decomposition"]["window_contributions"]
        curv_contribs = obs["curved"]["decomposition"]["window_contributions"]
        assert abs(_max_window_contrib(lin_contribs) - lin_rmax) <= 1e-12
        assert abs(_max_window_contrib(curv_contribs) - curv_rmax) <= 1e-12

        # Shares sum to ~1.0 when sum is nonzero.
        s_lin = float(sum(float(c["share_of_sum_max_pairwise_r"]) for c in lin_contribs))
        s_curv = float(sum(float(c["share_of_sum_max_pairwise_r"]) for c in curv_contribs))
        if float(obs["linear"]["decomposition"]["sum_window_max_pairwise_r"]) != 0.0:
            assert abs(s_lin - 1.0) <= 1e-12
        if float(obs["curved"]["decomposition"]["sum_window_max_pairwise_r"]) != 0.0:
            assert abs(s_curv - 1.0) <= 1e-12

        # q_ratio recomputation matches locked q_ratio (within tolerance).
        assert abs(float(obs["q_ratio_recomputed"]) - float(obs["robustness_q_ratio_locked"])) <= 1e-12
