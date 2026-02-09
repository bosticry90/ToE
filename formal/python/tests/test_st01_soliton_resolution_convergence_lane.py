from pathlib import Path

from formal.python.tools.ptc_nlse_v1_run import (
    build_ptc_nlse_v1_report,
    input_from_dict,
    load_manifest,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def _build_payload_for_case(case_id: str) -> dict:
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"][case_id])
    raw["case_id"] = case_id
    return build_ptc_nlse_v1_report(inp=input_from_dict(raw))


def test_st01_soliton_resolution_convergence_n64_to_n128_front_door():
    """
    Resolution lane: shape metrics should not degrade when refining n64 -> n128.
    """
    n64 = _build_payload_for_case("conservative_bright_soliton_n64")
    n128 = _build_payload_for_case("conservative_bright_soliton_n128")

    assert n64["derived"]["initial_condition"] == "sech_soliton"
    assert n128["derived"]["initial_condition"] == "sech_soliton"

    residual64 = n64["output"]["shape_residual"]
    residual128 = n128["output"]["shape_residual"]
    assert residual64 < 5e-4
    assert residual128 < 5e-4
    assert residual128 <= residual64 + 1e-8

    ratio_err64 = abs(1.0 - n64["output"]["shape_peak_ratio"])
    ratio_err128 = abs(1.0 - n128["output"]["shape_peak_ratio"])
    assert ratio_err128 <= ratio_err64 + 1e-6
