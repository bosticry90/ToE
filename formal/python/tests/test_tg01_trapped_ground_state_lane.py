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


def test_tg01_pass_conservative_trap_shape_stability_front_door():
    """
    PASS lane: conservative trapped state keeps its pinned shape metrics.
    """
    payload = _build_payload_for_case("conservative_trapped_ground_state")

    assert payload["derived"]["rac_energy_class"] == "conservative"
    assert payload["derived"]["initial_condition"] == "harmonic_ground_state_like"
    assert payload["derived"]["potential"]["kind"] == "harmonic"
    assert payload["output"]["trap_shape_residual"] < 1e-5
    assert payload["output"]["trap_peak_ratio"] > 0.999
    assert abs(payload["output"]["trap_m2_delta"]) < 1e-6


def test_tg01_fail_dissipative_trap_shape_degrades_front_door():
    """
    FAIL lane: damping degrades trapped-state amplitude/shape metrics.
    """
    payload = _build_payload_for_case("dissipative_trapped_ground_state")

    assert payload["derived"]["rac_energy_class"] == "dissipative"
    assert payload["derived"]["initial_condition"] == "harmonic_ground_state_like"
    assert payload["derived"]["potential"]["kind"] == "harmonic"
    assert payload["output"]["trap_shape_residual"] > 5e-2
    assert payload["output"]["trap_peak_ratio"] < 0.9
