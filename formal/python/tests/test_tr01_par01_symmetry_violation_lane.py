from pathlib import Path

from formal.python.tools.ptc_nlse_v1_run import (
    build_ptc_nlse_v1_hooks,
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


def _build_hooks_for_case(case_id: str) -> dict:
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"][case_id])
    raw["case_id"] = case_id
    return build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))


def test_par01_pass_laplacian_parity_invariance():
    """
    PASS lane: parity residual is near zero on the PTC evolution surface.
    """
    hooks = _build_hooks_for_case("conservative_plane_wave")
    assert hooks["hooks"]["par01_parity_residual"] < 1e-12


def test_par01_fail_advection_parity_invariance():
    """
    FAIL lane: advection derivative residual breaks parity.
    """
    hooks = _build_hooks_for_case("conservative_plane_wave")
    assert hooks["hooks"]["par01_advection_break_residual"] > 1e-4


def test_tr01_pass_conservative_time_reversal_from_front_door():
    """
    PASS lane: conservative regime has near-zero TR residual.
    """
    payload = _build_payload_for_case("conservative_plane_wave")

    assert payload["derived"]["rac_energy_class"] == "conservative"
    assert abs(payload["output"]["time_reversal_error"]) < 1e-12


def test_tr01_fail_dissipative_breaks_time_reversal_from_front_door():
    """
    FAIL lane: dissipative regime has a nontrivial TR residual.
    """
    payload = _build_payload_for_case("dissipative_plane_wave")

    assert payload["derived"]["rac_energy_class"] == "dissipative"
    assert payload["output"]["time_reversal_error"] > 5e-5
