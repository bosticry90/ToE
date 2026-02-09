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


def test_ct01_front_door_conservative_dispersion_matches_contract():
    """
    PASS lane: conservative case matches the pinned dispersion contract.
    """
    payload = _build_payload_for_case("conservative_plane_wave")

    assert payload["derived"]["rac_energy_class"] == "conservative"
    assert abs(payload["output"]["omega_error"]) < 1e-10


def test_ct01_front_door_dissipative_breaks_conservative_dispersion_identity():
    """
    FAIL lane: dissipative damping breaks the conservative dispersion identity.
    """
    payload = _build_payload_for_case("dissipative_plane_wave")

    assert payload["derived"]["rac_energy_class"] == "dissipative"
    assert abs(payload["output"]["omega_error"]) > 1e-4


def test_ct01_front_door_k_scaling_matches_formula():
    """
    Conservative k-scan sanity check on front-door cases.
    """
    k1 = _build_payload_for_case("conservative_plane_wave_k1")
    k3 = _build_payload_for_case("conservative_plane_wave_k3")

    delta_expected = k3["output"]["omega_expected"] - k1["output"]["omega_expected"]
    delta_hat = k3["output"]["omega_hat"] - k1["output"]["omega_hat"]

    assert abs(delta_expected - 4.0) < 1e-12
    assert abs(delta_hat - delta_expected) < 1e-8
