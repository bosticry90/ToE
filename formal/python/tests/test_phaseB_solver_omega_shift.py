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


def test_omega_shift_front_door_amplitude_shift_matches_prediction():
    """
    PASS lane: omega shift follows g*(|A2|^2 - |A1|^2) on conservative cases.
    """
    base = _build_payload_for_case("conservative_plane_wave")
    amp_up = _build_payload_for_case("conservative_plane_wave_amp_up")

    a0_sq = float(base["inputs"]["A_re"]) ** 2 + float(base["inputs"]["A_im"]) ** 2
    a1_sq = float(amp_up["inputs"]["A_re"]) ** 2 + float(amp_up["inputs"]["A_im"]) ** 2
    g = float(base["inputs"]["g"])
    expected_shift = g * (a1_sq - a0_sq)

    delta_expected = amp_up["output"]["omega_expected"] - base["output"]["omega_expected"]
    delta_hat = amp_up["output"]["omega_hat"] - base["output"]["omega_hat"]

    assert abs(delta_expected - expected_shift) < 1e-12
    assert abs(delta_hat - expected_shift) < 1e-8


def test_omega_shift_front_door_coupling_shift_matches_prediction():
    """
    PASS lane: omega shift follows (g2 - g1)*|A|^2 on conservative cases.
    """
    base = _build_payload_for_case("conservative_plane_wave")
    g_up = _build_payload_for_case("conservative_plane_wave_g_up")

    a_sq = float(base["inputs"]["A_re"]) ** 2 + float(base["inputs"]["A_im"]) ** 2
    expected_shift = (float(g_up["inputs"]["g"]) - float(base["inputs"]["g"])) * a_sq

    delta_expected = g_up["output"]["omega_expected"] - base["output"]["omega_expected"]
    delta_hat = g_up["output"]["omega_hat"] - base["output"]["omega_hat"]

    assert abs(delta_expected - expected_shift) < 1e-12
    assert abs(delta_hat - expected_shift) < 1e-8


def test_omega_shift_dissipative_case_violates_conservative_prediction():
    """
    FAIL lane: dissipative case does not satisfy the conservative omega identity.
    """
    diss = _build_payload_for_case("dissipative_plane_wave")

    assert diss["derived"]["rac_energy_class"] == "dissipative"
    assert abs(diss["output"]["omega_error"]) > 1e-4
