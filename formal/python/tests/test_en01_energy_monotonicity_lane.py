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


def test_en01_pass_conservative_energy_is_invariant_from_front_door():
    """
    PASS lane: conservative regime preserves energy under the pinned PTC surface.
    """
    payload = _build_payload_for_case("conservative_plane_wave")

    assert payload["derived"]["rac_energy_class"] == "conservative"
    assert abs(payload["output"]["energy_delta"]) < 1e-8


def test_en01_fail_dissipative_energy_decreases_from_front_door():
    """
    FAIL lane: dissipative regime deterministically decreases energy.
    """
    payload = _build_payload_for_case("dissipative_plane_wave")

    assert payload["derived"]["rac_energy_class"] == "dissipative"
    assert payload["output"]["energy_delta"] < -1e-6
