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


def test_st01_pass_conservative_soliton_shape_preserved_front_door():
    """
    PASS lane: conservative soliton shape remains stable under the pinned PTC surface.
    """
    payload = _build_payload_for_case("conservative_bright_soliton")

    assert payload["derived"]["rac_energy_class"] == "conservative"
    assert payload["derived"]["initial_condition"] == "sech_soliton"
    assert payload["output"]["shape_residual"] < 1e-3
    assert payload["output"]["shape_peak_ratio"] > 0.99


def test_st01_fail_dissipative_soliton_shape_breaks_front_door():
    """
    FAIL lane: dissipative soliton shape decays under the pinned PTC surface.
    """
    payload = _build_payload_for_case("dissipative_bright_soliton")

    assert payload["derived"]["rac_energy_class"] == "dissipative"
    assert payload["derived"]["initial_condition"] == "sech_soliton"
    assert payload["output"]["shape_residual"] > 5e-2
    assert payload["output"]["shape_peak_ratio"] < 0.95
