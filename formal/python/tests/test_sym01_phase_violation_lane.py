from pathlib import Path

from formal.python.tools.ptc_nlse_v1_run import (
    build_ptc_nlse_v1_hooks,
    input_from_dict,
    load_manifest,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def _build_hooks_for_case(case_id: str) -> dict:
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"][case_id])
    raw["case_id"] = case_id
    return build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))


def test_sym01_phase_invariance_pass_cubic_front_door_hooks():
    """
    PASS lane: phase residual is near zero on the PTC cubic evolution surface.
    """
    payload = _build_hooks_for_case("conservative_plane_wave")

    assert payload["hooks"]["sym01_phase_residual"] < 1e-12


def test_sym01_phase_invariance_fail_conjugation_front_door_hooks():
    """
    FAIL lane: conjugation residual is nonzero under phase rotation.
    """
    payload = _build_hooks_for_case("conservative_plane_wave")

    assert payload["hooks"]["sym01_conjugation_residual"] > 1e-3
