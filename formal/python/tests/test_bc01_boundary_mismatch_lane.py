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


def test_bc01_pass_periodic_constant_field_laplacian_zero_front_door_hooks():
    """
    PASS lane: periodic constant-field residual is near zero.
    """
    hooks = _build_hooks_for_case("conservative_plane_wave")
    assert hooks["hooks"]["bc01_periodic_constant_residual"] < 1e-12


def test_bc01_fail_dirichlet_constant_field_laplacian_nonzero_front_door_hooks():
    """
    FAIL lane: Dirichlet constant-field residual is nonzero.
    """
    hooks = _build_hooks_for_case("conservative_plane_wave")
    assert hooks["hooks"]["bc01_dirichlet_constant_residual"] > 0.1


def test_bc01_boundary_residual_periodic_vs_dirichlet_front_door_hooks():
    """
    Boundary mismatch residual on the same PTC initial state is nontrivial.
    """
    hooks = _build_hooks_for_case("conservative_plane_wave")
    assert hooks["hooks"]["bc01_boundary_residual"] > 1e-2
