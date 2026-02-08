import json
from pathlib import Path

from formal.python.tools.ptc_nlse_v1_run import load_manifest


REPO_ROOT = Path(__file__).resolve().parents[3]

REPORT_SCHEMA = "PTC/NLSE_v1_report/v1"
HOOKS_SCHEMA = "PTC/NLSE_v1_hooks/v1"
MANIFEST_SCHEMA = "PTC/NLSE_v1_manifest/v1"

REPORT_TOP_LEVEL_KEYS = {
    "schema",
    "inputs",
    "input_fingerprint",
    "derived",
    "output",
    "determinism",
    "fingerprint",
}
HOOKS_TOP_LEVEL_KEYS = {
    "schema",
    "inputs",
    "input_fingerprint",
    "hooks",
    "determinism",
    "fingerprint",
}
DERIVED_BASE_KEYS = {"grid", "kgrid_sample", "rac_energy_class"}
OUTPUT_CORE_KEYS = {
    "omega_hat",
    "omega_expected",
    "omega_error",
    "energy_trace",
    "norm_trace",
    "energy_delta",
    "norm_delta",
    "phase_invariance_error",
    "time_reversal_error",
    "t_end",
}
HOOK_KEYS = {
    "sym01_phase_residual",
    "sym01_conjugation_residual",
    "par01_parity_residual",
    "par01_advection_break_residual",
    "bc01_boundary_residual",
    "bc01_periodic_constant_residual",
    "bc01_dirichlet_constant_residual",
}
TRAP_INPUT_KEYS = {"V_kind", "V_trap_omega", "V_center"}
REQUIRED_CASE_IDS = {
    "conservative_plane_wave",
    "dissipative_plane_wave",
    "conservative_bright_soliton",
    "dissipative_bright_soliton",
    "conservative_bright_soliton_n64",
    "conservative_bright_soliton_n128",
    "conservative_trapped_ground_state",
    "dissipative_trapped_ground_state",
}


def _load_json(relpath: str) -> dict:
    path = REPO_ROOT / relpath
    return json.loads(path.read_text(encoding="utf-8"))


def test_ptc_nlse_v1_manifest_required_cases_frozen():
    manifest = load_manifest(repo_root=REPO_ROOT)
    assert manifest["schema"] == MANIFEST_SCHEMA
    cases = set(manifest["cases"].keys())
    assert REQUIRED_CASE_IDS.issubset(cases)


def test_ptc_nlse_v1_report_top_level_keys_frozen():
    for rel in [
        "formal/output/PTC_NLSE_V1_REPORT.json",
        "formal/output/PTC_NLSE_V1_REPORT_DISSIPATIVE.json",
        "formal/output/PTC_NLSE_V1_REPORT_SOLITON.json",
        "formal/output/PTC_NLSE_V1_REPORT_SOLITON_DISSIPATIVE.json",
        "formal/output/PTC_NLSE_V1_REPORT_TRAP.json",
        "formal/output/PTC_NLSE_V1_REPORT_TRAP_DISSIPATIVE.json",
    ]:
        payload = _load_json(rel)
        assert payload["schema"] == REPORT_SCHEMA
        assert set(payload.keys()) == REPORT_TOP_LEVEL_KEYS


def test_ptc_nlse_v1_hooks_top_level_and_hook_keys_frozen():
    for rel in [
        "formal/output/PTC_NLSE_V1_HOOKS.json",
        "formal/output/PTC_NLSE_V1_HOOKS_DISSIPATIVE.json",
        "formal/output/PTC_NLSE_V1_HOOKS_SOLITON.json",
        "formal/output/PTC_NLSE_V1_HOOKS_SOLITON_DISSIPATIVE.json",
        "formal/output/PTC_NLSE_V1_HOOKS_TRAP.json",
        "formal/output/PTC_NLSE_V1_HOOKS_TRAP_DISSIPATIVE.json",
    ]:
        payload = _load_json(rel)
        assert payload["schema"] == HOOKS_SCHEMA
        assert set(payload.keys()) == HOOKS_TOP_LEVEL_KEYS
        assert set(payload["hooks"].keys()) == HOOK_KEYS


def test_ptc_nlse_v1_plane_wave_surface_keys_frozen():
    payload = _load_json("formal/output/PTC_NLSE_V1_REPORT.json")
    assert set(payload["derived"].keys()) == DERIVED_BASE_KEYS
    assert set(payload["output"].keys()) == OUTPUT_CORE_KEYS
    assert TRAP_INPUT_KEYS.isdisjoint(set(payload["inputs"].keys()))


def test_ptc_nlse_v1_soliton_surface_keys_frozen():
    payload = _load_json("formal/output/PTC_NLSE_V1_REPORT_SOLITON.json")
    assert set(payload["derived"].keys()) == DERIVED_BASE_KEYS | {"initial_condition"}
    assert set(payload["output"].keys()) == OUTPUT_CORE_KEYS | {
        "shape_residual",
        "shape_peak_delta",
        "shape_peak_ratio",
    }
    assert TRAP_INPUT_KEYS.isdisjoint(set(payload["inputs"].keys()))


def test_ptc_nlse_v1_trap_surface_keys_frozen():
    payload = _load_json("formal/output/PTC_NLSE_V1_REPORT_TRAP.json")
    assert set(payload["derived"].keys()) == DERIVED_BASE_KEYS | {"initial_condition", "potential"}
    assert set(payload["output"].keys()) == OUTPUT_CORE_KEYS | {
        "trap_shape_residual",
        "trap_peak_ratio",
        "trap_m2_delta",
    }
    assert TRAP_INPUT_KEYS.issubset(set(payload["inputs"].keys()))
