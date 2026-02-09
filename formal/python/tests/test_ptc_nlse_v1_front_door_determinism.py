import json
from pathlib import Path

from formal.python.tools.ptc_nlse_v1_run import (
    build_ptc_nlse_v1_hooks,
    build_ptc_nlse_v1_report,
    input_from_dict,
    load_manifest,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def _load_report(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _build_payload_for_case(case_id: str) -> dict:
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"][case_id])
    raw["case_id"] = case_id
    return build_ptc_nlse_v1_report(inp=input_from_dict(raw))


def test_ptc_nlse_v1_conservative_report_matches_locked_output():
    payload = _build_payload_for_case("conservative_plane_wave")
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_REPORT.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_dissipative_report_matches_locked_output():
    payload = _build_payload_for_case("dissipative_plane_wave")
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_REPORT_DISSIPATIVE.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_soliton_report_matches_locked_output():
    payload = _build_payload_for_case("conservative_bright_soliton")
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_REPORT_SOLITON.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_soliton_dissipative_report_matches_locked_output():
    payload = _build_payload_for_case("dissipative_bright_soliton")
    locked = _load_report(
        REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_REPORT_SOLITON_DISSIPATIVE.json"
    )
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_trap_report_matches_locked_output():
    payload = _build_payload_for_case("conservative_trapped_ground_state")
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_REPORT_TRAP.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_trap_dissipative_report_matches_locked_output():
    payload = _build_payload_for_case("dissipative_trapped_ground_state")
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_REPORT_TRAP_DISSIPATIVE.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_default_case_matches_locked_output():
    manifest = load_manifest(repo_root=REPO_ROOT)
    case = manifest["default_case"]
    payload = _build_payload_for_case(case)

    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_REPORT.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_conservative_hooks_match_locked_output():
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"]["conservative_plane_wave"])
    raw["case_id"] = "conservative_plane_wave"
    payload = build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_HOOKS.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_dissipative_hooks_match_locked_output():
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"]["dissipative_plane_wave"])
    raw["case_id"] = "dissipative_plane_wave"
    payload = build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_HOOKS_DISSIPATIVE.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_soliton_hooks_match_locked_output():
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"]["conservative_bright_soliton"])
    raw["case_id"] = "conservative_bright_soliton"
    payload = build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_HOOKS_SOLITON.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_soliton_dissipative_hooks_match_locked_output():
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"]["dissipative_bright_soliton"])
    raw["case_id"] = "dissipative_bright_soliton"
    payload = build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))
    locked = _load_report(
        REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_HOOKS_SOLITON_DISSIPATIVE.json"
    )
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_trap_hooks_match_locked_output():
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"]["conservative_trapped_ground_state"])
    raw["case_id"] = "conservative_trapped_ground_state"
    payload = build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_HOOKS_TRAP.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_trap_dissipative_hooks_match_locked_output():
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"]["dissipative_trapped_ground_state"])
    raw["case_id"] = "dissipative_trapped_ground_state"
    payload = build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))
    locked = _load_report(REPO_ROOT / "formal" / "output" / "PTC_NLSE_V1_HOOKS_TRAP_DISSIPATIVE.json")
    assert payload["schema"] == locked["schema"]
    assert payload["fingerprint"] == locked["fingerprint"]


def test_ptc_nlse_v1_energy_regimes():
    manifest = load_manifest(repo_root=REPO_ROOT)

    cons = dict(manifest["cases"]["conservative_plane_wave"])
    cons["case_id"] = "conservative_plane_wave"
    cons_payload = build_ptc_nlse_v1_report(inp=input_from_dict(cons))
    assert abs(cons_payload["output"]["energy_delta"]) < 1e-8

    diss = dict(manifest["cases"]["dissipative_plane_wave"])
    diss["case_id"] = "dissipative_plane_wave"
    diss_payload = build_ptc_nlse_v1_report(inp=input_from_dict(diss))
    assert diss_payload["output"]["energy_delta"] < -1e-6
