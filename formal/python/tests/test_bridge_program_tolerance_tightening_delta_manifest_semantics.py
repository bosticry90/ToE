from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_program_tolerance_tightening_delta_manifest_generate import (
    build_bridge_program_tolerance_tightening_delta_manifest,
)


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_bridge_program_tolerance_tightening_delta_manifest_v5_t1_closure() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    payload = build_bridge_program_tolerance_tightening_delta_manifest(repo_root=repo_root)

    control = dict(payload.get("expected_break_controls", {}).get("v5_t1_closure_expected", {}))
    recommended = dict(control.get("recommended_next_target", {}))

    assert bool(control.get("passes")) is True
    assert int(control.get("n_mismatch", 0)) == 0
    assert dict(control.get("reason_code_counts", {})) == {}
    assert recommended.get("reason_code") == "none"
    assert recommended.get("suggested_design_ticket") == "BRIDGE_TICKET_PROGRAM_COMPLETE"


def test_bridge_program_tolerance_tightening_delta_manifest_v5_t2_expected_break() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    payload = build_bridge_program_tolerance_tightening_delta_manifest(repo_root=repo_root)

    control = dict(payload.get("expected_break_controls", {}).get("v5_t2_expected_break", {}))
    assert bool(control.get("passes")) is False
    assert int(control.get("n_formerly_pass_probes_flipped", 0)) == 0
    assert control.get("pinned_probe_id") == "baseline_all_pass"
    assert control.get("baseline_signature") == "P-P-P"
    assert control.get("v5_t2_signature") == "P-P-P"

    v5_t2 = dict(payload.get("profiles", {}).get("v5_t2", {}))
    recommended = dict(v5_t2.get("recommended_next_target", {}))
    assert int(v5_t2.get("n_mismatch", 0)) == 0
    assert dict(v5_t2.get("reason_code_counts", {})) == {}
    assert recommended.get("reason_code") == "none"
