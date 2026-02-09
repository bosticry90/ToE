from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from formal.python.tools.bridge_program_orthogonality_mismatch_report_generate import (
    build_bridge_program_orthogonality_mismatch_report,
)
from formal.python.tools.bridge_program_orthogonality_report_generate import (
    build_bridge_program_orthogonality_report,
)
from formal.python.tools.bridge_toyh_c6_current_anchor import evaluate_toyh_c6_current_anchor
from formal.python.tools.bridge_toyh_c6_phase_anchor import evaluate_toyh_c6_phase_anchor


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_bridge_program_v5_t2_phase_stabilized_restores_repro_capsule() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    capsule_path = repo_root / "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_T2_REPRO_CAPSULE.json"
    capsule = json.loads(capsule_path.read_text(encoding="utf-8"))
    target_probe_ids = [str(it.get("probe_id")) for it in capsule.get("minimal_reproduction_probes", [])]

    report = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile="v5_t2")
    by_probe = {str(it.get("probe_id")): it for it in report.get("items", [])}

    for probe_id in target_probe_ids:
        item = by_probe[probe_id]
        assert item["signature"] == "P-P-P"
        assert item["toyh_phase_bridge"]["pass"] is True
        assert item["toyh_phase"]["reason_code"] in {"PASS", "FAIL_PHASE_CHANNEL_CONTROL_MIN"}
        assert item["toyh_phase_anchor"]["reason_code"] == "PASS_PHASE_ANCHOR"
        assert item["toyhg_pair_bridge"]["pass"] is True
        assert item["toyhg_pair_bridge"]["reason_code"] == "PASS_PAIR_COMPATIBLE"


def test_bridge_program_v5_t2_frontier_lock_after_l1() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile="v5_t2")
    mismatch = build_bridge_program_orthogonality_mismatch_report(repo_root=repo_root, tolerance_profile="v5_t2")

    assert report.get("summary", {}).get("n_probes") == 17
    mismatch_summary = dict(mismatch.get("summary", {}))
    reason_counts = dict(mismatch_summary.get("reason_code_counts", {}))
    assert int(mismatch_summary.get("n_mismatch", 0)) == 0
    assert reason_counts == {}
    assert ("none" if not reason_counts else "not_none") == "none"


def test_bridge_program_v5_t2_negative_controls_preserved_phase_wrong_sign() -> None:
    for theta in [float(np.pi / 6.0), float(np.pi / 2.0), float(2.0 * np.pi / 3.0)]:
        report = evaluate_toyh_c6_phase_anchor(
            theta=float(theta),
            grid_n=11,
            amplitude_scale=1.0,
            tol_invariance=1e-15,
            tol_phase_anchor=2e-8,
            min_anchor_magnitude=1e-8,
            anchor_sign=-1.0,
            use_stable_invariance=True,
        )
        assert report["status"]["admissible"] is False
        assert report["reason_code"] == "FAIL_ANCHOR_PHASE_MISMATCH"


def test_bridge_program_v5_t2_negative_controls_preserved_grid_amplitude_scale() -> None:
    for grid_n in [13, 15]:
        phase_report = evaluate_toyh_c6_phase_anchor(
            theta=float(np.pi / 3.0),
            grid_n=int(grid_n),
            amplitude_scale=1.1,
            tol_invariance=1e-15,
            tol_phase_anchor=2e-8,
            min_anchor_magnitude=1e-8,
            anchor_sign=1.0,
            use_stable_invariance=True,
        )
        current_report = evaluate_toyh_c6_current_anchor(
            theta=float(np.pi / 3.0),
            grid_n=int(grid_n),
            amplitude_scale=1.1,
            local_phase_shear_alpha=0.5,
            tol_invariance=1e-15,
            tol_current_anchor=2e-8,
            min_anchor_response=1.25e-8,
            anchor_sign=1.0,
        )

        assert phase_report["status"]["admissible"] is False
        assert phase_report["reason_code"] == "FAIL_PHASE_INVARIANCE_TOL"
        assert current_report["status"]["admissible"] is False
        assert current_report["reason_code"] == "FAIL_CURRENT_INVARIANCE_TOL"
