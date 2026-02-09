from __future__ import annotations

import numpy as np
from pathlib import Path

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


def test_bridge_program_orthogonality_expected_probe_signatures() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    by_probe = {str(it.get("probe_id")): it for it in report.get("items", [])}
    assert by_probe["baseline_all_pass"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_phase_control"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_current_control"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_current_control_alpha_0p125"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_current_control_alpha_0p500"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_current_control_alpha_1p000"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_theta_set_pi_over_6"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_theta_set_pi_over_2"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_theta_set_2pi_over_3"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_grid_size_n13"]["signature"] == "P-P-P"
    assert by_probe["stress_toyh_grid_size_n15"]["signature"] == "P-P-P"
    assert by_probe["stress_toyg_integer"]["signature"] == "P-P-P"
    assert by_probe["stress_toyg_unwrap"]["signature"] == "P-P-P"
    assert by_probe["stress_c6_amplitude_scale"]["signature"] == "F-F-F"
    assert by_probe["stress_c6_amplitude_scale_1p02"]["signature"] == "F-F-F"
    assert by_probe["stress_c6_amplitude_scale_1p05"]["signature"] == "F-F-F"
    assert by_probe["stress_c6_amplitude_scale_1p20"]["signature"] == "F-F-F"


def test_bridge_program_orthogonality_nonredundancy_summary() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    summary = dict(report.get("summary", {}))
    pairwise = dict(summary.get("pairwise_disagreement_counts", {}))

    assert summary.get("n_probes") == len(report.get("items", []))
    assert summary.get("nonredundant") is True
    assert int(pairwise.get("phase_vs_toyg_bridge", 0)) >= 1
    assert int(pairwise.get("current_vs_toyg_bridge", 0)) >= 1


def test_bridge_program_orthogonality_mode_index_resolves_targeted_winding_mismatch() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    summary = dict(report.get("summary", {}))
    resolution = dict(summary.get("targeted_resolution", {}))
    assert int(resolution.get("n_winding_not_integer_close_resolved_by_mode", 0)) >= 1


def test_bridge_program_orthogonality_unwrap_resolves_targeted_bridge_only_mismatch() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    summary = dict(report.get("summary", {}))
    resolution = dict(summary.get("targeted_resolution", {}))
    assert int(resolution.get("n_winding_unwrap_guard_resolved_by_unwrap", 0)) >= 1


def test_bridge_program_orthogonality_phase_anchor_resolves_targeted_phase_control_mismatch() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    summary = dict(report.get("summary", {}))
    resolution = dict(summary.get("targeted_resolution", {}))
    assert int(resolution.get("n_phase_control_fail_resolved_by_phase_anchor", 0)) >= 1


def test_bridge_program_orthogonality_current_anchor_resolves_targeted_current_control_mismatch() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    summary = dict(report.get("summary", {}))
    resolution = dict(summary.get("targeted_resolution", {}))
    assert int(resolution.get("n_current_control_fail_resolved_by_current_anchor", 0)) >= 1


def test_bridge_program_orthogonality_pair_channel_resolves_targeted_pair_vs_bridge_mismatch() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    summary = dict(report.get("summary", {}))
    resolution = dict(summary.get("targeted_resolution", {}))
    assert int(resolution.get("n_pair_vs_bridge_resolved_by_pair_channel", 0)) >= 1


def test_bridge_program_orthogonality_amplitude_expansion_negative_controls() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    by_probe = {str(it.get("probe_id")): it for it in report.get("items", [])}
    for probe_id in [
        "stress_c6_amplitude_scale",
        "stress_c6_amplitude_scale_1p02",
        "stress_c6_amplitude_scale_1p05",
        "stress_c6_amplitude_scale_1p20",
    ]:
        item = by_probe[probe_id]
        assert item["signature_raw"] == "F-F-P"
        assert item["signature"] == "F-F-F"


def test_bridge_program_orthogonality_current_control_expansion_presence() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    by_probe = {str(it.get("probe_id")): it for it in report.get("items", [])}
    current_probe_ids = [
        "stress_toyh_current_control_alpha_0p125",
        "stress_toyh_current_control_alpha_0p500",
        "stress_toyh_current_control_alpha_1p000",
    ]
    for probe_id in current_probe_ids:
        item = by_probe[probe_id]
        assert item["probe_kind"] == "toyh_current_control_stress_expansion_v2"
        assert item["signature"] == "P-P-P"

    summary = dict(report.get("summary", {}))
    assert int(summary.get("n_probes", 0)) == 17

    shared = dict(report.get("shared_probe_set", {}))
    assert shared.get("current_control_alphas_frontier_expansion_v2") == [0.125, 0.5, 1.0]
    assert float(shared.get("current_control_negative_anchor_sign_frontier_expansion_v2", 0.0)) == -1.0


def test_bridge_program_orthogonality_current_control_expansion_negative_controls() -> None:
    for alpha in [0.125, 0.5, 1.0]:
        report = evaluate_toyh_c6_current_anchor(
            theta=float(np.pi / 3.0),
            grid_n=11,
            amplitude_scale=1.0,
            local_phase_shear_alpha=float(alpha),
            anchor_sign=-1.0,
        )
        assert report["status"]["admissible"] is False
        assert report["reason_code"] == "FAIL_CURRENT_ANCHOR_MISMATCH"


def test_bridge_program_orthogonality_theta_set_expansion_presence() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    by_probe = {str(it.get("probe_id")): it for it in report.get("items", [])}
    theta_probe_ids = [
        "stress_toyh_theta_set_pi_over_6",
        "stress_toyh_theta_set_pi_over_2",
        "stress_toyh_theta_set_2pi_over_3",
    ]
    for probe_id in theta_probe_ids:
        item = by_probe[probe_id]
        assert item["probe_kind"] == "theta_set_stress_expansion_v3"
        assert item["signature"] == "P-P-P"

    summary = dict(report.get("summary", {}))
    assert int(summary.get("n_probes", 0)) == 17

    shared = dict(report.get("shared_probe_set", {}))
    assert np.allclose(
        shared.get("theta_values_frontier_expansion_v3"),
        [float(np.pi / 6.0), float(np.pi / 2.0), float(2.0 * np.pi / 3.0)],
    )
    assert float(shared.get("theta_negative_anchor_sign_frontier_expansion_v3", 0.0)) == -1.0


def test_bridge_program_orthogonality_theta_set_expansion_negative_controls() -> None:
    for theta in [float(np.pi / 6.0), float(np.pi / 2.0), float(2.0 * np.pi / 3.0)]:
        report = evaluate_toyh_c6_phase_anchor(
            theta=float(theta),
            grid_n=11,
            amplitude_scale=1.0,
            anchor_sign=-1.0,
        )
        assert report["status"]["admissible"] is False
        assert report["reason_code"] == "FAIL_ANCHOR_PHASE_MISMATCH"


def test_bridge_program_orthogonality_grid_size_expansion_presence() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root)

    by_probe = {str(it.get("probe_id")): it for it in report.get("items", [])}
    for probe_id, grid_n in [
        ("stress_toyh_grid_size_n13", 13),
        ("stress_toyh_grid_size_n15", 15),
    ]:
        item = by_probe[probe_id]
        assert item["probe_kind"] == "grid_size_stress_expansion_v4"
        assert int(item["grid_n"]) == int(grid_n)
        assert item["signature"] == "P-P-P"

    summary = dict(report.get("summary", {}))
    assert int(summary.get("n_probes", 0)) == 17

    shared = dict(report.get("shared_probe_set", {}))
    assert shared.get("grid_sizes_frontier_expansion_v4") == [13, 15]
    assert float(shared.get("grid_size_negative_amplitude_scale_frontier_expansion_v4", 0.0)) == 1.1


def test_bridge_program_orthogonality_grid_size_expansion_negative_controls() -> None:
    for grid_n in [13, 15]:
        phase_report = evaluate_toyh_c6_phase_anchor(
            theta=float(np.pi / 3.0),
            grid_n=int(grid_n),
            amplitude_scale=1.1,
            anchor_sign=1.0,
        )
        current_report = evaluate_toyh_c6_current_anchor(
            theta=float(np.pi / 3.0),
            grid_n=int(grid_n),
            amplitude_scale=1.1,
            local_phase_shear_alpha=0.5,
            anchor_sign=1.0,
        )

        assert phase_report["status"]["admissible"] is False
        assert phase_report["reason_code"] == "FAIL_PHASE_INVARIANCE_TOL"
        assert current_report["status"]["admissible"] is False
        assert current_report["reason_code"] == "FAIL_CURRENT_INVARIANCE_TOL"


def test_bridge_program_orthogonality_v5_tolerance_profile_application() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile="v5_t1")

    shared = dict(report.get("shared_probe_set", {}))
    profiles = dict(shared.get("tolerance_profile_frontier_expansion_v5", {}))
    effective = dict(shared.get("effective_tolerances_v5", {}))
    summary = dict(report.get("summary", {}))

    assert shared.get("tolerance_profile_selected_v5") == "v5_t1"
    assert set(profiles.keys()) == {"baseline", "v5_t1", "v5_t2"}
    assert int(summary.get("n_probes", 0)) == 17

    pinned_t1 = dict(profiles.get("v5_t1", {}))
    for k in [
        "toyh_tolerance",
        "phase_anchor_tolerance",
        "current_anchor_tolerance",
        "current_anchor_min_response",
    ]:
        assert np.isclose(float(effective[k]), float(pinned_t1[k]))


def test_bridge_program_orthogonality_v5_t1_negative_controls_preserve_reason_codes() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    report = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile="v5_t1")
    effective = dict(report.get("shared_probe_set", {}).get("effective_tolerances_v5", {}))

    phase_report = evaluate_toyh_c6_phase_anchor(
        theta=float(np.pi / 3.0),
        grid_n=15,
        amplitude_scale=1.1,
        tol_invariance=float(effective["toyh_tolerance"]),
        tol_phase_anchor=float(effective["phase_anchor_tolerance"]),
        min_anchor_magnitude=1e-8,
        anchor_sign=1.0,
    )
    current_report = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=15,
        amplitude_scale=1.1,
        local_phase_shear_alpha=0.5,
        tol_invariance=float(effective["toyh_tolerance"]),
        tol_current_anchor=float(effective["current_anchor_tolerance"]),
        min_anchor_response=float(effective["current_anchor_min_response"]),
        anchor_sign=1.0,
    )

    assert phase_report["status"]["admissible"] is False
    assert phase_report["reason_code"] == "FAIL_PHASE_INVARIANCE_TOL"
    assert current_report["status"]["admissible"] is False
    assert current_report["reason_code"] == "FAIL_CURRENT_INVARIANCE_TOL"


def test_bridge_program_orthogonality_v5_t2_expected_breaks_are_tolerance_driven() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    baseline = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile="baseline")
    t2 = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile="v5_t2")

    shared = dict(t2.get("shared_probe_set", {}))
    assert shared.get("phase_stabilization_lane_l1_enabled") is True
    assert int(t2.get("summary", {}).get("n_probes", 0)) == 17

    base_by_probe = {str(it.get("probe_id")): it for it in baseline.get("items", [])}
    t2_by_probe = {str(it.get("probe_id")): it for it in t2.get("items", [])}
    for probe_id, base_item in base_by_probe.items():
        if base_item["signature"] == "P-P-P":
            assert t2_by_probe[probe_id]["signature"] == "P-P-P"
