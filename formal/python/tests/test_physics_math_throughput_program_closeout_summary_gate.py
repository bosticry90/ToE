from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))

REPORT_PATHS = [
    "formal/output/reports/physics_math_throughput_baseline_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase1_retro_truth_alignment_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase1_t02_selective_downgrade_execution_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase2_lane_split_bootstrap_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase2_gate_topology_split_compatibility_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase3_theorem_depth_bootstrap_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase3_t08_theorem_depth_execution_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase4_seam_empirical_bootstrap_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase4_t09_seam_empirical_execution_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase5_ssot_migration_bootstrap_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase5_t10_ssot_cutover_rehearsal_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase5_t11_program_closeout_readiness_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase6_t14_second_live_matrix_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase6_t15_third_live_matrix_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase6_t16_fourth_live_matrix_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase6_t17_fifth_live_matrix_packet_20260407_v0.json",
    "formal/output/reports/physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_all_remediation_reports_exist() -> None:
    for rel in REPORT_PATHS:
        assert (REPO_ROOT / rel).exists(), f"Missing remediation report: {rel}"


def test_all_report_controls_preserve_invariance() -> None:
    for rel in REPORT_PATHS:
        payload = _read_json(REPO_ROOT / rel)
        controls = payload.get("controls", {})
        if controls:
            assert controls.get("release_gate_truth_changed") is False, rel
            assert controls.get("nonclaim_boundary_changed") is False, rel
            assert controls.get("packet_policy_changed") is False, rel
            assert controls.get("scalar_freeze_policy_changed") is False, rel


def test_closeout_readiness_declares_full_coverage() -> None:
    closeout = _read_json(
        REPO_ROOT / "formal/output/reports/physics_math_throughput_phase5_t11_program_closeout_readiness_20260407_v0.json"
    )
    contract = closeout.get("coverage_contract", {})
    # T11 is a historical closeout-readiness contract and must remain pinned.
    assert contract.get("declared_tranche_count") == 12
    assert len(contract.get("tranche_ids", [])) == 12


def test_phase6_t12_decision_declares_extended_coverage() -> None:
    decision = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json"
    )
    contract = decision.get("coverage_contract", {})
    assert contract.get("declared_tranche_count") == 13
    assert len(contract.get("tranche_ids", [])) == 13


def test_phase6_t13_first_live_packet_declares_extended_coverage() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json"
    )
    contract = packet.get("coverage_contract", {})
    # T13 contract is historically pinned to the first 14 tranches.
    assert contract.get("declared_tranche_count") == 14
    assert len(contract.get("tranche_ids", [])) == 14


def test_phase6_t14_second_live_packet_declares_extended_coverage() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t14_second_live_matrix_packet_20260407_v0.json"
    )
    contract = packet.get("coverage_contract", {})
    # T14 contract is historically pinned to the first 15 tranches.
    assert contract.get("declared_tranche_count") == 15
    assert len(contract.get("tranche_ids", [])) == 15


def test_phase6_t15_third_live_packet_declares_extended_coverage() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t15_third_live_matrix_packet_20260407_v0.json"
    )
    contract = packet.get("coverage_contract", {})
    # T15 contract is historically pinned to the first 16 tranches.
    assert contract.get("declared_tranche_count") == 16
    assert len(contract.get("tranche_ids", [])) == 16


def test_phase6_t16_fourth_live_packet_declares_extended_coverage() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t16_fourth_live_matrix_packet_20260407_v0.json"
    )
    contract = packet.get("coverage_contract", {})
    # T16 contract is historically pinned to the first 17 tranches.
    assert contract.get("declared_tranche_count") == 17
    assert len(contract.get("tranche_ids", [])) == 17


def test_phase6_t17_fifth_live_packet_declares_extended_coverage() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t17_fifth_live_matrix_packet_20260407_v0.json"
    )
    contract = packet.get("coverage_contract", {})
    # T17 contract is historically pinned to the first 18 tranches.
    assert contract.get("declared_tranche_count") == 18
    assert len(contract.get("tranche_ids", [])) == 18


def test_phase6_t18_sixth_live_packet_declares_extended_coverage() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json"
    )
    contract = packet.get("coverage_contract", {})
    assert contract.get("declared_tranche_count") == len(REPORT_PATHS)
    assert len(contract.get("tranche_ids", [])) == len(REPORT_PATHS)


def test_phase6_t13_required_green_gates_include_live_controls() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json"
    )
    required = set(packet.get("live_matrix_packet", {}).get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py" in required


def test_phase6_t14_required_green_gates_include_live_controls() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t14_second_live_matrix_packet_20260407_v0.json"
    )
    required = set(packet.get("live_matrix_packet", {}).get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_t14_second_live_matrix_packet_gate.py" in required


def test_phase6_t15_required_green_gates_include_live_controls() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t15_third_live_matrix_packet_20260407_v0.json"
    )
    required = set(packet.get("live_matrix_packet", {}).get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_t15_third_live_matrix_packet_gate.py" in required


def test_phase6_t16_required_green_gates_include_live_controls() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t16_fourth_live_matrix_packet_20260407_v0.json"
    )
    required = set(packet.get("live_matrix_packet", {}).get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_t16_fourth_live_matrix_packet_gate.py" in required


def test_phase6_t17_required_green_gates_include_live_controls() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t17_fifth_live_matrix_packet_20260407_v0.json"
    )
    required = set(packet.get("live_matrix_packet", {}).get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_t17_fifth_live_matrix_packet_gate.py" in required


def test_phase6_t18_required_green_gates_include_live_controls() -> None:
    packet = _read_json(
        REPO_ROOT
        / "formal/output/reports/physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json"
    )
    required = set(packet.get("live_matrix_packet", {}).get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py" in required
    assert "formal/python/tests/test_physics_math_throughput_phase6_t18_sixth_live_matrix_packet_gate.py" in required
