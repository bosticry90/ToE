from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


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

AGGREGATE_EXISTENCE_EXPECTATION_RETIREMENT = {
    "status": "RETIRED_RETENTION_EXPIRED_HISTORICAL_NONCURRENT",
    "accepted_disposition": "RETIRE_RETENTION_EXPIRED_EXPECTATION",
    "accepted_review": (
        "formal/docs/release/"
        "REPOSITORY_HISTORICAL_REPORT_AGGREGATE_CONTRACT_DECOMPOSITION_RESULT_REVIEW_20260722_v0.json"
    ),
    "identity_count": 19,
    "retention_expired_count": 19,
    "current_critical_count": 0,
    "ignored_live_path_count": 15,
    "committed_historical_record_count": 4,
    "identity_local_semantic_controls_retired": False,
}

IDENTITY_LOCAL_SEMANTIC_ROUTES = {
    REPORT_PATHS[0]: "formal/python/tests/test_physics_math_throughput_baseline_snapshot_gate.py",
    REPORT_PATHS[1]: "formal/python/tests/test_physics_math_throughput_phase1_retro_truth_alignment_gate.py",
    REPORT_PATHS[2]: "formal/python/tests/test_physics_math_throughput_phase1_t02_selective_downgrade_execution_gate.py",
    REPORT_PATHS[3]: "formal/python/tests/test_physics_math_throughput_phase2_lane_split_bootstrap_gate.py",
    REPORT_PATHS[4]: "formal/python/tests/test_physics_math_throughput_phase2_gate_topology_split_compatibility_gate.py",
    REPORT_PATHS[5]: "formal/python/tests/test_physics_math_throughput_phase3_theorem_depth_bootstrap_gate.py",
    REPORT_PATHS[6]: "formal/python/tests/test_physics_math_throughput_phase3_t08_theorem_depth_execution_packet_gate.py",
    REPORT_PATHS[7]: "formal/python/tests/test_physics_math_throughput_phase4_seam_empirical_bootstrap_gate.py",
    REPORT_PATHS[8]: "formal/python/tests/test_physics_math_throughput_phase4_t09_seam_empirical_execution_packet_gate.py",
    REPORT_PATHS[9]: "formal/python/tests/test_physics_math_throughput_phase5_ssot_migration_bootstrap_gate.py",
    REPORT_PATHS[10]: "formal/python/tests/test_physics_math_throughput_phase5_t10_ssot_cutover_rehearsal_gate.py",
    REPORT_PATHS[11]: "formal/python/tests/test_physics_math_throughput_phase5_t11_program_closeout_readiness_gate.py",
    REPORT_PATHS[12]: "formal/python/tests/test_physics_math_throughput_phase6_t12_live_authorization_decision_gate.py",
    REPORT_PATHS[13]: "formal/python/tests/test_physics_math_throughput_phase6_t13_first_live_matrix_packet_gate.py",
    REPORT_PATHS[14]: "formal/python/tests/test_physics_math_throughput_phase6_t14_second_live_matrix_packet_gate.py",
    REPORT_PATHS[15]: "formal/python/tests/test_physics_math_throughput_phase6_t15_third_live_matrix_packet_gate.py",
    REPORT_PATHS[16]: "formal/python/tests/test_physics_math_throughput_phase6_t16_fourth_live_matrix_packet_gate.py",
    REPORT_PATHS[17]: "formal/python/tests/test_physics_math_throughput_phase6_t17_fifth_live_matrix_packet_gate.py",
    REPORT_PATHS[18]: "formal/python/tests/test_physics_math_throughput_phase6_t18_sixth_live_matrix_packet_gate.py",
}

COMMITTED_HISTORICAL_REPORT_PATHS = tuple(REPORT_PATHS[15:])


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_aggregate_report_existence_expectation_is_formally_retired() -> None:
    retirement = AGGREGATE_EXISTENCE_EXPECTATION_RETIREMENT
    assert retirement["status"] == "RETIRED_RETENTION_EXPIRED_HISTORICAL_NONCURRENT"
    assert retirement["accepted_disposition"] == "RETIRE_RETENTION_EXPIRED_EXPECTATION"
    assert (REPO_ROOT / retirement["accepted_review"]).is_file()
    assert retirement["identity_count"] == len(REPORT_PATHS)
    assert retirement["retention_expired_count"] == len(REPORT_PATHS)
    assert retirement["current_critical_count"] == 0
    assert retirement["ignored_live_path_count"] == 15
    assert retirement["committed_historical_record_count"] == len(COMMITTED_HISTORICAL_REPORT_PATHS)
    assert retirement["identity_local_semantic_controls_retired"] is False


def test_aggregate_control_invariance_is_decomposed_to_identity_local_routes() -> None:
    assert list(IDENTITY_LOCAL_SEMANTIC_ROUTES) == REPORT_PATHS
    assert len(set(IDENTITY_LOCAL_SEMANTIC_ROUTES.values())) == len(REPORT_PATHS)

    for report_path, local_gate_path in IDENTITY_LOCAL_SEMANTIC_ROUTES.items():
        local_gate = REPO_ROOT / local_gate_path
        assert local_gate.is_file(), local_gate_path
        assert Path(report_path).name in _read(local_gate), local_gate_path

    for report_path in COMMITTED_HISTORICAL_REPORT_PATHS:
        assert (REPO_ROOT / report_path).is_file(), report_path


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
