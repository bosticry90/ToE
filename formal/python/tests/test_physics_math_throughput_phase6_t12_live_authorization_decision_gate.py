from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_12_PHASE6_LIVE_AUTHORIZATION_DECISION_PACKET_20260407_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase6_t12_files_exist() -> None:
    assert PROGRAM_PATH.exists()
    assert DECLARATION_PATH.exists()
    assert CHECKPOINT_PATH.exists()


def test_phase6_t12_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE6_T12_LIVE_AUTHORIZATION_DECISION_PACKET",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T12_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_12_PHASE6_LIVE_AUTHORIZATION_DECISION_PACKET_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T12_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T12_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_t12_live_authorization_decision_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_NON_PLACEHOLDER_DELTA_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_non_placeholder_delta_gate.py",
    ]
    missing = [token for token in required if token not in text]
    assert not missing


def test_phase6_t12_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE6_T12_LIVE_AUTHORIZATION_DECISION_PACKET_v0"
    assert payload.get("status") == "PHASE6_T12_DECISION_PACKET_DECLARED_NONLIVE_NONCLAIM"

    coverage = payload.get("coverage_contract", {})
    assert coverage.get("declared_tranche_count") == 13
    assert len(coverage.get("tranche_ids", [])) == 13
    assert coverage.get("summary_gate") == "formal/python/tests/test_physics_math_throughput_program_closeout_summary_gate.py"

    decision = payload.get("go_no_go_contract", {})
    assert decision.get("decision_mode") == "GO_NO_GO_DECISION_PACKET_WITH_BASELINE_DELTA_CONTRACT"
    assert decision.get("live_execution_enabled") is False
    required_green = set(decision.get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_policy_approval_binding_gate.py" in required_green
    assert "formal/python/tests/test_physics_math_throughput_phase6_non_placeholder_delta_gate.py" in required_green

    delta = decision.get("delta_fields", {})
    assert delta.get("baseline_report") == "formal/output/reports/physics_math_throughput_baseline_20260407_v0.json"
    assert delta.get("current_reference") == "formal/output/reports/physics_math_throughput_phase5_t11_program_closeout_readiness_20260407_v0.json"
    assert delta.get("science_surface_share_delta") != 0.0
    assert delta.get("theorem_depth_queue_delta") != 0
    assert delta.get("seam_empirical_packet_delta") != 0
    assert delta.get("controls_overhead_delta") != 0.0

    provenance = decision.get("delta_provenance", {})
    assert provenance.get("refresh_tool") == "formal/python/tools/physics_math_throughput_phase6_delta_refresh.py"
    assert provenance.get("method") == "proxy_from_baseline_and_execution_packets"

    approval = payload.get("approval_binding", {})
    assert approval.get("decision_artifact") == "formal/docs/release/WS_10_T14_POST_T13_DUAL_CANDIDATE_LANE_AUTHORIZATION_DECISION_v0.md"
    assert approval.get("approval_status") == "APPROVAL_BOUND_NONLIVE"
    required_fields = set(approval.get("required_fields", []))
    expected_fields = {
        "approval_authority",
        "approval_timestamp_utc",
        "approval_scope_token",
        "approval_expiry_utc",
        "authorized_live_envelope",
    }
    assert expected_fields.issubset(required_fields)

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("execution_live_enabled") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_AUTHORIZATION_DRIFT"
