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
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_04_PHASE2_GATE_TOPOLOGY_SPLIT_COMPATIBILITY_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase2_gate_topology_split_compatibility_20260407_v0.json"
)
MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
SELECTOR_PATH = REPO_ROOT / "formal" / "python" / "tools" / "governance_manifest_select.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase2_t04_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase2 tranche04 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase2 tranche04 checkpoint artifact."
    assert MANIFEST_PATH.exists(), "Missing governance manifest."
    assert SELECTOR_PATH.exists(), "Missing governance manifest selector tool."


def test_phase2_t04_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE2_T04_GATE_TOPOLOGY_SPLIT_COMPATIBILITY",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_T04_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_04_PHASE2_GATE_TOPOLOGY_SPLIT_COMPATIBILITY_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_T04_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase2_gate_topology_split_compatibility_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_T04_GATE_v0: formal/python/tests/test_physics_math_throughput_phase2_gate_topology_split_compatibility_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_TOPOLOGY_MODE_v0: TIER_FILTER_COMPATIBILITY_LOCKED",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_EXECUTION_STATUS_v0: TOPOLOGY_COMPATIBILITY_DECLARED_NONLIVE_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_TOPOLOGY_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase2 tranche04 program token(s): " + ", ".join(missing)


def test_phase2_t04_topology_and_tooling_compatibility() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    manifest = _read_json(MANIFEST_PATH)
    selector_text = _read(SELECTOR_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE2_GATE_TOPOLOGY_SPLIT_COMPATIBILITY_v0"
    assert payload.get("status") == "PHASE2_T04_TOPOLOGY_COMPATIBILITY_DECLARED_NONLIVE_NONCLAIM"

    checks = payload.get("compatibility_checks", {})
    assert checks.get("manifest_has_test_tiers") is True
    assert checks.get("manifest_has_critical_group") is True
    assert checks.get("manifest_has_integrity_group") is True
    assert checks.get("selector_supports_tier_filter") is True
    assert checks.get("selector_supports_print_summary") is True

    manifest_groups = manifest.get("groups", {})
    assert "critical_gates" in manifest_groups
    assert "integrity_gates" in manifest_groups
    assert isinstance(manifest.get("test_tiers", {}), dict)

    assert "--tier-filter" in selector_text
    assert "--print-summary" in selector_text

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("execution_live_enabled") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_TOPOLOGY_DRIFT"
