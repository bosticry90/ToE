from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

import pytest


@dataclass(frozen=True)
class SrM5CycleGateSpec:
    cycle: int
    status_token: str
    skip_historical: bool


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
TARGET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md"
SR_AUTHORITY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_AUDIT_OBJECTIVE = "LEGACY_LEAKAGE_ZERO_SINGLE_ACTIVE_POINTER_AND_TOKEN_ORDER_STABLE_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _assign_test(module_globals: dict[str, object], test_name: str, test_callable: object) -> None:
    test_callable.__name__ = test_name
    module_globals[test_name] = test_callable


def register_sr_m5_cycle_gate(module_globals: dict[str, object], spec: SrM5CycleGateSpec) -> None:
    cycle_str = f"{spec.cycle:02d}"
    prev_cycle_str = f"{spec.cycle - 1:02d}"
    gate_relative_path = f"formal/python/tests/test_sr_m5_theory_parity_link_cycle{cycle_str}_gate.py"
    artifact_relative_path = f"formal/output/sr_m5_theory_parity_link_cycle{cycle_str}_v0.json"
    artifact_path = REPO_ROOT / "formal" / "output" / f"sr_m5_theory_parity_link_cycle{cycle_str}_v0.json"
    expected_artifact_id = f"sr_m5_theory_parity_link_cycle{cycle_str}_v0"

    if spec.skip_historical:
        module_globals["pytestmark"] = pytest.mark.skip(
            reason="Historical SR M5 cycle gate retained for archive traceability; active gate is registry-driven."
        )

    def _test_cycle_gate() -> None:
        if spec.skip_historical:
            pytest.skip("Historical SR M5 cycle gate retained for archive traceability; active gate is registry-driven.")

        registry = _read_json(REGISTRY_PATH)
        target_text = _read(TARGET_DOC_PATH)
        sr_text = _read(SR_AUTHORITY_PATH)
        state_text = _read(STATE_PATH)
        roadmap_text = _read(ROADMAP_PATH)

        assert artifact_path.exists(), f"SR M5 theory-parity-link cycle{cycle_str} artifact is missing."
        artifact_json = _read_json(artifact_path)
        artifact_hash = hashlib.sha256(artifact_path.read_bytes()).hexdigest()

        assert artifact_json.get("artifact_id") == expected_artifact_id
        assert artifact_json.get("payload", {}).get("maturity_tier") == "M5_THEORY_PARITY_LINKED"
        assert artifact_json.get("payload", {}).get("status") == "RUN_BOUNDED_v0_NONCLAIM"
        assert artifact_json.get("payload", {}).get("audit_objective") == EXPECTED_AUDIT_OBJECTIVE
        assert artifact_json.get("payload", {}).get("readiness") == "THEORY_PARITY_LINK_PINNED_v0"

        assert registry.get("sr_m5_theory_parity_gate_path") == gate_relative_path

        sr_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-SR"), None)
        assert sr_row is not None, "Missing PILLAR-SR row in deep maturity registry."

        m5_parity = sr_row.get("m5_theory_parity", {})
        assert m5_parity.get("target_id") == "TARGET-SR-M5-THEORY-PARITY-LINK-v0"
        assert m5_parity.get("doc_path") == "formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md"
        assert m5_parity.get("artifact_path") == artifact_relative_path
        assert m5_parity.get("gate_path") == gate_relative_path

        for text in (target_text, sr_text, state_text, roadmap_text):
            assert _extract_token(text, "SR_M5_STATUS_v0") == spec.status_token
            assert _extract_token(text, "SR_M5_THEORY_PARITY_ARTIFACT_v0") == expected_artifact_id
            assert _extract_token(text, "SR_M5_THEORY_PARITY_SHA256_v0") == artifact_hash
            assert _extract_token(text, "SR_M5_THEORY_PARITY_GATE_v0") == EXPECTED_GATE
            assert _extract_token(text, "SR_M5_READINESS_v0") == "THEORY_PARITY_LINK_PINNED_v0"

        for path_ref in (
            artifact_relative_path,
            gate_relative_path,
            "formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md",
        ):
            assert path_ref in target_text
            assert path_ref in sr_text
            assert path_ref in state_text
            assert path_ref in roadmap_text

        for text in (target_text, sr_text, state_text, roadmap_text):
            assert text.count(artifact_relative_path) == 1
            assert text.count(gate_relative_path) == 1
            assert f"formal/output/sr_m5_theory_parity_link_cycle{prev_cycle_str}_v0.json" not in text
            assert f"formal/python/tests/test_sr_m5_theory_parity_link_cycle{prev_cycle_str}_gate.py" not in text

            idx_status = text.find("SR_M5_STATUS_v0")
            idx_artifact = text.find("SR_M5_THEORY_PARITY_ARTIFACT_v0")
            idx_sha = text.find("SR_M5_THEORY_PARITY_SHA256_v0")
            idx_gate = text.find("SR_M5_THEORY_PARITY_GATE_v0")
            idx_readiness = text.find("SR_M5_READINESS_v0")
            assert -1 not in (idx_status, idx_artifact, idx_sha, idx_gate, idx_readiness)
            assert idx_status < idx_artifact < idx_sha < idx_gate < idx_readiness

    _assign_test(module_globals, f"test_sr_m5_theory_parity_link_cycle{cycle_str}_gate", _test_cycle_gate)
