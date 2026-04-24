from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


ACTIVE_GATE_TOKEN = "sr_m5_theory_parity_gate_path"

REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
GOVERNANCE_SUITE_PATH = REPO_ROOT / "governance_suite.ps1"
TEST_ROOT = REPO_ROOT / "formal" / "python" / "tests"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _cycle_from_path(path_text: str) -> int:
    m = re.search(r"cycle(\d+)", path_text)
    assert m is not None, f"Missing cycle marker in path: {path_text}"
    return int(m.group(1))


def test_sr_m5_cycle_archive_discipline_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    suite_text = _read(GOVERNANCE_SUITE_PATH)

    active_gate_rel = registry.get(ACTIVE_GATE_TOKEN)
    assert isinstance(active_gate_rel, str) and active_gate_rel, "Registry missing active SR M5 gate path."

    sr_row = next((row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-SR"), None)
    assert sr_row is not None, "Missing PILLAR-SR row in deep maturity registry."

    m5 = sr_row.get("m5_theory_parity", {})
    assert m5.get("gate_path") == active_gate_rel

    active_artifact_rel = m5.get("artifact_path")
    assert isinstance(active_artifact_rel, str) and active_artifact_rel, "Missing active SR M5 artifact path."

    gate_files = sorted(TEST_ROOT.glob("test_sr_m5_theory_parity_link_cycle*_gate.py"))
    assert gate_files, "No SR M5 cycle gate files found."

    active_gate_abs = REPO_ROOT / active_gate_rel
    assert active_gate_abs.exists(), f"Active gate path does not exist: {active_gate_rel}"

    active_cycle = _cycle_from_path(active_gate_rel)
    max_cycle = max(_cycle_from_path(str(p)) for p in gate_files)
    assert active_cycle == max_cycle, "Active SR M5 gate must be the highest cycle gate present."

    non_skipped = []
    for gate in gate_files:
        text = _read(gate)
        is_skipped = "pytestmark = pytest.mark.skip(" in text
        gate_cycle = _cycle_from_path(gate.name)

        if gate.resolve() == active_gate_abs.resolve():
            assert not is_skipped, "Active gate must not be skip-marked."
        else:
            assert is_skipped, f"Historical gate must be skip-marked: {gate.name}"

        if not is_skipped:
            non_skipped.append(gate)

    assert len(non_skipped) == 1, "Exactly one SR M5 cycle gate must remain active."
    assert non_skipped[0].resolve() == active_gate_abs.resolve()

    expected_artifact_rel = f"formal/output/sr_m5_theory_parity_link_cycle{active_cycle}_v0.json"
    assert active_artifact_rel == expected_artifact_rel
    assert (REPO_ROOT / active_artifact_rel).exists(), f"Missing active artifact: {active_artifact_rel}"

    assert active_gate_rel in suite_text, "Governance suite must execute the active SR M5 gate."
