from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


POLICY_PATH_REL = "formal/docs/release/SR_M5_ARCHIVE_RETENTION_POLICY_v0.md"
ARCHIVE_GATE_PATH = "formal/python/tests/test_sr_m5_cycle_archive_discipline_gate.py"
ROLL_TOOL_PATH = "formal/python/tools/sr_m5_cycle_rollover.py"

REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
POLICY_PATH = REPO_ROOT / POLICY_PATH_REL
TEST_ROOT = REPO_ROOT / "formal" / "python" / "tests"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}` in retention policy doc."
    return m.group(1)


def test_sr_m5_archive_retention_policy_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    policy_text = _read(POLICY_PATH)

    assert registry.get("sr_m5_archive_retention_policy_doc") == POLICY_PATH_REL
    assert registry.get("sr_m5_archive_retention_policy_gate_path") == (
        "formal/python/tests/test_sr_m5_archive_retention_policy_gate.py"
    )

    assert POLICY_PATH_REL in policy_text
    assert ROLL_TOOL_PATH in policy_text
    assert ARCHIVE_GATE_PATH in policy_text

    assert _extract_token(policy_text, "SR_M5_ARCHIVE_RETENTION_POLICY_STATUS_v0") == "ACTIVE_v0"
    max_history = int(_extract_token(policy_text, "SR_M5_ARCHIVE_RETENTION_MAX_HISTORY_v0"))
    cadence = int(_extract_token(policy_text, "SR_M5_QUALITY_CHECKPOINT_CADENCE_v0"))

    assert max_history >= 50, "Configured retention ceiling unexpectedly low."
    assert cadence > 0 and cadence <= 25, "Quality checkpoint cadence should be bounded and practical."

    gate_files = sorted(TEST_ROOT.glob("test_sr_m5_theory_parity_link_cycle*_gate.py"))
    assert len(gate_files) <= max_history, "SR M5 gate history exceeds policy ceiling."
