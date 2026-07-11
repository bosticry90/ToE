from __future__ import annotations

import ast
import json
from collections import defaultdict
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RECORD_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "HISTORICAL_CURRENT_MIRROR_TEST_RETIREMENTS_20260711_v0.json"
)
CONFTEST_PATH = REPO_ROOT / "formal" / "python" / "tests" / "conftest.py"

PROTECTED_CURRENT_GATE_PREFIXES = (
    "formal/python/tests/test_current_authoritative_surfaces_gate.py::",
    "formal/python/tests/test_current_target_freshness_gate.py::",
    "formal/python/tests/test_loop_control_registry_envelope_integrity_gate.py::",
    "formal/python/tests/test_loop_control_registry_v0_gate.py::",
)


def _record() -> dict:
    return json.loads(RECORD_PATH.read_text(encoding="utf-8"))


def test_retired_historical_current_mirror_nodes_are_exact_and_still_exist() -> None:
    payload = _record()
    rows = payload["retired_tests"]
    nodeids = [row["nodeid"] for row in rows]
    assert payload["status"] == (
        "APPLIED_EXACT_NODE_RETIREMENT_ARTIFACT_GATES_REMAIN_ACTIVE"
    )
    assert len(nodeids) == len(set(nodeids)) == 197
    assert payload["source_validation"]["retired_node_count"] == len(nodeids)

    by_file: dict[str, set[str]] = defaultdict(set)
    for nodeid in nodeids:
        path_text, test_name = nodeid.split("::", 1)
        by_file[path_text].add(test_name.split("[", 1)[0])
        assert not nodeid.startswith(PROTECTED_CURRENT_GATE_PREFIXES)

    for path_text, retired_names in by_file.items():
        path = REPO_ROOT / path_text
        assert path.exists(), f"retired test file disappeared: {path_text}"
        tree = ast.parse(path.read_text(encoding="utf-8-sig"))
        all_test_names = {
            node.name
            for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name.startswith("test_")
        }
        assert retired_names <= all_test_names
        assert all_test_names - retired_names, (
            f"retirement would suppress every test in {path_text}"
        )


def test_retirement_is_bounded_and_scientifically_nonpromotional() -> None:
    payload = _record()
    assert payload["current_target_at_retirement"] == (
        "execute_pillar_seam_unit_mapping_ledger_v0"
    )
    assert payload["boundary"] == {
        "artifact_or_scientific_test_files_deleted": False,
        "current_authority_gate_retired": False,
        "historical_artifacts_modified": False,
        "live_target_changed": False,
        "scientific_claim_changed": False,
    }
    assert {row["failure_class"] for row in payload["retired_tests"]} == {
        "historical_active_status_assertion",
        "historical_active_target_or_successor_assertion",
        "historical_authority_mirror_token_assertion",
        "historical_candidate_or_current_state_assertion",
        "historical_current_surface_or_successor_chain_assertion",
    }

    conftest = CONFTEST_PATH.read_text(encoding="utf-8")
    assert RECORD_PATH.name in conftest
    assert "retired_nodeids" in conftest
    assert "pytest.mark.skip" in conftest
