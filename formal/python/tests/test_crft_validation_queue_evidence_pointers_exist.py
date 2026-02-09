from __future__ import annotations

import json
import re
from pathlib import Path


def _repo_root_from_test_file(p: Path) -> Path:
    return p.resolve().parents[3]


def _parse_pytest_node(node: str) -> tuple[str, str]:
    # Expected: "path/to/file.py::test_func"
    if "::" not in node:
        raise AssertionError(f"Invalid pytest node (missing ::): {node!r}")
    path, func = node.split("::", 1)
    if not path.endswith(".py"):
        raise AssertionError(f"Invalid pytest node (path must end with .py): {node!r}")
    if not func:
        raise AssertionError(f"Invalid pytest node (missing function part): {node!r}")
    return path, func


def _assert_test_function_exists(py_file: Path, fn_name: str) -> None:
    text = py_file.read_text(encoding="utf-8", errors="ignore")
    # Keep it simple and deterministic: look for a top-level "def <name>(".
    pat = re.compile(rf"^def\s+{re.escape(fn_name)}\s*\(", flags=re.MULTILINE)
    assert pat.search(text), f"Expected test function {fn_name} in {py_file.as_posix()}"


def test_crft_validation_queue_evidence_pointers_exist() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    q_path = repo_root / "formal" / "quarantine" / "validation" / "CRFT_validation_queue_extended_crft_test_family_v1.json"
    assert q_path.exists(), "Expected generated validation queue artifact to exist"

    payload = json.loads(q_path.read_text(encoding="utf-8"))
    assert payload.get("schema_version") in {1, 2, 3}

    for item in payload.get("items", []):
        assert item.get("claim_family"), f"Missing claim_family for claim_id={item.get('claim_id')}"
        assert item.get("evidence_strength"), f"Missing evidence_strength for claim_id={item.get('claim_id')}"
        evidence = item.get("evidence", {})
        nodes = list(evidence.get("pytest_nodes", []))

        # If a ticket has no nodes, it's either not yet wired or intentionally doc-only.
        # For current queue items, nodes should be present.
        assert nodes, f"Missing pytest_nodes evidence for claim_id={item.get('claim_id')}"

        for node in nodes:
            rel_path, fn_name = _parse_pytest_node(str(node))
            py_file = repo_root / Path(rel_path)
            assert py_file.exists(), f"Evidence path does not exist: {rel_path}"
            _assert_test_function_exists(py_file, fn_name)
