from __future__ import annotations

import importlib
import json
import re
from pathlib import Path


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _parse_pytest_node(node: str) -> tuple[str, str]:
    parts = str(node).split("::")
    if len(parts) != 2:
        raise AssertionError(f"Invalid pytest node (expected path::test_fn): {node!r}")
    return parts[0], parts[1]


def _assert_test_function_exists(py_file: Path, fn_name: str) -> None:
    text = py_file.read_text(encoding="utf-8", errors="ignore")
    pat = re.compile(rf"^def\s+{re.escape(fn_name)}\s*\(", flags=re.MULTILINE)
    assert pat.search(text), f"Expected test function {fn_name} in {py_file.as_posix()}"


def test_toy_law_ledger_evidence_pointers_exist() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    ledger_rel = Path("formal/quarantine/toy_laws/TOY_LAW_LEDGER.json")
    ledger_path = repo_root / ledger_rel
    assert ledger_path.exists(), "Expected toy-law ledger artifact to exist"

    payload = json.loads(ledger_path.read_text(encoding="utf-8"))
    assert payload.get("schema") == "TOY/toy_law_ledger/v1"

    for item in payload.get("items", []):
        front_door = item.get("front_door", {})
        module_name = str(front_door.get("tool_module", ""))
        assert module_name, f"Missing front_door.tool_module for toy_law_id={item.get('toy_law_id')}"
        importlib.import_module(module_name)

        evidence = item.get("evidence", {})
        nodes = list(evidence.get("pytest_nodes", []))
        assert nodes, f"Missing pytest_nodes evidence for toy_law_id={item.get('toy_law_id')}"

        for node in nodes:
            rel_path, fn_name = _parse_pytest_node(str(node))
            py_file = repo_root / Path(rel_path)
            assert py_file.exists(), f"Evidence path does not exist: {rel_path}"
            _assert_test_function_exists(py_file, fn_name)
