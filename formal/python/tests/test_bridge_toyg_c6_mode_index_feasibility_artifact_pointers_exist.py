from __future__ import annotations

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


def test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    artifact_rel = Path("formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json")
    artifact_path = repo_root / artifact_rel
    assert artifact_path.exists(), "Expected Toy-G C6 mode-index feasibility artifact to exist"

    payload = json.loads(artifact_path.read_text(encoding="utf-8"))
    assert payload.get("schema_version") == 1
    assert payload.get("bridge_id") == "BRIDGE_TICKET_TOYG_0002"

    surface = dict(payload.get("canonical_surface", {}))
    surface_path = str(surface.get("path", ""))
    assert surface_path
    assert (repo_root / surface_path).exists(), f"Missing canonical surface path: {surface_path}"

    mismatch_source = dict(payload.get("program_mismatch_source", {}))
    mismatch_path = str(mismatch_source.get("path", ""))
    assert mismatch_path
    assert (repo_root / mismatch_path).exists(), f"Missing mismatch source path: {mismatch_path}"

    evidence = dict(payload.get("evidence", {}))
    nodes = list(evidence.get("pytest_nodes", []))
    assert nodes, "Missing pytest_nodes evidence in Toy-G mode-index feasibility artifact"
    for node in nodes:
        rel_path, fn_name = _parse_pytest_node(str(node))
        py_file = repo_root / Path(rel_path)
        assert py_file.exists(), f"Evidence path does not exist: {rel_path}"
        _assert_test_function_exists(py_file, fn_name)
