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


def test_bridge_toyh_c6_current_anchor_feasibility_artifact_pointers_exist() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    artifact_rel = Path("formal/quarantine/feasibility/BRIDGE_TOYH_C6_current_anchor_feasibility.json")
    artifact_path = repo_root / artifact_rel
    assert artifact_path.exists(), "Expected Toy-H C6 current-anchor feasibility artifact to exist"

    payload = json.loads(artifact_path.read_text(encoding="utf-8"))
    assert payload.get("schema_version") == 1
    assert payload.get("bridge_id") == "BRIDGE_TICKET_TOYH_0004"

    surface = dict(payload.get("canonical_surface", {}))
    surface_path = str(surface.get("path", ""))
    assert surface_path
    assert (repo_root / surface_path).exists(), f"Missing canonical surface path: {surface_path}"

    sources = dict(payload.get("source_artifacts", {}))
    for src in ["orthogonality_report", "mismatch_report", "mismatch_summary"]:
        info = dict(sources.get(src, {}))
        src_path = str(info.get("path", ""))
        assert src_path
        assert (repo_root / src_path).exists(), f"Missing source artifact path: {src_path}"

    evidence = dict(payload.get("evidence", {}))
    nodes = list(evidence.get("pytest_nodes", []))
    assert nodes, "Missing pytest_nodes evidence in Toy-H current-anchor feasibility artifact"
    for node in nodes:
        rel_path, fn_name = _parse_pytest_node(str(node))
        py_file = repo_root / Path(rel_path)
        assert py_file.exists(), f"Evidence path does not exist: {rel_path}"
        _assert_test_function_exists(py_file, fn_name)

