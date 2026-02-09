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


def test_bridge_toyg_canonical_feasibility_artifact_pointers_exist() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    artifact_rel = Path("formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json")
    artifact_path = repo_root / artifact_rel
    assert artifact_path.exists(), "Expected Toy-G canonical feasibility artifact to exist"

    payload = json.loads(artifact_path.read_text(encoding="utf-8"))
    assert payload.get("schema_version") == 1
    assert payload.get("bridge_family") == "BRIDGE_TOYG_CANONICAL_FEASIBILITY"

    targets = list(payload.get("targets", []))
    assert targets, "Expected non-empty targets list in Toy-G feasibility artifact"
    for t in targets:
        surface = dict(t.get("canonical_surface", {}))
        rel_path = str(surface.get("path", ""))
        assert rel_path, f"Missing canonical surface path for target={t.get('target_id')}"
        assert (repo_root / rel_path).exists(), f"Canonical surface path missing: {rel_path}"

    evidence = dict(payload.get("evidence", {}))
    nodes = list(evidence.get("pytest_nodes", []))
    assert nodes, "Missing pytest_nodes evidence in Toy-G feasibility artifact"
    for node in nodes:
        rel_path, fn_name = _parse_pytest_node(str(node))
        py_file = repo_root / Path(rel_path)
        assert py_file.exists(), f"Evidence path does not exist: {rel_path}"
        _assert_test_function_exists(py_file, fn_name)
