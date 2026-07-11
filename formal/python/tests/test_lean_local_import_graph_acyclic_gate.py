from __future__ import annotations

import re
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.generate_lean_all_modules_aggregate import tracked_module_names


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_ROOT = REPO_ROOT / "formal" / "toe_formal"
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$", re.MULTILINE)


def _module_path(module: str) -> Path:
    return LEAN_ROOT / Path(*module.split(".")).with_suffix(".lean")


def _local_imports(module: str, known: set[str]) -> list[str]:
    source = _module_path(module).read_text(encoding="utf-8")
    imports = [name for name in IMPORT_RE.findall(source) if name.startswith("ToeFormal")]
    missing = sorted(name for name in imports if name not in known)
    assert not missing, f"{module} has unresolved local imports: {missing}"
    return imports


def _find_cycle(graph: dict[str, list[str]]) -> list[str] | None:
    state: dict[str, int] = {}
    stack: list[str] = []
    positions: dict[str, int] = {}

    def visit(module: str) -> list[str] | None:
        color = state.get(module, 0)
        if color == 2:
            return None
        if color == 1:
            start = positions[module]
            return stack[start:] + [module]

        state[module] = 1
        positions[module] = len(stack)
        stack.append(module)
        for dependency in graph[module]:
            cycle = visit(dependency)
            if cycle is not None:
                return cycle
        stack.pop()
        positions.pop(module)
        state[module] = 2
        return None

    for module in graph:
        cycle = visit(module)
        if cycle is not None:
            return cycle
    return None


def test_every_working_tree_toeformal_module_has_resolved_local_imports() -> None:
    modules = tracked_module_names()
    known = set(modules)
    assert len(modules) == len(known)
    for module in modules:
        _local_imports(module, known)


def test_toeformal_local_import_graph_is_acyclic() -> None:
    modules = tracked_module_names()
    known = set(modules)
    graph = {module: _local_imports(module, known) for module in modules}
    cycle = _find_cycle(graph)
    assert cycle is None, "Lean local import cycle: " + " -> ".join(cycle or [])


def test_first_variation_cycle_repair_makes_retained_assumptions_explicit() -> None:
    core = _module_path("ToeFormal.Variational.FirstVariationRepresentationCore")
    declared = _module_path("ToeFormal.Variational.FirstVariationDeclared")
    uniqueness = _module_path("ToeFormal.Variational.FirstVariationUniqueness")

    core_text = core.read_text(encoding="utf-8")
    declared_text = declared.read_text(encoding="utf-8")
    uniqueness_text = uniqueness.read_text(encoding="utf-8")

    assert not re.search(r"^\s*(?:axiom|constant)\s+", core_text, re.MULTILINE)
    assert not re.search(r"^\s*(?:axiom|constant)\s+", declared_text, re.MULTILINE)
    assert "(hPairing : NondegeneratePairing)" in declared_text
    assert "(hEL : Represents EL_toe)" in declared_text
    assert "(hPcubic : Represents (FN01.P_cubic declared_g))" in declared_text
    assert "import ToeFormal.Variational.FirstVariationRepresentationCore" in declared_text
    assert "import ToeFormal.Variational.FirstVariationRepresentationCore" in uniqueness_text
    assert "import ToeFormal.Variational.FirstVariationDeclared" not in uniqueness_text


def test_coherence_transport_uses_type_parameters_not_signature_assumptions() -> None:
    path = _module_path("ToeFormal.SubstrateToyLaws.CoherenceTransport")
    text = path.read_text(encoding="utf-8")
    assert not re.search(r"^\s*(?:axiom|constant)\s+", text, re.MULTILINE)
    assert "structure BState (SubstrateState CoherenceState : Type u)" in text


def test_admissibility_manifest_has_one_conservative_default_declaration() -> None:
    path = _module_path("ToeFormal.Constraints.AD00_AdmissibilityManifest")
    text = path.read_text(encoding="utf-8")
    declarations = re.findall(
        r"^def defaultEnabled\s*:\s*List String\s*:=\s*(.+)$", text, re.MULTILINE
    )
    assert declarations == ["[]"]
    assert text.count('"enabled": false') == 3
