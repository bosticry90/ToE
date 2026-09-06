"""Generated calculator-specific Python/Julia/Lean dependency closure.

The closure is derived from imports and fixed contract surfaces. It is not a
developer-maintained allowlist, so a failing dependency cannot disappear by
editing a release manifest.
"""
from __future__ import annotations

import ast
from pathlib import Path
import re
import sys
from typing import Any, Iterable

from .canonical import digest, file_sha256
from .errors import require


TRUSTED_PREFIX = "formal.python.toe.generic_runner.verified_calculator"
CALCULATOR_TESTS = (
    "formal/python/tests/test_verified_calculator_v1.py",
    "formal/python/tests/test_typed_provenance_kernel_v1.py",
    "formal/python/tests/test_runner_provenance_verifier_v4.py",
    "formal/python/tests/test_c03_normalization_v1.py",
    "formal/python/tests/test_seven_record_source_candidate_v4.py",
    "formal/python/tests/test_rv_source_derivation_v2.py",
    "formal/python/tests/test_c03_physical_dag_v1.py",
)
FIXED_ARTIFACT_REFERENCES = (
    ".gitattributes",
    "formal/docs/release/VERIFIED_CALCULATOR_REPAIR_CORPUS_PRESERVATION_20260905_v1.json",
    "formal/docs/release/VERIFIED_CALCULATOR_C03_RV_POLICY_FREEZE_20260905_v1.json",
    "formal/docs/release/VERIFIED_CALCULATOR_C03_RV_SOURCE_MATERIAL_CONTRACT_20260905_v1.json",
    "formal/docs/release/STRICT_MODEL1_ROUTE_C_CURRENT_AUTHORITY_v0.json",
    "formal/tooling/scientific_compute/model1_installation_preparation/route_c03_terminal_adjudication_pass_0275_v0/terminal_adjudication.json",
    "formal/tooling/scientific_compute/model1_installation_preparation/route_c03_values_pass_0272_v0/closeout/six_record_value_damage_matrix.json",
    "formal/python/toe/generic_runner/verified_calculator/schemas/contracts_v1.schema.json",
    ".github/workflows/ci.yml",
)
PLATFORM_RUNTIME_COMMANDS = {
    "windows": ("certutil",),
    "linux": ("sha256sum",),
}


def _module_name(repository_root: Path, path: Path) -> str:
    relative = path.relative_to(repository_root).with_suffix("")
    parts = list(relative.parts)
    if parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def _resolved_import_name(current_module: str, is_package: bool, node: ast.ImportFrom) -> str:
    if node.level == 0:
        return node.module or ""
    package = current_module.split(".") if is_package else current_module.split(".")[:-1]
    keep = len(package) - node.level + 1
    require(keep >= 0, "PYTHON_RELATIVE_IMPORT", current_module)
    return ".".join(package[:keep] + ((node.module or "").split(".") if node.module else []))


def _python_imports(path: Path, module_name: str) -> tuple[tuple[str, ...], tuple[str, ...]]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    imports: set[str] = set()
    dynamic: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            base = _resolved_import_name(module_name, path.name == "__init__.py", node)
            if base:
                imports.add(base)
            for alias in node.names:
                if alias.name != "*" and base:
                    imports.add(f"{base}.{alias.name}")
        elif isinstance(node, ast.Call):
            name = ""
            if isinstance(node.func, ast.Name):
                name = node.func.id
            elif isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
                name = f"{node.func.value.id}.{node.func.attr}"
            if name in {"__import__", "importlib.import_module"} and node.args and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str):
                imports.add(node.args[0].value)
            elif name in {"__import__", "importlib.import_module", "eval", "exec"}:
                dynamic.append(f"{path.as_posix()}:{getattr(node, 'lineno', 0)}:{name}")
    return tuple(sorted(imports)), tuple(dynamic)


def _local_module_path(repository_root: Path, module: str) -> Path | None:
    if not module.startswith("formal"):
        return None
    stem = repository_root.joinpath(*module.split("."))
    candidates = (stem.with_suffix(".py"), stem / "__init__.py")
    return next((path for path in candidates if path.is_file()), None)


def _transitive_python_files(repository_root: Path, seeds: Iterable[Path]) -> tuple[list[dict[str, Any]], list[str], list[str]]:
    pending = [path.resolve(strict=True) for path in seeds]
    seen: set[Path] = set()
    rows: list[dict[str, Any]] = []
    external: set[str] = set()
    dynamic: list[str] = []
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        module = _module_name(repository_root, path)
        imports, hidden = _python_imports(path, module)
        dynamic.extend(hidden)
        local_dependencies: set[str] = set()
        for name in imports:
            dependency = _local_module_path(repository_root, name)
            if dependency is not None:
                local_dependencies.add(dependency.relative_to(repository_root).as_posix())
                pending.append(dependency)
            else:
                top = name.split(".")[0]
                if top not in sys.stdlib_module_names and top not in {"__future__", "formal"}:
                    external.add(top)
        rows.append({
            "path": path.relative_to(repository_root).as_posix(),
            "sha256": file_sha256(path),
            "module": module,
            "imports": list(imports),
            "local_dependencies": sorted(local_dependencies),
        })
    return sorted(rows, key=lambda row: row["path"]), sorted(external), sorted(dynamic)


def _requirements_pins(path: Path) -> dict[str, str]:
    pins: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "==" not in line:
            continue
        name, version = line.split("==", 1)
        pins[name.lower().replace("-", "_")] = version
    return pins


def generate_dependency_closure(repository_root: Path) -> dict[str, Any]:
    repository_root = repository_root.resolve(strict=True)
    package = repository_root / "formal" / "python" / "toe" / "generic_runner" / "verified_calculator"
    seeds = list(package.glob("*.py"))
    seeds.append(repository_root / "formal" / "python" / "toe" / "generic_runner" / "verified_calculator_c03_rv_census_v1.py")
    seeds.append(repository_root / "formal" / "python" / "toe" / "generic_runner" / "verified_calculator_c03_rv_candidate_v1.py")
    seeds.append(repository_root / "formal" / "python" / "toe" / "generic_runner" / "verified_calculator_c03_rv_qualification_v1.py")
    seeds.extend(repository_root / path for path in CALCULATOR_TESTS)
    require(all(path.is_file() for path in seeds), "DEPENDENCY_CLOSURE_FILE")
    python_rows, external, dynamic = _transitive_python_files(repository_root, seeds)
    trusted_rows = [row for row in python_rows if row["module"] == TRUSTED_PREFIX or row["module"].startswith(TRUSTED_PREFIX + ".")]
    for row in trusted_rows:
        forbidden = [name for name in row["imports"] if name.startswith("formal.python.toe.generic_runner.") and not name.startswith(TRUSTED_PREFIX)]
        require(not forbidden, "TRUSTED_IMPORT_BOUNDARY", row["path"], ",".join(forbidden))

    requirement_path = repository_root / "requirements.ci.lock"
    pins = _requirements_pins(requirement_path)
    runtime_requirements = {name: pins.get(name) for name in external}
    unresolved_requirements = sorted(name for name, version in runtime_requirements.items() if version is None)

    julia_root = repository_root / "formal" / "tooling" / "scientific_compute" / "julia"
    julia_paths = [julia_root / "Project.toml", julia_root / "Manifest.toml", julia_root / "verified_calculator_v1.jl", julia_root / "verified_calculator_c03_rv_v1.jl", julia_root / "verified_calculator_numerics_v1.jl"]
    lean_root = repository_root / "formal" / "toe_formal"
    lean_module = lean_root / "ToeFormal" / "VerifiedCalculator" / "RuntimeCertificateV1.lean"
    lean_imports = re.findall(r"^import\s+([^\s]+)", lean_module.read_text(encoding="utf-8"), re.MULTILINE)
    lean_paths = [lean_root / "lean-toolchain", lean_root / "lakefile.toml", lean_root / "lake-manifest.json", lean_module]
    artifact_paths = [repository_root / path for path in FIXED_ARTIFACT_REFERENCES]
    require(all(path.is_file() for path in julia_paths + lean_paths + artifact_paths), "DEPENDENCY_CLOSURE_FILE")
    closure = {
        "schema_id": "VerifiedCalculatorDependencyClosureV1",
        "generation_method": "TRANSITIVE_STATIC_IMPORTS_PLUS_FIXED_CONTRACT_SURFACES",
        "python": python_rows,
        "calculator_test_roots": list(CALCULATOR_TESTS),
        "runtime_requirement_lock": {"path": requirement_path.relative_to(repository_root).as_posix(), "sha256": file_sha256(requirement_path), "resolved_packages": runtime_requirements},
        "unresolved_runtime_requirements": unresolved_requirements,
        "julia": [{"path": path.relative_to(repository_root).as_posix(), "sha256": file_sha256(path)} for path in julia_paths],
        "lean": [{"path": path.relative_to(repository_root).as_posix(), "sha256": file_sha256(path)} for path in lean_paths],
        "lean_imports": lean_imports,
        "platform_runtime_commands": {platform: list(commands) for platform, commands in PLATFORM_RUNTIME_COMMANDS.items()},
        "profile_policy_artifact_references": [{"path": path.relative_to(repository_root).as_posix(), "sha256": file_sha256(path)} for path in artifact_paths],
        "runtime_profile_sources": "GENERATED_FROM_EACH_PHYSICS_PROFILE_SOURCE_DECLARATION_AND_HASH_CHECKED_AT_LOAD_TIME",
        "unresolved_dynamic_imports": dynamic,
        "manually_excluded_dependencies": [],
    }
    closure["closure_hash"] = digest(closure, "VerifiedCalculatorDependencyClosureV1")
    return closure


def validate_dependency_closure(closure: dict[str, Any]) -> None:
    supplied = closure.get("closure_hash")
    body = dict(closure); body.pop("closure_hash", None)
    require(supplied == digest(body, "VerifiedCalculatorDependencyClosureV1"), "DEPENDENCY_CLOSURE_HASH")
    require(closure.get("generation_method") == "TRANSITIVE_STATIC_IMPORTS_PLUS_FIXED_CONTRACT_SURFACES", "DEPENDENCY_CLOSURE_METHOD")
    require(set(closure.get("calculator_test_roots", ())) == set(CALCULATOR_TESTS), "DEPENDENCY_TEST_CLOSURE_NARROWED")
    require({row.get("path") for row in closure.get("profile_policy_artifact_references", ())} == set(FIXED_ARTIFACT_REFERENCES), "DEPENDENCY_ARTIFACT_CLOSURE_NARROWED")
    require(closure.get("platform_runtime_commands") == {platform: list(commands) for platform, commands in PLATFORM_RUNTIME_COMMANDS.items()}, "DEPENDENCY_RUNTIME_COMMANDS_NARROWED")
    require(closure.get("unresolved_dynamic_imports") == [] and closure.get("unresolved_runtime_requirements") == [] and closure.get("manually_excluded_dependencies") == [], "DEPENDENCY_CLOSURE_NARROWED")
