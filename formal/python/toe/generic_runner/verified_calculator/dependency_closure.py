"""Generated calculator-specific Python/Julia/Lean dependency closure.

The closure is derived from imports and fixed contract surfaces. It is not a
developer-maintained allowlist, so a failing dependency cannot disappear by
editing a release manifest.
"""
from __future__ import annotations

import ast
import hashlib
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Iterable, Mapping

from .canonical import digest, file_sha256
from .errors import CalculatorError, require


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
    "formal/docs/research/project_situation_audit_20260904/c03_normalization_amendment_v1/effective_normalization_dag_contract_v1.json",
    "formal/tooling/scientific_compute/model1_installation_preparation/route_c03_derivation_pure_candidate_pass_0280_v0/provenance_dag_contract.json",
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
    artifact_paths = {row.get("path") for row in closure.get("profile_policy_artifact_references", ())}
    current_paths = set(FIXED_ARTIFACT_REFERENCES)
    frozen_v1_paths = current_paths - {
        "formal/docs/research/project_situation_audit_20260904/c03_normalization_amendment_v1/effective_normalization_dag_contract_v1.json",
        "formal/tooling/scientific_compute/model1_installation_preparation/route_c03_derivation_pure_candidate_pass_0280_v0/provenance_dag_contract.json",
    }
    require(artifact_paths in (current_paths, frozen_v1_paths), "DEPENDENCY_ARTIFACT_CLOSURE_NARROWED")
    require(closure.get("platform_runtime_commands") == {platform: list(commands) for platform, commands in PLATFORM_RUNTIME_COMMANDS.items()}, "DEPENDENCY_RUNTIME_COMMANDS_NARROWED")
    require(closure.get("unresolved_dynamic_imports") == [] and closure.get("unresolved_runtime_requirements") == [] and closure.get("manually_excluded_dependencies") == [], "DEPENDENCY_CLOSURE_NARROWED")


TEXT_IDENTITY_SUFFIXES = {
    "", ".gitattributes", ".json", ".jl", ".lean", ".lock", ".md",
    ".py", ".toml", ".txt", ".yaml", ".yml",
}


def canonical_text_v1_bytes(raw: bytes) -> bytes:
    """Return the deliberately narrow D-07 text identity domain.

    Only newline representation is normalized.  BOMs, invalid UTF-8,
    whitespace changes, and final-newline changes fail or remain visible.
    """
    require(not raw.startswith(b"\xef\xbb\xbf"), "CANONICAL_TEXT_V1_BOM")
    try:
        text = raw.decode("utf-8", "strict")
    except UnicodeDecodeError as exc:
        raise CalculatorError("CANONICAL_TEXT_V1_UTF8") from exc
    return text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")


def canonical_text_v1_sha256(raw: bytes) -> str:
    return hashlib.sha256(canonical_text_v1_bytes(raw)).hexdigest()


def _git(repository_root: Path, *args: str, text: bool = True) -> str | bytes:
    process = subprocess.run(
        ["git", "-C", str(repository_root), *args], capture_output=True,
        text=text, check=False,
    )
    require(process.returncode == 0, "DEPENDENCY_GIT_IDENTITY", detail=(process.stderr if text else process.stderr.decode("utf-8", "replace"))[-4000:])
    return process.stdout.strip() if text else process.stdout


def _identity_row(repository_root: Path, relative_path: str, tested_commit: str) -> dict[str, Any]:
    path = repository_root / relative_path
    require(path.is_file(), "DEPENDENCY_CLOSURE_FILE", relative_path)
    object_id = str(_git(repository_root, "rev-parse", f"{tested_commit}:{relative_path}"))
    blob = bytes(_git(repository_root, "cat-file", "blob", object_id, text=False))
    filesystem = path.read_bytes()
    row: dict[str, Any] = {
        "hash_domain": "GIT_BLOB_BYTES_V1",
        "git_commit": tested_commit,
        "repository_relative_path": relative_path,
        "git_object_id": object_id,
        "git_blob_sha256": hashlib.sha256(blob).hexdigest(),
        "filesystem_sha256": hashlib.sha256(filesystem).hexdigest(),
    }
    suffix = path.suffix.lower()
    if suffix in TEXT_IDENTITY_SUFFIXES or path.name in {"lean-toolchain"}:
        row.update({
            "checkout_domain": "CANONICAL_TEXT_V1",
            "canonical_text_v1_sha256": canonical_text_v1_sha256(blob),
            "filesystem_canonical_text_v1_sha256": canonical_text_v1_sha256(filesystem),
        })
        require(row["canonical_text_v1_sha256"] == row["filesystem_canonical_text_v1_sha256"], "DEPENDENCY_CANONICAL_TEXT_MISMATCH", relative_path)
    else:
        row["checkout_domain"] = "BINARY_BYTES_V1"
        require(blob == filesystem, "DEPENDENCY_BINARY_CHECKOUT_MISMATCH", relative_path)
    return row


def _v2_identity_projection(closure: Mapping[str, Any]) -> dict[str, Any]:
    def stable(row: Mapping[str, Any]) -> dict[str, Any]:
        return {key: value for key, value in row.items() if key not in {"filesystem_sha256", "filesystem_canonical_text_v1_sha256"}}

    return {
        "schema_id": closure["schema_id"],
        "generation_method": closure["generation_method"],
        "tested_commit": closure["tested_commit"],
        "python": [stable(row) for row in closure["python"]],
        "calculator_test_roots": closure["calculator_test_roots"],
        "runtime_requirement_lock": {**stable(closure["runtime_requirement_lock"]), "resolved_packages": closure["runtime_requirement_lock"]["resolved_packages"]},
        "unresolved_runtime_requirements": closure["unresolved_runtime_requirements"],
        "julia": [stable(row) for row in closure["julia"]],
        "lean": [stable(row) for row in closure["lean"]],
        "lean_imports": closure["lean_imports"],
        "platform_runtime_commands": closure["platform_runtime_commands"],
        "profile_policy_artifact_references": [stable(row) for row in closure["profile_policy_artifact_references"]],
        "runtime_profile_sources": closure["runtime_profile_sources"],
        "unresolved_dynamic_imports": closure["unresolved_dynamic_imports"],
        "manually_excluded_dependencies": closure["manually_excluded_dependencies"],
    }


def generate_dependency_closure_v2(
    repository_root: Path,
    *,
    tested_commit: str = "HEAD",
    require_clean: bool = True,
) -> dict[str, Any]:
    """Generate a Git-object-bound, checkout-observed D-07 closure.

    V1 remains available solely to replay the frozen pre-amendment lineage.
    V2 uses the Git blob as primary identity and records checkout bytes only as
    non-authoritative custody observations.
    """
    repository_root = repository_root.resolve(strict=True)
    commit = str(_git(repository_root, "rev-parse", f"{tested_commit}^{{commit}}"))
    if require_clean:
        status = str(_git(repository_root, "status", "--porcelain=v1", "--untracked-files=no"))
        require(not status, "DEPENDENCY_WORKTREE_NOT_CLEAN")
    old = generate_dependency_closure(repository_root)

    v2_seed_paths = (
        "formal/python/toe/generic_runner/verified_calculator_c03_rv_candidate_v2.py",
        "formal/python/toe/generic_runner/verified_calculator_c03_rv_qualification_v2.py",
        "formal/python/tools/compare_vpc_v6_payload.py",
        "formal/python/tools/generate_vpc_v6_execution_records.py",
        "formal/python/tools/run_vpc_v6_repair_acceptance.py",
        "formal/python/tests/test_verified_calculator_v6_repairs.py",
    )
    extra_rows, extra_external, extra_dynamic = _transitive_python_files(
        repository_root, (repository_root / path for path in v2_seed_paths)
    )
    merged_python = {row["path"]: row for row in old["python"]}
    merged_python.update({row["path"]: row for row in extra_rows})
    pins = _requirements_pins(repository_root / old["runtime_requirement_lock"]["path"])
    external_names = sorted({*old["runtime_requirement_lock"]["resolved_packages"], *extra_external})
    runtime_requirements = {name: pins.get(name) for name in external_names}
    unresolved = sorted(name for name, version in runtime_requirements.items() if version is None)

    def identity(path: str) -> dict[str, Any]:
        return _identity_row(repository_root, path, commit)

    python_rows = []
    for old_row in sorted(merged_python.values(), key=lambda row: row["path"]):
        row = identity(old_row["path"])
        row.update({key: old_row[key] for key in ("module", "imports", "local_dependencies")})
        python_rows.append(row)
    lock = identity(old["runtime_requirement_lock"]["path"])
    lock["resolved_packages"] = runtime_requirements
    lean_paths_v2 = sorted({
        *(row["path"] for row in old["lean"]),
        "formal/toe_formal/ToeFormal/VerifiedCalculator/RuntimeCertificateMainV1.lean",
        "formal/toe_formal/ToeFormal/VerifiedCalculator/QualificationEnvelopeV1.lean",
    })
    closure = {
        "schema_id": "VerifiedCalculatorDependencyClosureV2",
        "generation_method": "TRANSITIVE_STATIC_IMPORTS_PLUS_FIXED_CONTRACT_SURFACES__GIT_OBJECT_BOUND",
        "tested_commit": commit,
        "python": python_rows,
        "calculator_test_roots": [*old["calculator_test_roots"], "formal/python/tests/test_verified_calculator_v6_repairs.py"],
        "runtime_requirement_lock": lock,
        "unresolved_runtime_requirements": unresolved,
        "julia": [identity(row["path"]) for row in old["julia"]],
        "lean": [identity(path) for path in lean_paths_v2],
        "lean_imports": sorted(set(old["lean_imports"]) | {
            name
            for path in lean_paths_v2
            if path.endswith(".lean")
            for name in re.findall(r"^import\s+([^\s]+)", (repository_root / path).read_text(encoding="utf-8"), re.MULTILINE)
        }),
        "platform_runtime_commands": old["platform_runtime_commands"],
        "profile_policy_artifact_references": [identity(row["path"]) for row in old["profile_policy_artifact_references"]],
        "runtime_profile_sources": old["runtime_profile_sources"],
        "unresolved_dynamic_imports": sorted({*old["unresolved_dynamic_imports"], *extra_dynamic}),
        "manually_excluded_dependencies": old["manually_excluded_dependencies"],
    }
    closure["closure_hash"] = digest(_v2_identity_projection(closure), "VerifiedCalculatorDependencyClosureV2")
    closure["custody_observation_hash"] = digest(closure, "VerifiedCalculatorDependencyCustodyObservationV2")
    validate_dependency_closure_v2(closure)
    return closure


def validate_dependency_closure_v2(closure: Mapping[str, Any]) -> None:
    require(closure.get("schema_id") == "VerifiedCalculatorDependencyClosureV2", "DEPENDENCY_CLOSURE_V2_SCHEMA")
    supplied_observation = closure.get("custody_observation_hash")
    observation = dict(closure); observation.pop("custody_observation_hash", None)
    require(supplied_observation == digest(observation, "VerifiedCalculatorDependencyCustodyObservationV2"), "DEPENDENCY_CUSTODY_OBSERVATION_HASH")
    require(closure.get("closure_hash") == digest(_v2_identity_projection(closure), "VerifiedCalculatorDependencyClosureV2"), "DEPENDENCY_CLOSURE_HASH")
    rows = [*closure.get("python", ()), closure.get("runtime_requirement_lock", {}), *closure.get("julia", ()), *closure.get("lean", ()), *closure.get("profile_policy_artifact_references", ())]
    paths = []
    for row in rows:
        require(row.get("hash_domain") == "GIT_BLOB_BYTES_V1", "DEPENDENCY_HASH_DOMAIN")
        require(row.get("git_commit") == closure.get("tested_commit"), "DEPENDENCY_COMMIT_BINDING")
        require(all(isinstance(row.get(field), str) and row.get(field) for field in ("repository_relative_path", "git_object_id", "git_blob_sha256", "filesystem_sha256")), "DEPENDENCY_IDENTITY_FIELDS")
        if row.get("checkout_domain") == "CANONICAL_TEXT_V1":
            require(row.get("canonical_text_v1_sha256") == row.get("filesystem_canonical_text_v1_sha256"), "DEPENDENCY_CANONICAL_TEXT_MISMATCH", row.get("repository_relative_path"))
        else:
            require(row.get("checkout_domain") == "BINARY_BYTES_V1" and row.get("git_blob_sha256") == row.get("filesystem_sha256"), "DEPENDENCY_BINARY_CHECKOUT_MISMATCH", row.get("repository_relative_path"))
        paths.append(row["repository_relative_path"])
    require(len(paths) == len(set(paths)), "DEPENDENCY_DUPLICATE_PATH")
    require(closure.get("unresolved_dynamic_imports") == [] and closure.get("unresolved_runtime_requirements") == [] and closure.get("manually_excluded_dependencies") == [], "DEPENDENCY_CLOSURE_NARROWED")
