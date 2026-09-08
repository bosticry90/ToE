from __future__ import annotations

"""Strict, read-only evidence assembler for the R13 mechanism experiment.

This module is deliberately downstream of execution.  It has no execution
entry point and never creates or edits an experiment artifact.  Its public
``assemble_raw_evidence`` API accepts only a repository root and hard-binds the
v2 matrix, identity manifest, freeze packet, review anchor, and completed output
root.  Classifier gates and mechanism metrics are reconstructed from the twelve
JSON/NPZ payloads; caller-supplied booleans and stored summary metrics are never
authoritative.
"""

import hashlib
import importlib
import io
import json
import math
import struct
import zipfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NoReturn

import numpy as np

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v2
    as executor_custody_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v2
    as executor_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1
    as semantic_v1,
)


ASSEMBLER_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RAW_EVIDENCE_ASSEMBLER_v2"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v2.py"
)
DEFAULT_RUN_MATRIX_RELATIVE_PATH = executor_custody_v2.RUN_MATRIX_RELATIVE_PATH
DEFAULT_IDENTITY_MANIFEST_RELATIVE_PATH = (
    executor_custody_v2.IDENTITY_MANIFEST_RELATIVE_PATH
)
DEFAULT_FREEZE_PACKET_RELATIVE_PATH = executor_custody_v2.FREEZE_PACKET_RELATIVE_PATH
EXPECTED_OUTPUT_ROOT_RELATIVE_PATH = (
    executor_custody_v2.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
)
EXPECTED_CANONICAL_ROOT_RELATIVE_PATH = (
    executor_custody_v2.CANONICAL_OUTPUT_ROOT_RELATIVE_PATH
)
EXPECTED_CANONICAL_TREE_SHA256 = (
    "886541953dfcfecfffa44b2ff9e2ee62c14c468139042bf4f3477ef3a1f2a721"
)
EXPECTED_CANONICAL_INVENTORY_SHA256 = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)
EXPECTED_IMPLEMENTATION_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_IMPLEMENTATION_v0"
)
EXPECTED_IMPLEMENTATION_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_implementation_v0.py"
)
EXPECTED_IMPLEMENTATION_SHA256 = (
    "f4bdd5cd0f725f135060e1fe7476ef8edc5ce2a12c72ec0b0357239197006150"
)
EXPECTED_BOUND_SOURCES = {
    (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_non_authoritative_pilot_v1.py"
    ): "05e7015499e3d15bc172840ac637fd0fa86b6c50f87489d6b555657ac290adb6",
    (
        "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_"
        "pilot.py"
    ): "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
}
CLASSIFIER_V2_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_classifier_v2"
)
ASSEMBLER_V2_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v2"
)
SEMANTIC_V1_MODULE = semantic_v1.__name__
REQUIRED_IMPLEMENTATION_MODULE_NAMES = {
    ASSEMBLER_V2_MODULE,
    CLASSIFIER_V2_MODULE,
    SEMANTIC_V1_MODULE,
    executor_v2.__name__,
    executor_custody_v2.__name__,
    executor_custody_v2.V0_IMPLEMENTATION_MODULE,
    executor_custody_v2.HISTORICAL_EVOLUTION_MODULE,
    executor_custody_v2.HISTORICAL_PACK_MODULE,
}
RUN_PAYLOAD_JSON_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RUN_PAYLOAD_JSON_v0"
)
RUN_PAYLOAD_NPZ_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RUN_PAYLOAD_NPZ_v0"
)
RUN_ROLE_PAYLOAD_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_RUN_ROLE_PAYLOAD_v0"
)
EXECUTION_STARTED_SCHEMA_ID = executor_v2.EXECUTION_STARTED_SCHEMA_ID
MATRIX_RESULT_SCHEMA_ID = executor_v2.MATRIX_RESULT_SCHEMA_ID
EXPECTED_RUN_IDS = executor_custody_v2.EXACT_RUN_IDS
PAIR_IDS = (
    (EXPECTED_RUN_IDS[0], EXPECTED_RUN_IDS[1]),
    (EXPECTED_RUN_IDS[2], EXPECTED_RUN_IDS[3]),
    (EXPECTED_RUN_IDS[4], EXPECTED_RUN_IDS[5]),
)
CLASSIFIER_ROLE_BY_RUN_ID = {
    EXPECTED_RUN_IDS[0]: "R13_LOOSE",
    EXPECTED_RUN_IDS[2]: "R13_TIGHT",
    EXPECTED_RUN_IDS[4]: "R10_LOOSE_NEIGHBOR",
}
BLOCK_IDS = (
    "THETA_KINEMATIC",
    "P_LONGITUDINAL_MAXWELL",
    "PHI2_KINEMATIC",
    "P2_DYNAMIC",
    "PHI3_KINEMATIC",
    "P3_DYNAMIC",
    "DIRAC_PLUS",
    "DIRAC_MINUS",
)
BLOCK_SPANS_IN_N = {
    "THETA_KINEMATIC": (0, 1),
    "P_LONGITUDINAL_MAXWELL": (1, 2),
    "PHI2_KINEMATIC": (2, 3),
    "P2_DYNAMIC": (3, 4),
    "PHI3_KINEMATIC": (4, 5),
    "P3_DYNAMIC": (5, 6),
    "DIRAC_PLUS": (6, 14),
    "DIRAC_MINUS": (14, 22),
}
EVENT_FAMILIES = (
    "exchange",
    "terminal_equation_blocks",
    "solver_steps",
    "spatial_constraints",
    "discrete_closure",
)
PACKED_COMPONENTS_PER_SITE = 22
POSTINITIAL_STEPS = 16
CHECKPOINT_COUNT = 17
LATTICE_SIZE = 16
PACKED_WIDTH = PACKED_COMPONENTS_PER_SITE * LATTICE_SIZE
FLOAT64_UNIT_ROUNDOFF = 2.0**-53
GAMMA64 = (64.0 * FLOAT64_UNIT_ROUNDOFF) / (
    1.0 - 64.0 * FLOAT64_UNIT_ROUNDOFF
)
_TRAJECTORY_DOMAIN = b"R13-MECHANISM-PHYSICAL-TRAJECTORY-v0\x00"


class RawEvidenceError(ValueError):
    """Fail-closed evidence error with an authoritative blocked class."""

    def __init__(self, evidence_result: str, diagnostic: str, detail: str = "") -> None:
        super().__init__(f"{diagnostic}: {detail}" if detail else diagnostic)
        self.evidence_result = evidence_result
        self.diagnostic = diagnostic
        self.detail = detail


@dataclass(frozen=True)
class AssembledRawEvidence:
    assembler_id: str
    run_ids: tuple[str, ...]
    payload_identity_ids: tuple[str, ...]
    payloads_by_run_id: Mapping[str, Mapping[str, Any]]
    recomputed_metrics: Mapping[str, Mapping[str, Mapping[str, Any]]]
    nonperturbation_pairs: tuple[Mapping[str, Any], ...]
    canonical_tree_sha256: str
    review_anchor_sha256: str
    runtime_source_closure_sha256: str
    raw_evidence_ids: tuple[str, ...]
    supplied_summary_disposition: str
    semantic_contract_id: str


def _fail(result: str, diagnostic: str, detail: str = "") -> NoReturn:
    raise RawEvidenceError(result, diagnostic, detail)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _is_lower_hex(value: Any, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _sha256_path(path: Path, *, missing_result: str = "BLOCKED_CUSTODY") -> str:
    if not path.is_file():
        _fail(missing_result, "REQUIRED_OUTPUT_MISSING", str(path))
    return _sha256(path.read_bytes())


def _reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "DUPLICATE_JSON_KEY", key)
        result[key] = value
    return result


def _load_json_object(
    path: Path,
    *,
    missing_result: str = "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
) -> dict[str, Any]:
    if not path.is_file():
        _fail(missing_result, "REQUIRED_OUTPUT_MISSING", str(path))
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_reject_duplicate_pairs
        )
    except RawEvidenceError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "JSON_SCHEMA_INVALID", str(error))
    if not isinstance(value, dict):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "JSON_ROOT_NOT_OBJECT", str(path))
    return value


def _require_exact_keys(
    value: Any,
    expected: Sequence[str] | set[str] | tuple[str, ...],
    *,
    diagnostic: str,
) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", diagnostic, "not a mapping")
    expected_set = set(expected)
    actual_set = set(value)
    if actual_set != expected_set:
        missing = sorted(expected_set - actual_set)
        extra = sorted(actual_set - expected_set)
        _fail(
            "BLOCKED_OBSERVABLE_SEMANTICS",
            diagnostic,
            f"missing={missing}; extra={extra}",
        )
    return value


def _finite_float(value: Any, name: str, *, positive: bool = False) -> float:
    if isinstance(value, bool):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_FIELD_TYPE_INVALID", name)
    try:
        result = float(value)
    except (TypeError, ValueError):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_FIELD_TYPE_INVALID", name)
    if not math.isfinite(result) or (positive and result <= 0.0):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_FIELD_VALUE_INVALID", name)
    return result


def _exact_int(value: Any, name: str, *, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_FIELD_TYPE_INVALID", name)
    if minimum is not None and value < minimum:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_FIELD_VALUE_INVALID", name)
    return value


def _array(
    value: Any,
    name: str,
    *,
    shape: tuple[int, ...],
    dtype: np.dtype[Any] = np.dtype("<f8"),
) -> np.ndarray:
    if not isinstance(value, np.ndarray):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_ARRAY_REQUIRED", name)
    array = np.asarray(value)
    if array.shape != shape or array.dtype != dtype:
        _fail(
            "BLOCKED_OBSERVABLE_SEMANTICS",
            "RAW_ARRAY_SHAPE_OR_DTYPE_INVALID",
            f"{name}: shape={array.shape}, dtype={array.dtype}",
        )
    if array.dtype.kind in "fc" and not np.all(np.isfinite(array)):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_ARRAY_NONFINITE", name)
    return np.ascontiguousarray(array)


def _assert_exact(actual: Any, expected: Any, diagnostic: str, detail: str) -> None:
    if isinstance(actual, np.ndarray) or isinstance(expected, np.ndarray):
        if not (
            isinstance(actual, np.ndarray)
            and isinstance(expected, np.ndarray)
            and actual.dtype == expected.dtype
            and actual.shape == expected.shape
            and actual.tobytes(order="C") == expected.tobytes(order="C")
        ):
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", diagnostic, detail)
        return
    if type(actual) is not type(expected) or actual != expected:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", diagnostic, detail)


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _directory_tree_sha256(root: Path) -> str:
    if not root.is_dir():
        _fail("BLOCKED_CUSTODY", "CANONICAL_OUTPUT_ROOT_MISSING", str(root))
    digest = hashlib.sha256()
    digest.update(b"R13-MECHANISM-DIRECTORY-TREE-v0\x00")
    files = sorted(
        (path for path in root.rglob("*") if path.is_file()),
        key=lambda path: path.relative_to(root).as_posix(),
    )
    for path in files:
        relative = path.relative_to(root).as_posix().encode("utf-8")
        contents = path.read_bytes()
        digest.update(struct.pack("<Q", len(relative)))
        digest.update(relative)
        digest.update(struct.pack("<Q", len(contents)))
        digest.update(hashlib.sha256(contents).digest())
    return digest.hexdigest()


def _attest_authority_file_binding(
    repo_root: Path,
    binding: Mapping[str, Any],
    *,
    diagnostic: str,
) -> tuple[Path, bytes]:
    required = {"relative_path", "sha256"}
    if not required <= set(binding):
        _fail("BLOCKED_CUSTODY", diagnostic, "binding fields missing")
    relative_path = binding["relative_path"]
    if not isinstance(relative_path, str) or not relative_path:
        _fail("BLOCKED_CUSTODY", diagnostic, "relative_path invalid")
    path = (repo_root / relative_path).resolve()
    try:
        path.relative_to(repo_root)
    except ValueError:
        _fail("BLOCKED_CUSTODY", diagnostic, "path escapes repository")
    if not path.is_file():
        _fail("BLOCKED_CUSTODY", diagnostic, relative_path)
    contents = path.read_bytes()
    if (
        not _is_lower_hex(binding["sha256"], 64)
        or _sha256(contents) != binding["sha256"]
    ):
        _fail("BLOCKED_CUSTODY", diagnostic, relative_path)
    return path, contents


def _load_and_attest_reviewed_authority(
    repo_root: Path,
) -> tuple[Mapping[str, Any], str]:
    anchor_path = repo_root / executor_custody_v2.REVIEW_ANCHOR_RELATIVE_PATH
    anchor = _load_json_object(anchor_path, missing_result="BLOCKED_CUSTODY")
    if anchor.get("verdict") != executor_custody_v2.EXPECTED_REVIEW_VERDICT:
        _fail("BLOCKED_CUSTODY", "FREEZE_REVIEW_VERDICT_NOT_ACCEPTED")
    authority = anchor.get(executor_custody_v2.REVIEW_AUTHORITY_FIELD)
    expected_authority_keys = {
        "schema_id",
        "executor_id",
        "execution_authorized",
        "one_execution_only",
        "automatic_retries_authorized",
        "exact_run_ids",
        "pair_run_ids",
        "artifact_bindings",
        "runtime_source_closure",
        "runtime_source_closure_sha256",
        "expected_matrix_semantic_sha256",
        "expected_full_record_sha256_by_run_id",
        "expected_identity_fields_by_run_id",
        "expected_physical_configuration_sha256_by_run_id",
        "expected_scientific_input_sha256_by_run_id",
        "expected_complete_execution_sha256_by_run_id",
        "canonical_directory_tree_sha256",
        "canonical_directory_tree_sha256_domain",
        "experiment_output_root_relative_path",
        "canonical_output_root_relative_path",
    }
    if not isinstance(authority, Mapping) or not expected_authority_keys <= set(
        authority
    ):
        _fail("BLOCKED_CUSTODY", "RUNTIME_EXECUTION_AUTHORITY_SCHEMA_INVALID")
    try:
        loaded_authority, anchor_report = executor_v2._load_reviewed_authority(
            repo_root
        )
    except Exception as error:  # the loader is itself fail-closed
        _fail(
            "BLOCKED_CUSTODY",
            "REVIEWED_RUNTIME_AUTHORITY_LOAD_FAILED",
            f"{type(error).__name__}:{error}",
        )
    if loaded_authority != authority:
        _fail("BLOCKED_CUSTODY", "REVIEWED_RUNTIME_AUTHORITY_MISMATCH")
    anchor_sha256 = _sha256(anchor_path.read_bytes())
    if (
        anchor_report.get("relative_path")
        != executor_custody_v2.REVIEW_ANCHOR_RELATIVE_PATH
        or anchor_report.get("verdict")
        != executor_custody_v2.EXPECTED_REVIEW_VERDICT
        or anchor_report.get("sha256") != anchor_sha256
        or anchor_report.get("fixed_path_bytes_loaded") is not True
        or anchor_report.get("runtime_execution_authority_sha256")
        != _sha256(executor_v2.canonical_json_bytes(authority))
    ):
        _fail("BLOCKED_CUSTODY", "REVIEW_ANCHOR_ATTESTATION_MISMATCH")
    if (
        authority["executor_id"] != executor_v2.EXECUTOR_ID
        or authority["execution_authorized"] is not True
        or authority["one_execution_only"] is not True
        or authority["automatic_retries_authorized"] is not False
    ):
        _fail("BLOCKED_CUSTODY", "RUNTIME_EXECUTION_AUTHORITY_SEMANTICS_MISMATCH")
    if authority["exact_run_ids"] != list(EXPECTED_RUN_IDS):
        _fail("BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH")
    if authority["pair_run_ids"] != [list(pair) for pair in PAIR_IDS]:
        _fail("BLOCKED_RUN_IDENTITY", "RUN_PAIR_IDENTITY_MISMATCH")
    if (
        authority["experiment_output_root_relative_path"]
        != EXPECTED_OUTPUT_ROOT_RELATIVE_PATH
        or authority["canonical_output_root_relative_path"]
        != EXPECTED_CANONICAL_ROOT_RELATIVE_PATH
    ):
        _fail("BLOCKED_CUSTODY", "REVIEWED_OUTPUT_ROOT_IDENTITY_MISMATCH")
    if (
        authority["canonical_directory_tree_sha256"]
        != EXPECTED_CANONICAL_TREE_SHA256
    ):
        _fail("BLOCKED_CUSTODY", "REVIEWED_CANONICAL_DIGEST_MISMATCH")
    closure_digest = authority["runtime_source_closure_sha256"]
    if not _is_lower_hex(closure_digest, 64):
        _fail("BLOCKED_CUSTODY", "RUNTIME_SOURCE_CLOSURE_DIGEST_INVALID")
    expected_map_keys = set(EXPECTED_RUN_IDS)
    for field in (
        "expected_full_record_sha256_by_run_id",
        "expected_physical_configuration_sha256_by_run_id",
        "expected_scientific_input_sha256_by_run_id",
        "expected_complete_execution_sha256_by_run_id",
    ):
        mapping = authority[field]
        if (
            not isinstance(mapping, Mapping)
            or set(mapping) != expected_map_keys
            or any(not _is_lower_hex(value, 64) for value in mapping.values())
        ):
            _fail("BLOCKED_CUSTODY", "REVIEWED_RECORD_HASH_MAP_INVALID", field)
    artifact_bindings = authority["artifact_bindings"]
    if (
        not isinstance(artifact_bindings, Mapping)
        or set(artifact_bindings) != set(executor_custody_v2.REQUIRED_ARTIFACT_PATHS)
    ):
        _fail("BLOCKED_CUSTODY", "ARTIFACT_BINDING_CLOSURE_INVALID")
    artifact_paths: list[str] = []
    for artifact_name, expected_relative_path in (
        executor_custody_v2.REQUIRED_ARTIFACT_PATHS.items()
    ):
        binding = artifact_bindings[artifact_name]
        if not isinstance(binding, Mapping):
            _fail("BLOCKED_CUSTODY", "ARTIFACT_BINDING_CLOSURE_INVALID")
        if binding.get("relative_path") != expected_relative_path:
            _fail(
                "BLOCKED_CUSTODY",
                "ARTIFACT_BINDING_CLOSURE_INVALID",
                artifact_name,
            )
        _attest_authority_file_binding(
            repo_root, binding, diagnostic="REVIEWED_ARTIFACT_BYTES_MISMATCH"
        )
        artifact_paths.append(str(binding["relative_path"]))
    if len(artifact_paths) != len(set(artifact_paths)):
        _fail("BLOCKED_CUSTODY", "DUPLICATE_REVIEWED_ARTIFACT_BINDING")
    if set(artifact_paths) != set(executor_custody_v2.REQUIRED_ARTIFACT_PATHS.values()):
        _fail("BLOCKED_CUSTODY", "ARTIFACT_BINDING_CLOSURE_INVALID")
    runtime_source_closure = authority["runtime_source_closure"]
    if (
        not isinstance(runtime_source_closure, Mapping)
        or not isinstance(runtime_source_closure.get("modules"), list)
    ):
        _fail("BLOCKED_CUSTODY", "RUNTIME_SOURCE_CLOSURE_INVALID")
    if (
        _sha256(executor_v2.canonical_json_bytes(runtime_source_closure))
        != closure_digest
    ):
        _fail("BLOCKED_CUSTODY", "RUNTIME_SOURCE_CLOSURE_DIGEST_MISMATCH")
    module_names: list[str] = []
    for binding in runtime_source_closure["modules"]:
        if not isinstance(binding, Mapping) or not isinstance(
            binding.get("module_name"), str
        ):
            _fail("BLOCKED_CUSTODY", "RUNTIME_SOURCE_CLOSURE_INVALID")
        module_name = str(binding["module_name"])
        path, _ = _attest_authority_file_binding(
            repo_root,
            binding,
            diagnostic="IMPLEMENTATION_CLOSURE_BYTES_MISMATCH",
        )
        try:
            module = importlib.import_module(module_name)
        except Exception as error:
            _fail(
                "BLOCKED_OPERATOR_BINDING",
                "LOADED_OPERATOR_MODULE_IDENTITY_MISMATCH",
                f"{module_name}:{type(error).__name__}",
            )
        module_file = getattr(module, "__file__", None)
        spec_origin = getattr(getattr(module, "__spec__", None), "origin", None)
        if (
            module_file is None
            or Path(module_file).resolve() != path
            or spec_origin is None
            or Path(spec_origin).resolve() != path
            or type(getattr(module.__spec__, "loader", None)).__name__
            != binding.get("loader_type")
        ):
            _fail(
                "BLOCKED_OPERATOR_BINDING",
                "LOADED_OPERATOR_MODULE_IDENTITY_MISMATCH",
                module_name,
            )
        module_names.append(module_name)
    if tuple(module_names) != executor_custody_v2.REQUIRED_MODULE_NAMES or set(
        module_names
    ) != REQUIRED_IMPLEMENTATION_MODULE_NAMES:
        _fail("BLOCKED_CUSTODY", "RUNTIME_SOURCE_CLOSURE_INVALID")
    return authority, anchor_sha256


def _physical_trajectory_sha256(trajectory: np.ndarray) -> str:
    little = np.ascontiguousarray(trajectory.astype("<f8", copy=False))
    digest = hashlib.sha256()
    digest.update(_TRAJECTORY_DOMAIN)
    digest.update(struct.pack("<QQ", little.shape[0], little.shape[1]))
    digest.update(little.tobytes(order="C"))
    return digest.hexdigest()


def _load_npz_arrays(
    npz_path: Path,
    registry: Sequence[Any],
    expected_npz_sha256: str,
) -> dict[str, np.ndarray]:
    if not npz_path.is_file():
        _fail(
            "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
            "REQUIRED_OUTPUT_MISSING",
            str(npz_path),
        )
    raw = npz_path.read_bytes()
    if _sha256(raw) != expected_npz_sha256:
        _fail("BLOCKED_CUSTODY", "NPZ_SHA256_MISMATCH", str(npz_path))
    if not isinstance(registry, list):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "ARRAY_REGISTRY_INVALID")
    expected_ids = [f"array_{index:06d}" for index in range(len(registry))]
    registry_ids: list[str] = []
    by_id: dict[str, Mapping[str, Any]] = {}
    for item in registry:
        record = _require_exact_keys(
            item,
            {"array_id", "dtype", "shape", "raw_c_order_sha256"},
            diagnostic="ARRAY_REGISTRY_RECORD_INVALID",
        )
        array_id = record["array_id"]
        if not isinstance(array_id, str) or array_id in by_id:
            _fail("BLOCKED_RUN_IDENTITY", "DUPLICATE_PAYLOAD_IDENTITY", str(array_id))
        registry_ids.append(array_id)
        by_id[array_id] = record
    if registry_ids != expected_ids:
        _fail("BLOCKED_RUN_IDENTITY", "ARRAY_REGISTRY_ID_CLOSURE_MISMATCH")
    try:
        archive = zipfile.ZipFile(io.BytesIO(raw), mode="r")
        infos = archive.infolist()
    except zipfile.BadZipFile as error:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "NPZ_ARCHIVE_INVALID", str(error))
    names = [info.filename for info in infos]
    expected_names = [f"{array_id}.npy" for array_id in expected_ids]
    if names != expected_names or len(names) != len(set(names)):
        _fail("BLOCKED_RUN_IDENTITY", "NPZ_ARRAY_IDENTITY_CLOSURE_MISMATCH")
    arrays: dict[str, np.ndarray] = {}
    for info, array_id in zip(infos, expected_ids, strict=True):
        if info.compress_type != zipfile.ZIP_STORED or info.is_dir():
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "NPZ_MEMBER_ENCODING_INVALID", array_id)
        try:
            member = archive.read(info)
            array = np.lib.format.read_array(io.BytesIO(member), allow_pickle=False)
        except (ValueError, OSError) as error:
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "NPY_MEMBER_INVALID", str(error))
        record = by_id[array_id]
        if array.dtype.hasobject or array.dtype.kind not in "biufc":
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "NPY_DTYPE_FORBIDDEN", array_id)
        if array.dtype.str != record["dtype"] or list(array.shape) != record["shape"]:
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "NPY_SCHEMA_MISMATCH", array_id)
        canonical = np.ascontiguousarray(array)
        if _sha256(canonical.tobytes(order="C")) != record["raw_c_order_sha256"]:
            _fail("BLOCKED_CUSTODY", "NPY_RAW_SHA256_MISMATCH", array_id)
        if canonical.dtype.kind in "fc" and not np.all(np.isfinite(canonical)):
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_ARRAY_NONFINITE", array_id)
        arrays[array_id] = canonical
    return arrays


def _restore_payload_arrays(value: Any, arrays: Mapping[str, np.ndarray]) -> Any:
    reference_counts = {array_id: 0 for array_id in arrays}

    def restore(item: Any) -> Any:
        if isinstance(item, dict):
            if "$npz_array" in item:
                if set(item) != {"$npz_array"}:
                    _fail("BLOCKED_OBSERVABLE_SEMANTICS", "NPZ_REFERENCE_SCHEMA_INVALID")
                array_id = item["$npz_array"]
                if not isinstance(array_id, str) or array_id not in arrays:
                    _fail("BLOCKED_RUN_IDENTITY", "UNKNOWN_PAYLOAD_ARRAY_ID", str(array_id))
                reference_counts[array_id] += 1
                return arrays[array_id]
            return {key: restore(child) for key, child in item.items()}
        if isinstance(item, list):
            return [restore(child) for child in item]
        return item

    restored = restore(value)
    if any(count != 1 for count in reference_counts.values()):
        _fail("BLOCKED_RUN_IDENTITY", "PAYLOAD_ARRAY_REFERENCE_NOT_BIJECTIVE")
    return restored


def _load_role_payload(
    json_path: Path,
    npz_path: Path,
    *,
    expected_run_id: str,
    expected_json_sha256: str | None,
    expected_npz_sha256: str | None,
) -> tuple[dict[str, Any], str, str]:
    raw_json = json_path.read_bytes() if json_path.is_file() else b""
    if not raw_json:
        _fail(
            "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
            "REQUIRED_OUTPUT_MISSING",
            str(json_path),
        )
    json_sha = _sha256(raw_json)
    if expected_json_sha256 is not None and json_sha != expected_json_sha256:
        _fail("BLOCKED_CUSTODY", "JSON_SHA256_MISMATCH", expected_run_id)
    envelope = _load_json_object(json_path)
    if raw_json != _canonical_json_bytes(envelope):
        _fail("BLOCKED_CUSTODY", "RUN_PAYLOAD_JSON_NOT_CANONICAL", expected_run_id)
    envelope = dict(
        _require_exact_keys(
            envelope,
            {
                "schema_id",
                "npz_schema_id",
                "output_schema_version",
                "implementation_id",
                "role_id",
                "array_registry",
                "npz_sha256",
                "payload",
            },
            diagnostic="RUN_PAYLOAD_ENVELOPE_SCHEMA_INVALID",
        )
    )
    expected_envelope = {
        "schema_id": RUN_PAYLOAD_JSON_SCHEMA_ID,
        "npz_schema_id": RUN_PAYLOAD_NPZ_SCHEMA_ID,
        "output_schema_version": "v0",
        "implementation_id": EXPECTED_IMPLEMENTATION_ID,
        "role_id": expected_run_id,
    }
    for key, expected in expected_envelope.items():
        if envelope[key] != expected:
            _fail("BLOCKED_RUN_IDENTITY", "ROLE_PAYLOAD_IDENTITY_MISMATCH", f"{expected_run_id}:{key}")
    npz_sha = _sha256_path(
        npz_path, missing_result="BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
    )
    if expected_npz_sha256 is not None and npz_sha != expected_npz_sha256:
        _fail("BLOCKED_CUSTODY", "NPZ_SHA256_MISMATCH", expected_run_id)
    if envelope["npz_sha256"] != npz_sha:
        _fail("BLOCKED_CUSTODY", "ENVELOPE_NPZ_SHA256_MISMATCH", expected_run_id)
    arrays = _load_npz_arrays(npz_path, envelope["array_registry"], npz_sha)
    payload = _restore_payload_arrays(envelope["payload"], arrays)
    if not isinstance(payload, dict):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "ROLE_PAYLOAD_SCHEMA_INVALID", expected_run_id)
    return payload, json_sha, npz_sha


def _validate_frozen_documents(
    repo_root: Path,
    matrix: Mapping[str, Any],
    manifest: Mapping[str, Any],
    authority: Mapping[str, Any],
) -> tuple[list[Mapping[str, Any]], Path]:
    try:
        matrix_diagnostics = executor_v2.strict_validate_matrix(matrix, authority)
    except (AttributeError, KeyError, TypeError, ValueError) as error:
        _fail(
            "BLOCKED_CUSTODY",
            "RUN_MATRIX_FULL_RECORD_IDENTITY_UNAVAILABLE",
            f"{type(error).__name__}:{error}",
        )
    if matrix_diagnostics:
        _fail("BLOCKED_RUN_IDENTITY", matrix_diagnostics[0])
    records = matrix.get("records")
    if not isinstance(records, list) or len(records) != 6:
        _fail("BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH")
    if matrix.get("expected_run_id_order") != list(EXPECTED_RUN_IDS):
        _fail("BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH")
    if [record.get("run_id") for record in records] != list(EXPECTED_RUN_IDS):
        _fail("BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH")
    if manifest.get("output_root") != EXPECTED_OUTPUT_ROOT_RELATIVE_PATH:
        _fail("BLOCKED_CUSTODY", "INSTRUMENTED_OUTPUT_ROOT_IDENTITY_MISMATCH")
    output_root = (repo_root / EXPECTED_OUTPUT_ROOT_RELATIVE_PATH).resolve()
    canonical_root = (repo_root / EXPECTED_CANONICAL_ROOT_RELATIVE_PATH).resolve()
    if output_root == canonical_root or output_root in canonical_root.parents or canonical_root in output_root.parents:
        _fail("BLOCKED_CUSTODY", "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL")
    outputs = manifest.get("outputs")
    if not isinstance(outputs, list) or len(outputs) != 6:
        _fail("BLOCKED_RUN_IDENTITY", "EXPECTED_PAYLOAD_ID_CLOSURE_MISMATCH")
    by_manifest_run = {item.get("run_id"): item for item in outputs if isinstance(item, dict)}
    if set(by_manifest_run) != set(EXPECTED_RUN_IDS) or len(by_manifest_run) != 6:
        _fail("BLOCKED_RUN_IDENTITY", "DUPLICATE_PAYLOAD_IDENTITY")
    json_paths: list[str] = []
    npz_paths: list[str] = []
    for ordinal, (record, run_id) in enumerate(zip(records, EXPECTED_RUN_IDS, strict=True)):
        if record.get("execution_ordinal_zero_based") != ordinal:
            _fail("BLOCKED_RUN_IDENTITY", "RUN_EXECUTION_ORDINAL_MISMATCH", run_id)
        if record.get("implementation_id") != EXPECTED_IMPLEMENTATION_ID or record.get("implementation_sha256") != EXPECTED_IMPLEMENTATION_SHA256:
            _fail("BLOCKED_CUSTODY", "IMPLEMENTATION_IDENTITY_MISMATCH", run_id)
        # V2 separates physics, runtime-source, and complete execution identity.
        try:
            closure_digest = authority["runtime_source_closure_sha256"]
            physical_core = executor_v2.build_physical_configuration_core(
                record, closure_digest
            )
            scientific_core = executor_v2.build_scientific_input_core(
                record, closure_digest
            )
            physical_hash = executor_v2.physical_configuration_hash(
                physical_core
            )
            scientific_hash = executor_v2.scientific_input_hash(scientific_core)
            complete_hash = executor_v2.complete_execution_identity_sha256(
                record, closure_digest
            )
            full_hash = executor_v2.full_record_identity_sha256(record)
        except (AttributeError, KeyError, TypeError, ValueError) as error:
            _fail(
                "BLOCKED_RUN_IDENTITY",
                "RUN_RECORD_IDENTITY_RECOMPUTATION_FAILED",
                f"{run_id}:{type(error).__name__}",
            )
        expected_hashes = {
            "expected_physical_configuration_sha256_by_run_id": physical_hash,
            "expected_scientific_input_sha256_by_run_id": scientific_hash,
            "expected_complete_execution_sha256_by_run_id": complete_hash,
            "expected_full_record_sha256_by_run_id": full_hash,
        }
        if any(
            authority[field][run_id] != actual
            for field, actual in expected_hashes.items()
        ):
            _fail("BLOCKED_RUN_IDENTITY", "RUN_RECORD_IDENTITY_MISMATCH", run_id)
        if not physical_hash or not scientific_hash or not complete_hash or not full_hash:
            _fail("BLOCKED_RUN_IDENTITY", "RUN_RECORD_IDENTITY_RECOMPUTATION_FAILED", run_id)
        manifest_record = by_manifest_run[run_id]
        for field in (
            "run_id",
            "input_hash",
            "instrumentation_enabled",
            "json_relative_output_path",
            "npz_relative_output_path",
            "paired_run_id",
            "parent_canonical_run_id",
            "scientific_row_id",
            "implementation_id",
            "implementation_sha256",
            "runtime_source_closure_sha256",
            "complete_execution_identity_sha256",
            "output_schema_version",
        ):
            if manifest_record.get(field) != record.get(field):
                _fail("BLOCKED_RUN_IDENTITY", "MANIFEST_MATRIX_IDENTITY_MISMATCH", f"{run_id}:{field}")
        json_paths.append(str(record.get("json_relative_output_path")))
        npz_paths.append(str(record.get("npz_relative_output_path")))
        for path_field in (
            "json_relative_output_path",
            "npz_relative_output_path",
        ):
            resolved_payload_path = (repo_root / str(record[path_field])).resolve()
            if resolved_payload_path.parent != output_root:
                _fail(
                    "BLOCKED_CUSTODY",
                    "PAYLOAD_PATH_ESCAPES_EXPERIMENT_ROOT",
                    f"{run_id}:{path_field}",
                )
        parent_path = repo_root / str(record.get("parent_canonical_output_path"))
        if _sha256_path(parent_path) != record.get("parent_canonical_output_sha256"):
            _fail("BLOCKED_CUSTODY", "PARENT_CANONICAL_OUTPUT_SHA256_MISMATCH", run_id)
        parent = _load_json_object(parent_path, missing_result="BLOCKED_CUSTODY")
        for parent_field, record_field in (
            ("run_id", "parent_canonical_run_id"),
            ("input_hash", "parent_canonical_input_hash"),
            ("scientific_row_id", "scientific_row_id"),
        ):
            if parent.get(parent_field) != record.get(record_field):
                _fail("BLOCKED_RUN_IDENTITY", "WRONG_PARENT_CANONICAL_IDENTITY", f"{run_id}:{parent_field}")
    by_id = {str(record["run_id"]): record for record in records}
    for instrumented_id, control_id in PAIR_IDS:
        closure_digest = authority["runtime_source_closure_sha256"]
        instrumented_core = executor_v2.build_physical_configuration_core(
            by_id[instrumented_id], closure_digest
        )
        control_core = executor_v2.build_physical_configuration_core(
            by_id[control_id], closure_digest
        )
        if executor_v2.physical_configuration_hash(
            instrumented_core
        ) != executor_v2.physical_configuration_hash(control_core):
            _fail(
                "BLOCKED_RUN_IDENTITY",
                "PHYSICAL_CONFIGURATION_PAIR_MISMATCH",
                instrumented_id,
            )
    if len(set(json_paths + npz_paths)) != 12:
        _fail("BLOCKED_RUN_IDENTITY", "DUPLICATE_PAYLOAD_IDENTITY")
    expected_json_map = {record["json_relative_output_path"]: record["run_id"] for record in records}
    expected_npz_map = {record["npz_relative_output_path"]: record["run_id"] for record in records}
    if manifest.get("json_relative_output_path_to_run_id") != expected_json_map or manifest.get("npz_relative_output_path_to_run_id") != expected_npz_map:
        _fail("BLOCKED_RUN_IDENTITY", "PAYLOAD_PATH_MAP_MISMATCH")
    expected_json_filename_map = {
        record["json_safe_filename"]: record["run_id"] for record in records
    }
    expected_npz_filename_map = {
        record["npz_safe_filename"]: record["run_id"] for record in records
    }
    if (
        manifest.get("json_safe_filename_to_run_id")
        != expected_json_filename_map
        or manifest.get("npz_safe_filename_to_run_id")
        != expected_npz_filename_map
    ):
        _fail("BLOCKED_RUN_IDENTITY", "PAYLOAD_FILENAME_MAP_MISMATCH")
    auxiliary = manifest.get("auxiliary_execution_files")
    expected_aux = {
        f"{EXPECTED_OUTPUT_ROOT_RELATIVE_PATH}/EXECUTION-STARTED.json",
        f"{EXPECTED_OUTPUT_ROOT_RELATIVE_PATH}/MATRIX-RESULT.json",
    }
    if not isinstance(auxiliary, list) or {item.get("relative_output_path") for item in auxiliary if isinstance(item, dict)} != expected_aux:
        _fail("BLOCKED_RUN_IDENTITY", "AUXILIARY_OUTPUT_IDENTITY_MISMATCH")
    return records, output_root


def _validate_source_custody(repo_root: Path) -> None:
    if _sha256_path(repo_root / EXPECTED_IMPLEMENTATION_RELATIVE_PATH) != EXPECTED_IMPLEMENTATION_SHA256:
        _fail("BLOCKED_CUSTODY", "IMPLEMENTATION_IDENTITY_MISMATCH")
    for relative_path, expected in EXPECTED_BOUND_SOURCES.items():
        if _sha256_path(repo_root / relative_path) != expected:
            _fail("BLOCKED_OPERATOR_BINDING", "LOADED_OPERATOR_MODULE_IDENTITY_MISMATCH", relative_path)


def _unpack_state(vector: np.ndarray) -> dict[str, np.ndarray]:
    result: dict[str, np.ndarray] = {}
    offset = 0
    for key in ("theta", "p", "phi2", "P2", "phi3", "P3"):
        result[key] = vector[offset : offset + LATTICE_SIZE].copy()
        offset += LATTICE_SIZE
    for key in ("psi_plus", "psi_minus"):
        real = vector[offset : offset + 4 * LATTICE_SIZE].reshape(LATTICE_SIZE, 4)
        offset += 4 * LATTICE_SIZE
        imag = vector[offset : offset + 4 * LATTICE_SIZE].reshape(LATTICE_SIZE, 4)
        offset += 4 * LATTICE_SIZE
        result[key] = real + 1j * imag
    if offset != PACKED_WIDTH:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "PACKED_STATE_LAYOUT_MISMATCH")
    return result


def _block_maxima(defect: np.ndarray) -> dict[str, float]:
    return {
        block_id: float(np.max(np.abs(defect[start * LATTICE_SIZE : stop * LATTICE_SIZE])))
        for block_id, (start, stop) in BLOCK_SPANS_IN_N.items()
    }


def _normalized_and_shares(
    defect: np.ndarray, tolerance: float
) -> tuple[dict[str, float], dict[str, float]]:
    raw = _block_maxima(defect)
    denominator = max(tolerance, GAMMA64)
    normalized = {block_id: raw[block_id] / denominator for block_id in BLOCK_IDS}
    total = sum(normalized.values()) + GAMMA64
    shares = {block_id: normalized[block_id] / total for block_id in BLOCK_IDS}
    return normalized, shares


def _validate_block_mapping(
    observed: Any,
    expected: Mapping[str, float],
    name: str,
) -> None:
    mapping = _require_exact_keys(observed, BLOCK_IDS, diagnostic="UNKNOWN_NINTH_SOLVER_BLOCK")
    for block_id in BLOCK_IDS:
        actual = _finite_float(mapping[block_id], f"{name}.{block_id}")
        if actual != expected[block_id]:
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_SUMMARY_RECOMPUTATION_MISMATCH", f"{name}.{block_id}")


def _validate_payload_identity(payload: Mapping[str, Any], record: Mapping[str, Any]) -> tuple[np.ndarray, np.ndarray]:
    required = {
        "schema_id",
        "implementation_id",
        "historical_evolution_module",
        "historical_pack_module",
        "bound_source_sha256",
        "role_id",
        "row_id",
        "instrumentation_enabled",
        "model",
        "configuration",
        "initial_state_reconstruction",
        "times",
        "physical_trajectory",
        "physical_trajectory_sha256",
        "all_steps_converged",
        "maximum_iterations_used",
        "maximum_solver_residual",
        "raw_events",
        "metrics",
    }
    _require_exact_keys(payload, required, diagnostic="ROLE_PAYLOAD_SCHEMA_INVALID")
    run_id = str(record["run_id"])
    expected_scalars = {
        "schema_id": RUN_ROLE_PAYLOAD_SCHEMA_ID,
        "implementation_id": EXPECTED_IMPLEMENTATION_ID,
        "role_id": run_id,
        "row_id": record["scientific_row_id"],
        "instrumentation_enabled": record["instrumentation_enabled"],
        "model": record["model_class"],
    }
    for key, expected in expected_scalars.items():
        if payload[key] != expected or type(payload[key]) is not type(expected):
            _fail("BLOCKED_RUN_IDENTITY", "ROLE_PAYLOAD_IDENTITY_MISMATCH", f"{run_id}:{key}")
    if payload["bound_source_sha256"] != EXPECTED_BOUND_SOURCES:
        _fail("BLOCKED_OPERATOR_BINDING", "LOADED_OPERATOR_MODULE_IDENTITY_MISMATCH", run_id)
    configuration = _require_exact_keys(
        payload["configuration"],
        {
            "N",
            "a",
            "requested_dt",
            "effective_dt",
            "duration",
            "steps",
            "solver_tolerance",
            "max_iterations",
            "mass",
            "charge",
            "row",
        },
        diagnostic="CONFIGURATION_SCHEMA_INVALID",
    )
    expected_configuration = {
        "N": record["n"],
        "requested_dt": record["dt"],
        "duration": record["duration"],
        "steps": POSTINITIAL_STEPS,
        "solver_tolerance": record["tolerance"],
        "max_iterations": record["max_iterations"],
        "row": record["row"],
    }
    for key, expected in expected_configuration.items():
        if configuration[key] != expected or type(configuration[key]) is not type(expected):
            _fail("BLOCKED_RUN_IDENTITY", "ROLE_CONFIGURATION_IDENTITY_MISMATCH", f"{run_id}:{key}")
    if configuration["effective_dt"] != record["dt"] or configuration["a"] != 1.0 / record["n"]:
        _fail("BLOCKED_RUN_IDENTITY", "ROLE_CONFIGURATION_IDENTITY_MISMATCH", run_id)
    expected_mass = float(record["row"]["MU_MASS_DOMAIN"])
    expected_charge = float(record["row"]["ETA_Q"]) * expected_mass
    if configuration["mass"] != expected_mass or configuration["charge"] != expected_charge:
        _fail("BLOCKED_RUN_IDENTITY", "ROLE_CONFIGURATION_IDENTITY_MISMATCH", run_id)
    times = _array(payload["times"], f"{run_id}.times", shape=(CHECKPOINT_COUNT,))
    expected_times = np.arange(CHECKPOINT_COUNT, dtype=np.float64) * float(record["dt"])
    _assert_exact(times, expected_times, "TIME_GRID_IDENTITY_MISMATCH", run_id)
    trajectory = _array(
        payload["physical_trajectory"],
        f"{run_id}.physical_trajectory",
        shape=(CHECKPOINT_COUNT, PACKED_WIDTH),
    )
    trajectory_sha = _physical_trajectory_sha256(trajectory)
    if payload["physical_trajectory_sha256"] != trajectory_sha:
        _fail("BLOCKED_CUSTODY", "PHYSICAL_TRAJECTORY_SHA256_MISMATCH", run_id)
    return times, trajectory


def _validate_exchange_event(
    event: Any,
    step: int,
    previous_p: np.ndarray,
    current_p: np.ndarray,
    spacing: float,
) -> tuple[float, float, float, np.ndarray]:
    fields = {
        "step",
        "time",
        "x_field_cell_contribution",
        "x_matter_cell_contribution",
        "x_field_integral",
        "x_matter_integral",
        "remainder_integral",
        "conditioning_numerator",
        "gamma64_floor",
        "kappa",
    }
    event = _require_exact_keys(event, fields, diagnostic="EXCHANGE_EVENT_SCHEMA_INVALID")
    if event["step"] != step:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "EVENT_STEP_IDENTITY_MISMATCH", f"exchange:{step}")
    field_cell = _array(event["x_field_cell_contribution"], "x_field_cell", shape=(LATTICE_SIZE,))
    matter_cell = _array(event["x_matter_cell_contribution"], "x_matter_cell", shape=(LATTICE_SIZE,))
    expected_field_cell = (current_p**2 - previous_p**2) / (2.0 * spacing)
    _assert_exact(
        field_cell,
        expected_field_cell,
        "RAW_EXCHANGE_SOURCE_BINDING_MISMATCH",
        f"field:{step}",
    )
    field = float(np.sum(field_cell, dtype=np.float64))
    matter = float(np.sum(matter_cell, dtype=np.float64))
    # Decision-bearing values are the independently summed cell arrays.
    remainder = field + matter
    # Stored scalar summaries are advisory v0 fields.  Validate only their
    # schema/finite domain; never use them to judge or override the raw cells.
    for key in (
        "x_field_integral",
        "x_matter_integral",
        "remainder_integral",
        "conditioning_numerator",
        "gamma64_floor",
        "kappa",
    ):
        _finite_float(event[key], f"legacy.exchange.{key}")
    return field, matter, remainder, matter_cell


def _validate_terminal_event(event: Any, step: int, tolerance: float) -> tuple[np.ndarray, dict[str, float]]:
    event = _require_exact_keys(
        event,
        {
            "packed_terminal_equation_defect",
            "packed_real_block_maxima",
            "normalized_block_magnitudes",
            "dominance_share_by_block",
            "step",
            "time",
        },
        diagnostic="TERMINAL_BLOCK_EVENT_SCHEMA_INVALID",
    )
    if event["step"] != step:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "EVENT_STEP_IDENTITY_MISMATCH", f"terminal:{step}")
    defect = _array(event["packed_terminal_equation_defect"], "terminal_defect", shape=(PACKED_WIDTH,))
    raw = _block_maxima(defect)
    normalized, shares = _normalized_and_shares(defect, tolerance)
    _validate_block_mapping(event["packed_real_block_maxima"], raw, "terminal.raw")
    _validate_block_mapping(event["normalized_block_magnitudes"], normalized, "terminal.normalized")
    _validate_block_mapping(event["dominance_share_by_block"], shares, "terminal.share")
    return defect, shares


def _validate_solver_step(event: Any, step: int, tolerance: float) -> None:
    event = _require_exact_keys(
        event,
        {
            "step",
            "time",
            "requested_tolerance",
            "terminal_solver_residual",
            "terminal_update_residual",
            "terminal_equation_residual",
            "stopping_reason",
            "step_accepted",
            "converged",
            "iteration_count",
            "terminal_iteration_state_index",
            "iteration_events",
            "algorithm",
            "damping",
            "line_search",
            "jacobian",
            "preconditioner",
            "conditioning_estimate",
        },
        diagnostic="SOLVER_STEP_SCHEMA_INVALID",
    )
    if event["step"] != step or event["requested_tolerance"] != tolerance:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "EVENT_STEP_IDENTITY_MISMATCH", f"solver:{step}")
    iteration_count = _exact_int(event["iteration_count"], "iteration_count", minimum=1)
    if iteration_count > 80 or event["terminal_iteration_state_index"] != iteration_count:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "ITERATION_HISTORY_IDENTITY_MISMATCH", str(step))
    iteration_events = event["iteration_events"]
    if not isinstance(iteration_events, list) or len(iteration_events) != iteration_count:
        _fail("BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "REQUIRED_ITERATION_HISTORY_MISSING", str(step))
    last_update = None
    for index, iteration_event in enumerate(iteration_events):
        item = _require_exact_keys(
            iteration_event,
            {
                "iteration",
                "update_ordinal",
                "packed_update_defect",
                "packed_real_block_maxima",
                "maximum_absolute_update_defect",
                "normalized_block_magnitudes",
                "dominance_share_by_block",
            },
            diagnostic="SOLVER_ITERATION_EVENT_SCHEMA_INVALID",
        )
        if item["iteration"] != index or item["update_ordinal"] != index + 1:
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "ITERATION_HISTORY_IDENTITY_MISMATCH", f"{step}:{index}")
        defect = _array(item["packed_update_defect"], "packed_update_defect", shape=(PACKED_WIDTH,))
        raw = _block_maxima(defect)
        normalized, shares = _normalized_and_shares(defect, tolerance)
        _validate_block_mapping(item["packed_real_block_maxima"], raw, "iteration.raw")
        _validate_block_mapping(item["normalized_block_magnitudes"], normalized, "iteration.normalized")
        _validate_block_mapping(item["dominance_share_by_block"], shares, "iteration.share")
        maximum = float(np.max(np.abs(defect)))
        if item["maximum_absolute_update_defect"] != maximum:
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_SUMMARY_RECOMPUTATION_MISMATCH", f"iteration.maximum:{step}:{index}")
        last_update = maximum
    equation_residual = _finite_float(event["terminal_equation_residual"], "terminal_equation_residual")
    update_residual = _finite_float(event["terminal_update_residual"], "terminal_update_residual")
    solver_residual = _finite_float(event["terminal_solver_residual"], "terminal_solver_residual")
    if last_update != update_residual or max(update_residual, equation_residual) != solver_residual:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_SUMMARY_RECOMPUTATION_MISMATCH", f"solver residual:{step}")
    if event["algorithm"] != "MONOLITHIC_PICARD_FIXED_POINT_IMPLICIT_MIDPOINT" or event["step_accepted"] is not True:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "SOLVER_ALGORITHM_CONTRACT_MISMATCH", str(step))
    if type(event["converged"]) is not bool:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "SOLVER_ALGORITHM_CONTRACT_MISMATCH", str(step))
    expected_reason = (
        "TOLERANCE_REACHED" if event["converged"] else "MAX_ITERATIONS_REACHED"
    )
    if event["stopping_reason"] != expected_reason:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "SOLVER_ALGORITHM_CONTRACT_MISMATCH", str(step))
    if event["converged"] and update_residual > tolerance:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "SOLVER_STOPPING_RULE_MISMATCH", str(step))


def _validate_spatial_event(
    event: Any,
    step: int,
    spacing: float,
    terminal_defect: np.ndarray,
) -> dict[str, np.ndarray | float]:
    fields = {
        "step",
        "time",
        "gauss_residual_field",
        "continuity_residual_field",
        "longitudinal_theta_equation_defect",
        "longitudinal_p_equation_defect",
        "gauss_maximum_absolute",
        "continuity_maximum_absolute",
        "gauss_grid_weighted_l2",
        "continuity_grid_weighted_l2",
        "gauss_lowest_index_argmax",
        "continuity_lowest_index_argmax",
        "longitudinal_theta_grid_weighted_l2",
        "longitudinal_p_grid_weighted_l2",
        "longitudinal_theta_lowest_index_argmax",
        "longitudinal_p_lowest_index_argmax",
    }
    event = _require_exact_keys(event, fields, diagnostic="SPATIAL_EVENT_SCHEMA_INVALID")
    if event["step"] != step:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "EVENT_STEP_IDENTITY_MISMATCH", f"spatial:{step}")
    arrays = {
        key: _array(event[key], key, shape=(LATTICE_SIZE,))
        for key in (
            "gauss_residual_field",
            "continuity_residual_field",
            "longitudinal_theta_equation_defect",
            "longitudinal_p_equation_defect",
        )
    }
    theta_expected = terminal_defect[0:LATTICE_SIZE]
    p_expected = terminal_defect[LATTICE_SIZE : 2 * LATTICE_SIZE]
    _assert_exact(arrays["longitudinal_theta_equation_defect"], theta_expected, "LONGITUDINAL_DEFECT_SOURCE_MISMATCH", f"theta:{step}")
    _assert_exact(arrays["longitudinal_p_equation_defect"], p_expected, "LONGITUDINAL_DEFECT_SOURCE_MISMATCH", f"p:{step}")
    summary_specs = (
        ("gauss", arrays["gauss_residual_field"]),
        ("continuity", arrays["continuity_residual_field"]),
        ("longitudinal_theta", arrays["longitudinal_theta_equation_defect"]),
        ("longitudinal_p", arrays["longitudinal_p_equation_defect"]),
    )
    for prefix, array in summary_specs:
        if prefix in {"gauss", "continuity"}:
            maximum_key = f"{prefix}_maximum_absolute"
            if event[maximum_key] != float(np.max(np.abs(array))):
                _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_SUMMARY_RECOMPUTATION_MISMATCH", f"{maximum_key}:{step}")
        l2_key = f"{prefix}_grid_weighted_l2"
        argmax_key = f"{prefix}_lowest_index_argmax"
        expected_l2 = float(math.sqrt(spacing * float(np.sum(array**2))))
        if event[l2_key] != expected_l2 or event[argmax_key] != int(np.argmax(np.abs(array))):
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "RAW_SUMMARY_RECOMPUTATION_MISMATCH", f"{prefix}:{step}")
    return {**arrays, "gauss_maximum_absolute": float(np.max(np.abs(arrays["gauss_residual_field"]))), "continuity_maximum_absolute": float(np.max(np.abs(arrays["continuity_residual_field"])))}


def _expected_forward_wilson_matrix(spacing: float) -> np.ndarray:
    i2 = np.eye(2, dtype=np.complex128)
    sigma1 = np.array([[0, 1], [1, 0]], dtype=np.complex128)
    sigma2 = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
    sigma3 = np.array([[1, 0], [0, -1]], dtype=np.complex128)
    gamma0 = np.kron(sigma3, i2)
    gamma1 = np.kron(1j * sigma2, i2)
    beta = gamma0
    alpha1 = gamma0 @ gamma1
    return np.ascontiguousarray((-1j * alpha1 - beta) / (2.0 * spacing))


def _independent_charge_density(
    state: Mapping[str, np.ndarray], charge: float
) -> np.ndarray:
    density = np.zeros(LATTICE_SIZE, dtype=np.float64)
    for sigma, species in ((1, "psi_plus"), (-1, "psi_minus")):
        psi = state[species]
        species_density = np.sum(np.abs(psi) ** 2, axis=1).real
        density += sigma * charge * species_density
    return density


def _validate_operator_outputs(
    outputs: Any,
    operator_inputs: Mapping[str, Any],
    previous_state: Mapping[str, np.ndarray],
    current_state: Mapping[str, np.ndarray],
    charge: float,
    spacing: float,
    step: int,
) -> np.ndarray:
    base = {
        "time_centered_theta",
        "backward_shift_p_previous",
        "backward_shift_p_current",
        "backward_shift_grad_theta_midpoint",
        "grad_theta_midpoint_registered",
        "forward_wilson_matrix",
        "wilson_r",
        "periodic_shift_rule",
        "time_centering_rule",
        "grad_theta_midpoint_recomputed",
        "grad_theta_recomputation_byte_identical",
    }
    per_species = {
        f"{species}_{suffix}"
        for species in ("psi_plus", "psi_minus")
        for suffix in (
            "next_periodic",
            "gauge_phase",
            "forward_transport",
            "link_bilinear",
            "grad_contribution",
        )
    }
    outputs = _require_exact_keys(outputs, base | per_species, diagnostic="DISCRETE_OPERATOR_OUTPUT_SCHEMA_INVALID")
    midpoint_theta = 0.5 * (previous_state["theta"] + current_state["theta"])
    _assert_exact(_array(outputs["time_centered_theta"], "time_centered_theta", shape=(LATTICE_SIZE,)), midpoint_theta, "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"theta:{step}")
    checks = {
        "backward_shift_p_previous": np.roll(operator_inputs["p_previous"], 1),
        "backward_shift_p_current": np.roll(operator_inputs["p_current"], 1),
        "backward_shift_grad_theta_midpoint": np.roll(operator_inputs["grad_theta_midpoint"], 1),
        "grad_theta_midpoint_registered": operator_inputs["grad_theta_midpoint"],
    }
    for key, expected in checks.items():
        _assert_exact(_array(outputs[key], key, shape=(LATTICE_SIZE,)), expected, "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"{key}:{step}")
    forward = _array(outputs["forward_wilson_matrix"], "forward_wilson_matrix", shape=(4, 4), dtype=np.dtype("<c16"))
    _assert_exact(forward, _expected_forward_wilson_matrix(spacing), "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"forward_matrix:{step}")
    if outputs["wilson_r"] != 1.0 or outputs["periodic_shift_rule"] != "NUMPY_ROLL_AXIS0" or outputs["time_centering_rule"] != "ARITHMETIC_MIDPOINT":
        _fail("BLOCKED_OPERATOR_BINDING", "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"operator policy:{step}")
    recomputed = np.zeros(LATTICE_SIZE, dtype=np.float64)
    for sigma, species in ((1, "psi_plus"), (-1, "psi_minus")):
        psi = 0.5 * (previous_state[species] + current_state[species])
        next_psi = np.roll(psi, -1, axis=0)
        phase = np.exp(1j * sigma * charge * midpoint_theta)
        transported = phase[:, None] * next_psi
        bilinear = np.einsum("ni,ij,nj->n", psi.conj(), forward, transported)
        contribution = 2.0 * spacing * np.real(1j * sigma * charge * bilinear)
        expected_arrays = {
            f"{species}_next_periodic": next_psi,
            f"{species}_gauge_phase": phase,
            f"{species}_forward_transport": transported,
            f"{species}_link_bilinear": bilinear,
            f"{species}_grad_contribution": contribution,
        }
        for key, expected in expected_arrays.items():
            dtype = np.dtype("<c16") if np.iscomplexobj(expected) else np.dtype("<f8")
            shape = expected.shape
            _assert_exact(_array(outputs[key], key, shape=shape, dtype=dtype), np.ascontiguousarray(expected), "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"{key}:{step}")
        recomputed += contribution
    _assert_exact(_array(outputs["grad_theta_midpoint_recomputed"], "grad_theta_midpoint_recomputed", shape=(LATTICE_SIZE,)), recomputed, "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"grad recomputed:{step}")
    registered_current = operator_inputs["grad_theta_midpoint"]
    computed_byte_identity = (
        recomputed.dtype == registered_current.dtype
        and recomputed.shape == registered_current.shape
        and recomputed.tobytes(order="C")
        == registered_current.tobytes(order="C")
    )
    supplied_byte_identity = outputs[
        "grad_theta_recomputation_byte_identical"
    ]
    if (
        type(supplied_byte_identity) is not bool
        or supplied_byte_identity != computed_byte_identity
    ):
        _fail(
            "BLOCKED_OPERATOR_BINDING",
            "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
            f"grad byte flag:{step}",
        )
    # Do not require the two currents to agree.  Their independently verified
    # disagreement is the decision-bearing H_C signal.
    # Return the value independently reconstructed from the per-species Dirac
    # link bilinears.  H_C path B consumes this array, never the registered
    # Maxwell-source array or its supplied equality Boolean.
    return recomputed


def _validate_closure_event(
    event: Any,
    step: int,
    trajectory: np.ndarray,
    spatial: Mapping[str, Any],
    terminal_defect: np.ndarray,
    configuration: Mapping[str, Any],
) -> dict[str, np.ndarray | float]:
    closure_keys = {
        "step",
        "time",
        "operator_inputs",
        "actual_discrete_operator_outputs",
        "p_previous",
        "p_current",
        "rho_previous",
        "rho_current",
        "grad_theta_midpoint",
        "gauss_previous",
        "gauss_current",
        "p_equation_defect",
        "continuity_residual",
        "p_defect_divergence",
        "continuity_increment",
        "closure_q",
        "roundoff_scale",
        "roundoff_bound",
        "roundoff_bound_ratio",
        "gamma_operation_count",
        "gamma32",
    }
    event = _require_exact_keys(event, closure_keys, diagnostic="DISCRETE_CLOSURE_EVENT_SCHEMA_INVALID")
    if event["step"] != step:
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "EVENT_STEP_IDENTITY_MISMATCH", f"closure:{step}")
    inputs = _require_exact_keys(
        event["operator_inputs"],
        {"p_previous", "p_current", "rho_previous", "rho_current", "grad_theta_midpoint", "a", "dt"},
        diagnostic="DISCRETE_OPERATOR_INPUT_SCHEMA_INVALID",
    )
    raw_inputs = {key: _array(inputs[key], key, shape=(LATTICE_SIZE,)) for key in ("p_previous", "p_current", "rho_previous", "rho_current", "grad_theta_midpoint")}
    spacing = _finite_float(inputs["a"], "operator_inputs.a", positive=True)
    dt = _finite_float(inputs["dt"], "operator_inputs.dt", positive=True)
    if spacing != configuration["a"] or dt != configuration["effective_dt"]:
        _fail("BLOCKED_OPERATOR_BINDING", "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"spacing/time:{step}")
    previous_state = _unpack_state(trajectory[step - 1])
    current_state = _unpack_state(trajectory[step])
    _assert_exact(raw_inputs["p_previous"], previous_state["p"], "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"p_previous:{step}")
    _assert_exact(raw_inputs["p_current"], current_state["p"], "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"p_current:{step}")
    charge = float(configuration["charge"])
    _assert_exact(
        raw_inputs["rho_previous"],
        _independent_charge_density(previous_state, charge),
        "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
        f"rho_previous:{step}",
    )
    _assert_exact(
        raw_inputs["rho_current"],
        _independent_charge_density(current_state, charge),
        "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
        f"rho_current:{step}",
    )
    independently_recomputed_current = _validate_operator_outputs(
        event["actual_discrete_operator_outputs"],
        raw_inputs,
        previous_state,
        current_state,
        charge,
        spacing,
        step,
    )
    p0 = raw_inputs["p_previous"]
    p1 = raw_inputs["p_current"]
    rho0 = raw_inputs["rho_previous"]
    rho1 = raw_inputs["rho_current"]
    grad = raw_inputs["grad_theta_midpoint"]
    gauss0 = np.roll(p0, 1) - p0 + spacing * rho0
    gauss1 = np.roll(p1, 1) - p1 + spacing * rho1
    rp = p1 - p0 + dt * grad
    continuity = (rho1 - rho0) / dt + (grad - np.roll(grad, 1)) / spacing
    divergence = np.roll(rp, 1) - rp
    increment = spacing * dt * continuity
    q = (gauss1 - gauss0) - divergence - increment
    # The exact legacy-Q intermediates remain an operator-consistency gate.
    # The old gamma32 scale, bound, ratio, and operation-count convention are
    # advisory schema fields only in v2 and cannot block or support H_C.
    recomputed = {
        "p_previous": p0,
        "p_current": p1,
        "rho_previous": rho0,
        "rho_current": rho1,
        "grad_theta_midpoint": grad,
        "gauss_previous": gauss0,
        "gauss_current": gauss1,
        "p_equation_defect": rp,
        "continuity_residual": continuity,
        "p_defect_divergence": divergence,
        "continuity_increment": increment,
        "closure_q": q,
    }
    for key, expected in recomputed.items():
        _assert_exact(_array(event[key], key, shape=(LATTICE_SIZE,)), np.ascontiguousarray(expected), "LEGACY_Q_OPERATOR_GATE_INVALID", f"{key}:{step}")
    for legacy_field in (
        "roundoff_scale",
        "roundoff_bound",
        "roundoff_bound_ratio",
    ):
        _array(event[legacy_field], legacy_field, shape=(LATTICE_SIZE,))
    _exact_int(
        event["gamma_operation_count"],
        "legacy.gamma_operation_count",
        minimum=1,
    )
    _finite_float(event["gamma32"], "legacy.gamma32", positive=True)
    _assert_exact(gauss1, spatial["gauss_residual_field"], "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"gauss spatial:{step}")
    _assert_exact(continuity, spatial["continuity_residual_field"], "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED", f"continuity spatial:{step}")
    direct_p = terminal_defect[LATTICE_SIZE : 2 * LATTICE_SIZE]
    return {
        **raw_inputs,
        "continuity_current_midpoint_independently_recomputed": (
            independently_recomputed_current
        ),
        "maxwell_source_midpoint_registered": raw_inputs[
            "grad_theta_midpoint"
        ],
        "direct_terminal_p_equation_defect": direct_p,
        "a": spacing,
        "dt": dt,
    }


def _summarize_block_dominance(share_by_block: Mapping[str, Sequence[float]]) -> dict[str, Any]:
    matrix = np.stack([np.asarray(share_by_block[block_id], dtype=np.float64) for block_id in BLOCK_IDS], axis=1)
    medians = np.median(matrix, axis=0)
    index = int(np.argmax(medians))
    return {
        "dominant_block_id": BLOCK_IDS[index],
        "median_dominance_share": float(medians[index]),
        "dominant_step_fraction": float(np.mean(np.argmax(matrix, axis=1) == index)),
        "median_share_by_block": {block_id: float(medians[i]) for i, block_id in enumerate(BLOCK_IDS)},
        "sample_count": int(matrix.shape[0]),
    }


def _summarize_distributed(
    share_by_block: Mapping[str, Sequence[float]],
    linked: Mapping[str, Sequence[float]],
) -> dict[str, Any]:
    constants = semantic_v1.SUPPORT_CONSTANTS_V1["H_D"]
    matrix = np.stack([np.asarray(share_by_block[block_id], dtype=np.float64) for block_id in BLOCK_IDS], axis=1)
    count = np.sum(matrix >= constants["per_block_share_minimum"], axis=1)
    total = np.sum(matrix, axis=1)
    square = np.sum(matrix**2, axis=1)
    effective = np.zeros(matrix.shape[0], dtype=np.float64)
    np.divide(total**2, square, out=effective, where=square > 0.0)
    maximum = np.max(matrix, axis=1)
    qualifying = (
        (count >= constants["minimum_contributing_block_count_per_step"])
        & (effective >= constants["effective_block_count_minimum"])
        & (maximum < constants["single_block_share_maximum_exclusive"])
    )
    linked_arrays = {key: np.asarray(value, dtype=np.float64) for key, value in linked.items()}
    return {
        "distributed_step_fraction": float(np.mean(qualifying)),
        "linked_series_maxima_at_final_count": sum(bool(array[-1] == np.max(array)) for array in linked_arrays.values()),
        "minimum_nondecreasing_increment_count": min(int(np.sum(np.diff(array) >= 0.0)) for array in linked_arrays.values()),
        "sample_count": int(matrix.shape[0]),
        "linked_series_count": len(linked_arrays),
        "contributing_block_count_by_step": [int(value) for value in count],
        "effective_block_count_by_step": [float(value) for value in effective],
        "maximum_block_share_by_step": [float(value) for value in maximum],
    }


def _recompute_instrumented_metrics(payload: Mapping[str, Any], record: Mapping[str, Any]) -> dict[str, Any]:
    run_id = str(record["run_id"])
    raw_events = _require_exact_keys(payload["raw_events"], EVENT_FAMILIES, diagnostic="INSTRUMENTED_EVENT_FAMILY_CLOSURE_MISMATCH")
    for family in EVENT_FAMILIES:
        if not isinstance(raw_events[family], list) or len(raw_events[family]) != POSTINITIAL_STEPS:
            _fail("BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "REQUIRED_RAW_EVENT_MISSING", f"{run_id}:{family}")
    trajectory = payload["physical_trajectory"]
    tolerance = float(record["tolerance"])
    spacing = float(payload["configuration"]["a"])
    field_series: list[float] = []
    matter_series: list[float] = []
    remainder_series: list[float] = []
    shares = {block_id: [] for block_id in BLOCK_IDS}
    gauss_series: list[float] = []
    continuity_series: list[float] = []
    longitudinal_series: list[float] = []
    solver_converged: list[bool] = []
    solver_iterations: list[int] = []
    solver_residuals: list[float] = []
    hc_inputs: dict[str, list[np.ndarray]] = {
        key: []
        for key in (
            "direct_terminal_p_equation_defect",
            "p_previous",
            "p_current",
            "rho_previous",
            "rho_current",
            "continuity_current_midpoint_independently_recomputed",
            "maxwell_source_midpoint_registered",
        )
    }
    for step in range(1, POSTINITIAL_STEPS + 1):
        expected_time = step * float(payload["configuration"]["effective_dt"])
        for family in EVENT_FAMILIES:
            event = raw_events[family][step - 1]
            if (
                not isinstance(event, Mapping)
                or event.get("step") != step
                or event.get("time") != expected_time
            ):
                _fail(
                    "BLOCKED_OBSERVABLE_SEMANTICS",
                    "EVENT_TIME_OR_STEP_IDENTITY_MISMATCH",
                    f"{run_id}:{family}:{step}",
                )
        previous_state = _unpack_state(trajectory[step - 1])
        current_state = _unpack_state(trajectory[step])
        field, matter, remainder, matter_cell = _validate_exchange_event(
            raw_events["exchange"][step - 1],
            step,
            previous_state["p"],
            current_state["p"],
            spacing,
        )
        defect, step_shares = _validate_terminal_event(raw_events["terminal_equation_blocks"][step - 1], step, tolerance)
        solver_event = raw_events["solver_steps"][step - 1]
        _validate_solver_step(solver_event, step, tolerance)
        if solver_event["terminal_equation_residual"] != float(
            np.max(np.abs(defect))
        ):
            _fail(
                "BLOCKED_OBSERVABLE_SEMANTICS",
                "RAW_SUMMARY_RECOMPUTATION_MISMATCH",
                f"{run_id}:terminal equation residual:{step}",
            )
        spatial = _validate_spatial_event(raw_events["spatial_constraints"][step - 1], step, spacing, defect)
        closure = _validate_closure_event(raw_events["discrete_closure"][step - 1], step, trajectory, spatial, defect, payload["configuration"])
        expected_matter_cell = (
            float(payload["configuration"]["effective_dt"])
            * closure["maxwell_source_midpoint_registered"]
            * (0.5 * (previous_state["p"] + current_state["p"]) / spacing)
        )
        _assert_exact(
            matter_cell,
            expected_matter_cell,
            "RAW_EXCHANGE_SOURCE_BINDING_MISMATCH",
            f"matter:{step}",
        )
        field_series.append(field)
        matter_series.append(matter)
        remainder_series.append(remainder)
        for block_id in BLOCK_IDS:
            shares[block_id].append(step_shares[block_id])
        gauss_series.append(float(spatial["gauss_maximum_absolute"]))
        continuity_series.append(float(spatial["continuity_maximum_absolute"]))
        longitudinal_series.append(max(_block_maxima(defect)["THETA_KINEMATIC"], _block_maxima(defect)["P_LONGITUDINAL_MAXWELL"]))
        solver_converged.append(bool(solver_event["converged"]))
        solver_iterations.append(int(solver_event["iteration_count"]))
        solver_residuals.append(float(solver_event["terminal_solver_residual"]))
        for key in hc_inputs:
            hc_inputs[key].append(np.asarray(closure[key], dtype=np.float64))
    if (
        payload["all_steps_converged"] is not all(solver_converged)
        or payload["maximum_iterations_used"] != max(solver_iterations)
        or payload["maximum_solver_residual"] != max(solver_residuals)
    ):
        _fail(
            "BLOCKED_OBSERVABLE_SEMANTICS",
            "RAW_SUMMARY_RECOMPUTATION_MISMATCH",
            f"{run_id}:solver payload summary",
        )
    field_array = np.asarray(field_series, dtype=np.float64)
    matter_array = np.asarray(matter_series, dtype=np.float64)
    numerator = np.abs(field_array) + np.abs(matter_array)
    remainder = field_array + matter_array
    kappa = np.zeros_like(numerator)
    np.divide(numerator, np.abs(remainder) + GAMMA64 * numerator, out=kappa, where=numerator > 0.0)
    h_a_threshold = semantic_v1.SUPPORT_CONSTANTS_V1["H_A"]["loose_median_kappa_minimum"]
    exchange_summary = {
        "median_kappa": float(np.median(kappa)),
        "severe_step_fraction": float(np.mean(kappa >= h_a_threshold)),
        "sample_count": int(kappa.size),
        "severe_kappa_threshold": h_a_threshold,
        "gamma_operation_count": 64,
        "gamma64": GAMMA64,
    }
    block_summary = _summarize_block_dominance(shares)
    paths = semantic_v1.reconstruct_independent_hc_paths(
        direct_terminal_p_equation_defect=np.stack(hc_inputs["direct_terminal_p_equation_defect"]),
        p_previous=np.stack(hc_inputs["p_previous"]),
        p_current=np.stack(hc_inputs["p_current"]),
        rho_previous=np.stack(hc_inputs["rho_previous"]),
        rho_current=np.stack(hc_inputs["rho_current"]),
        continuity_current_midpoint_independently_recomputed=np.stack(
            hc_inputs["continuity_current_midpoint_independently_recomputed"]
        ),
        maxwell_source_midpoint_registered=np.stack(
            hc_inputs["maxwell_source_midpoint_registered"]
        ),
        a=spacing,
        dt=float(payload["configuration"]["effective_dt"]),
        requested_solver_tolerance=tolerance,
    )
    closure_summary = semantic_v1.summarize_independent_hc_paths(paths)
    distributed_summary = _summarize_distributed(
        shares,
        {
            "GAUSS": gauss_series,
            "CONTINUITY": continuity_series,
            "LONGITUDINAL_EXCHANGE": np.abs(remainder).tolist(),
            "LONGITUDINAL_MAXWELL": longitudinal_series,
        },
    )
    # v0 payload metrics and MATRIX-RESULT classifier_metrics are retained only
    # as non-authoritative historical summaries.  No value is read here.
    return {
        "exchange_conditioning": exchange_summary,
        "block_dominance": block_summary,
        "independent_discrete_closure": closure_summary,
        "distributed_accumulation": distributed_summary,
    }


def _validate_auxiliary_result(
    repo_root: Path,
    output_root: Path,
    records: Sequence[Mapping[str, Any]],
    file_hashes: Mapping[str, tuple[str, str]],
    trajectories: Mapping[str, np.ndarray],
    canonical_digest: str,
    authority: Mapping[str, Any],
    review_anchor_sha256: str,
) -> tuple[Mapping[str, Any], tuple[Mapping[str, Any], ...]]:
    start = _load_json_object(output_root / "EXECUTION-STARTED.json")
    result = _load_json_object(output_root / "MATRIX-RESULT.json")
    if (
        start.get("schema_id") != EXECUTION_STARTED_SCHEMA_ID
        or start.get("status") != "EXECUTION_STARTED_NO_RETRY"
        or not isinstance(start.get("runtime_custody"), Mapping)
        or start["runtime_custody"].get("requested_run_ids")
        != list(EXPECTED_RUN_IDS)
    ):
        _fail("BLOCKED_CUSTODY", "EXECUTION_START_MARKER_INVALID")
    if start.get("no_overwrite") is not True or start.get("no_retry") is not True:
        _fail("BLOCKED_CUSTODY", "EXECUTION_START_MARKER_INVALID")
    if (
        start["runtime_custody"].get("all_passed") is not True
        or start["runtime_custody"].get("execution_invoked") is not True
    ):
        _fail("BLOCKED_CUSTODY", "RUNTIME_PREFLIGHT_CUSTODY_FAILED")
    runtime_custody = start["runtime_custody"]
    review_anchor_report = runtime_custody.get("review_anchor")
    if (
        not isinstance(review_anchor_report, Mapping)
        or review_anchor_report.get("relative_path")
        != executor_custody_v2.REVIEW_ANCHOR_RELATIVE_PATH
        or review_anchor_report.get("verdict")
        != executor_custody_v2.EXPECTED_REVIEW_VERDICT
        or review_anchor_report.get("sha256") != review_anchor_sha256
        or review_anchor_report.get("fixed_path_bytes_loaded") is not True
    ):
        _fail(
            "BLOCKED_CUSTODY",
            "EXECUTION_START_REVIEW_ANCHOR_MISMATCH",
            "review_anchor",
        )
    expected_runtime_anchor = {
        "runtime_execution_authority_sha256": _sha256(
            executor_v2.canonical_json_bytes(authority)
        ),
        "runtime_source_closure_sha256": authority[
            "runtime_source_closure_sha256"
        ],
        "expected_full_record_sha256_by_run_id": authority[
            "expected_full_record_sha256_by_run_id"
        ],
        "physical_configuration_core_sha256_by_run_id": authority[
            "expected_physical_configuration_sha256_by_run_id"
        ],
        "scientific_input_core_sha256_by_run_id": authority[
            "expected_scientific_input_sha256_by_run_id"
        ],
        "complete_execution_identity_sha256_by_run_id": authority[
            "expected_complete_execution_sha256_by_run_id"
        ],
    }
    for key, expected in expected_runtime_anchor.items():
        if runtime_custody.get(key) != expected:
            _fail(
                "BLOCKED_CUSTODY",
                "EXECUTION_START_REVIEW_ANCHOR_MISMATCH",
                key,
            )
    loaded_attestation = runtime_custody.get("loaded_module_attestation")
    if (
        not isinstance(loaded_attestation, Mapping)
        or loaded_attestation.get("all_passed") is not True
        or loaded_attestation.get("runtime_source_closure_sha256")
        != authority["runtime_source_closure_sha256"]
        or loaded_attestation.get("loaded_module_count")
        != len(REQUIRED_IMPLEMENTATION_MODULE_NAMES)
    ):
        _fail("BLOCKED_CUSTODY", "EXECUTION_START_MODULE_CLOSURE_MISMATCH")
    if result.get("schema_id") != MATRIX_RESULT_SCHEMA_ID or result.get("status") != "EXECUTION_COMPLETED_ONCE":
        _fail("BLOCKED_CUSTODY", "MATRIX_EXECUTION_NOT_COMPLETED_ONCE")
    if result.get("runtime_custody") != start.get("runtime_custody"):
        _fail("BLOCKED_CUSTODY", "RUNTIME_PREFLIGHT_CUSTODY_MISMATCH")
    if result.get("exact_run_ids") != list(EXPECTED_RUN_IDS) or result.get("execution_count_by_run_id") != {run_id: 1 for run_id in EXPECTED_RUN_IDS}:
        _fail("BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH")
    custody = result.get("run_custody")
    if not isinstance(custody, list) or len(custody) != 6:
        _fail("BLOCKED_RUN_IDENTITY", "EXPECTED_PAYLOAD_ID_CLOSURE_MISMATCH")
    by_run = {item.get("run_id"): item for item in custody if isinstance(item, dict)}
    if set(by_run) != set(EXPECTED_RUN_IDS) or len(by_run) != 6:
        _fail("BLOCKED_RUN_IDENTITY", "DUPLICATE_PAYLOAD_IDENTITY")
    for ordinal, record in enumerate(records, start=1):
        run_id = str(record["run_id"])
        item = by_run[run_id]
        json_sha, npz_sha = file_hashes[run_id]
        expected = {
            "execution_ordinal": ordinal,
            "full_record_identity_sha256": (
                authority["expected_full_record_sha256_by_run_id"][run_id]
            ),
            "physical_configuration_core_sha256": (
                authority[
                    "expected_physical_configuration_sha256_by_run_id"
                ][run_id]
            ),
            "scientific_input_core_sha256": (
                authority["expected_scientific_input_sha256_by_run_id"][run_id]
            ),
            "complete_execution_identity_sha256": (
                authority["expected_complete_execution_sha256_by_run_id"][run_id]
            ),
            "parent_canonical_run_id": record["parent_canonical_run_id"],
            "parent_canonical_input_hash": record[
                "parent_canonical_input_hash"
            ],
            "parent_canonical_output_sha256": record[
                "parent_canonical_output_sha256"
            ],
            "json_relative_output_path": record["json_relative_output_path"],
            "npz_relative_output_path": record["npz_relative_output_path"],
            "json_sha256": json_sha,
            "npz_sha256": npz_sha,
            "physical_trajectory_sha256": _physical_trajectory_sha256(trajectories[run_id]),
        }
        for key, value in expected.items():
            if item.get(key) != value:
                _fail("BLOCKED_CUSTODY", "MATRIX_RESULT_CUSTODY_MISMATCH", f"{run_id}:{key}")
    pairs: list[Mapping[str, Any]] = []
    for instrumented_id, control_id in PAIR_IDS:
        instrumented = trajectories[instrumented_id]
        control = trajectories[control_id]
        byte_identical = instrumented.dtype == control.dtype and instrumented.shape == control.shape and instrumented.tobytes(order="C") == control.tobytes(order="C")
        record = {
            "instrumented_run_id": instrumented_id,
            "control_run_id": control_id,
            "shape_equal": instrumented.shape == control.shape,
            "byte_identical": byte_identical,
            "instrumented_sha256": _physical_trajectory_sha256(instrumented),
            "control_sha256": _physical_trajectory_sha256(control),
        }
        pairs.append(record)
        if not byte_identical:
            _fail("BLOCKED_INSTRUMENTATION_PERTURBATION", "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL", instrumented_id)
    supplied_pairs = result.get("instrumentation_nonperturbation_pairs")
    if not isinstance(supplied_pairs, list) or len(supplied_pairs) != 3:
        _fail("BLOCKED_CUSTODY", "NONPERTURBATION_SUMMARY_MISSING")
    supplied_by_pair = {(item.get("instrumented_run_id"), item.get("control_run_id")): item for item in supplied_pairs if isinstance(item, dict)}
    for pair in pairs:
        item = supplied_by_pair.get((pair["instrumented_run_id"], pair["control_run_id"]))
        if item is None or item.get("byte_identical") is not True or item.get("instrumented_sha256") != pair["instrumented_sha256"] or item.get("control_sha256") != pair["control_sha256"]:
            _fail("BLOCKED_CUSTODY", "NONPERTURBATION_SUMMARY_RECOMPUTATION_MISMATCH")
    if result.get("all_pairs_byte_identical") is not True or result.get("mechanism_classification_allowed") is not True:
        _fail("BLOCKED_CUSTODY", "NONPERTURBATION_SUMMARY_RECOMPUTATION_MISMATCH")
    if result.get("canonical_digest_before") != canonical_digest or result.get("canonical_digest_after") != canonical_digest or result.get("canonical_digest_unchanged") is not True:
        _fail("BLOCKED_CUSTODY", "CANONICAL_DIGEST_CHANGED")
    return result, tuple(pairs)


def _assemble_raw_evidence_from_paths(
    repo_root: str | Path,
    *,
    run_matrix_path: str | Path | None = None,
    identity_manifest_path: str | Path | None = None,
    freeze_packet_path: str | Path | None = None,
) -> AssembledRawEvidence:
    """Read and independently assemble the exact completed six-run evidence.

    No caller may provide gates, metrics, run IDs, payload IDs, or mechanism
    summaries.  Those values are derived from files registered by the freeze.
    """

    root = Path(repo_root).resolve()
    matrix_path = Path(run_matrix_path) if run_matrix_path is not None else root / DEFAULT_RUN_MATRIX_RELATIVE_PATH
    manifest_path = Path(identity_manifest_path) if identity_manifest_path is not None else root / DEFAULT_IDENTITY_MANIFEST_RELATIVE_PATH
    packet_path = Path(freeze_packet_path) if freeze_packet_path is not None else root / DEFAULT_FREEZE_PACKET_RELATIVE_PATH
    if not matrix_path.is_absolute():
        matrix_path = root / matrix_path
    if not manifest_path.is_absolute():
        manifest_path = root / manifest_path
    if not packet_path.is_absolute():
        packet_path = root / packet_path
    authority, review_anchor_sha256 = _load_and_attest_reviewed_authority(root)
    matrix = _load_json_object(matrix_path, missing_result="BLOCKED_CUSTODY")
    manifest = _load_json_object(manifest_path, missing_result="BLOCKED_CUSTODY")
    freeze_packet = _load_json_object(packet_path, missing_result="BLOCKED_CUSTODY")
    records, output_root = _validate_frozen_documents(
        root, matrix, manifest, authority
    )
    _validate_source_custody(root)
    metric_template = freeze_packet.get("metric_configuration_template")
    if not isinstance(metric_template, dict):
        _fail("BLOCKED_OBSERVABLE_SEMANTICS", "METRIC_CONFIGURATION_MISSING")
    expected_template_values = {
        "severe_kappa_threshold": semantic_v1.SUPPORT_CONSTANTS_V1["H_A"]["loose_median_kappa_minimum"],
        "epsilon_dominance": GAMMA64,
        "distributed_minimum_contributing_block_count": semantic_v1.SUPPORT_CONSTANTS_V1["H_D"]["minimum_contributing_block_count_per_step"],
        "distributed_per_block_share_minimum": semantic_v1.SUPPORT_CONSTANTS_V1["H_D"]["per_block_share_minimum"],
        "distributed_effective_block_count_minimum": semantic_v1.SUPPORT_CONSTANTS_V1["H_D"]["effective_block_count_minimum"],
        "distributed_single_block_share_maximum_exclusive": semantic_v1.SUPPORT_CONSTANTS_V1["H_D"]["single_block_share_maximum_exclusive"],
        "postinitial_sample_count": POSTINITIAL_STEPS,
    }
    for key, expected in expected_template_values.items():
        if metric_template.get(key) != expected:
            _fail("BLOCKED_OBSERVABLE_SEMANTICS", "METRIC_CONFIGURATION_MISMATCH", key)
    if not output_root.is_dir():
        _fail("BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "REQUIRED_OUTPUT_MISSING", str(output_root))
    expected_files = {
        Path(record["json_relative_output_path"]).name for record in records
    } | {
        Path(record["npz_relative_output_path"]).name for record in records
    } | {"EXECUTION-STARTED.json", "MATRIX-RESULT.json"}
    actual_files = {path.name for path in output_root.iterdir() if path.is_file()}
    actual_nonfiles = [path.name for path in output_root.iterdir() if not path.is_file()]
    if actual_files != expected_files or actual_nonfiles:
        missing = sorted(expected_files - actual_files)
        extra = sorted(actual_files - expected_files) + sorted(actual_nonfiles)
        result = "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE" if missing else "BLOCKED_RUN_IDENTITY"
        _fail(result, "EXPECTED_PAYLOAD_INVENTORY_MISMATCH", f"missing={missing}; extra={extra}")
    canonical_root = root / EXPECTED_CANONICAL_ROOT_RELATIVE_PATH
    canonical_digest = _directory_tree_sha256(canonical_root)
    if canonical_digest != EXPECTED_CANONICAL_TREE_SHA256:
        _fail("BLOCKED_CUSTODY", "CANONICAL_DIGEST_CHANGED")
    payloads: dict[str, Mapping[str, Any]] = {}
    trajectories: dict[str, np.ndarray] = {}
    file_hashes: dict[str, tuple[str, str]] = {}
    metrics_by_family: dict[str, dict[str, Mapping[str, Any]]] = {
        family: {}
        for family in (
            "exchange_conditioning",
            "block_dominance",
            "independent_discrete_closure",
            "distributed_accumulation",
        )
    }
    payload_identity_ids: list[str] = []
    raw_evidence_ids: list[str] = []
    for record in records:
        run_id = str(record["run_id"])
        json_path = root / str(record["json_relative_output_path"])
        npz_path = root / str(record["npz_relative_output_path"])
        payload, json_sha, npz_sha = _load_role_payload(
            json_path,
            npz_path,
            expected_run_id=run_id,
            expected_json_sha256=None,
            expected_npz_sha256=None,
        )
        _, trajectory = _validate_payload_identity(payload, record)
        payloads[run_id] = payload
        trajectories[run_id] = trajectory
        file_hashes[run_id] = (json_sha, npz_sha)
        payload_identity_ids.extend([f"{run_id}:JSON:{json_sha}", f"{run_id}:NPZ:{npz_sha}"])
        if record["instrumentation_enabled"] is True:
            metrics = _recompute_instrumented_metrics(payload, record)
            role = CLASSIFIER_ROLE_BY_RUN_ID[run_id]
            for family, value in metrics.items():
                metrics_by_family[family][role] = value
            raw_evidence_ids.extend(f"{run_id}:RAW:{family}" for family in EVENT_FAMILIES)
        else:
            if payload["raw_events"] is not None or payload["metrics"] is not None:
                _fail("BLOCKED_OBSERVABLE_SEMANTICS", "NONINSTRUMENTED_CONTROL_HAS_MECHANISM_DATA", run_id)
    _, pairs = _validate_auxiliary_result(
        root,
        output_root,
        records,
        file_hashes,
        trajectories,
        canonical_digest,
        authority,
        review_anchor_sha256,
    )
    if any(set(role_map) != {"R13_LOOSE", "R13_TIGHT", "R10_LOOSE_NEIGHBOR"} for role_map in metrics_by_family.values()):
        _fail("BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "MECHANISM_METRIC_ROLE_CLOSURE_MISMATCH")
    return AssembledRawEvidence(
        assembler_id=ASSEMBLER_ID,
        run_ids=EXPECTED_RUN_IDS,
        payload_identity_ids=tuple(payload_identity_ids),
        payloads_by_run_id=payloads,
        recomputed_metrics=metrics_by_family,
        nonperturbation_pairs=pairs,
        canonical_tree_sha256=canonical_digest,
        review_anchor_sha256=review_anchor_sha256,
        runtime_source_closure_sha256=authority[
            "runtime_source_closure_sha256"
        ],
        raw_evidence_ids=tuple(raw_evidence_ids),
        supplied_summary_disposition=(
            "PAYLOAD.metrics and MATRIX-RESULT.classifier_metrics ignored; gates, "
            "nonperturbation, operator closure, and H_A-H_D metrics recomputed from raw arrays"
        ),
        semantic_contract_id=semantic_v1.CONTRACT_ID,
    )


def assemble_raw_evidence(repo_root: str | Path) -> AssembledRawEvidence:
    """Authoritative path-closed assembler for the frozen v2 contract.

    Tests may invoke the private ``_assemble_raw_evidence_from_paths`` helper
    with isolated fixtures.  Scientific review and execution-facing callers
    cannot substitute a different matrix, manifest, or freeze packet.
    """

    return _assemble_raw_evidence_from_paths(repo_root)


def self_validate() -> dict[str, bool]:
    """Pure checks; never requires or creates experiment output."""

    dummy = np.zeros((CHECKPOINT_COUNT, PACKED_WIDTH), dtype=np.float64)
    digest = _physical_trajectory_sha256(dummy)
    return {
        "exact_six_run_ids": len(EXPECTED_RUN_IDS) == 6 and len(set(EXPECTED_RUN_IDS)) == 6,
        "exact_twelve_payload_identity_classes": 2 * len(EXPECTED_RUN_IDS) == 12,
        "exact_eight_block_registry": len(BLOCK_IDS) == 8 and BLOCK_SPANS_IN_N[BLOCK_IDS[-1]][1] == PACKED_COMPONENTS_PER_SITE,
        "trajectory_hash_is_stable": digest == _physical_trajectory_sha256(dummy.copy()),
        "support_constant_leaf_count_is_23": sum(len(values) for values in semantic_v1.SUPPORT_CONSTANTS_V1.values()) == 23,
        "legacy_q_not_decision_bearing": semantic_v1.LEGACY_Q["mechanism_decision_bearing"] is False,
    }


__all__ = [
    "ASSEMBLER_ID",
    "AssembledRawEvidence",
    "RawEvidenceError",
    "assemble_raw_evidence",
    "self_validate",
]
