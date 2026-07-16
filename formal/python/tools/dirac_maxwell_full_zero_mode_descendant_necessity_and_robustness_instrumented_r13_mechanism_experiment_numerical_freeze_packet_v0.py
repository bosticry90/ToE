from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import importlib
import json
import math
import platform
import struct
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v0
    as classifier,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0.py"
)
CLASSIFIER_RELATIVE_PATH = classifier.SCRIPT_RELATIVE_PATH
IMPLEMENTATION_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_implementation_v0.py"
)
BASE_IMPLEMENTATION_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"
)
ROBUSTNESS_IMPLEMENTATION_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_non_authoritative_pilot_v1.py"
)

PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-PACKET-v0.json"
)
RUN_MATRIX_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-RUN-MATRIX-v0.json"
)
IDENTITY_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "EXPECTED-OUTPUT-IDENTITY-MANIFEST-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-MANIFEST-v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "20260715_v0.json"
)

DESIGN_PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-PACKET-v1.json"
)
DESIGN_MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-MANIFEST-v1.json"
)
DESIGN_REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_20260715_v1.json"
)
DESIGN_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_"
    "20260715_v1.json"
)
DESIGN_GENERATOR_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_v1.py"
)
DESIGN_REVIEW_GENERATOR_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_review_v1.py"
)

CANONICAL_FREEZE_V2_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
)
CANONICAL_FREEZE_V3_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v3.json"
)
CANONICAL_FREEZE_V3_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v3.json"
)
CANONICAL_MATRIX_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
)
CANONICAL_IDENTITY_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
)
CANONICAL_EXECUTION_PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-PACKET-v2.json"
)
CANONICAL_EXECUTION_MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-MANIFEST-v2.json"
)
CANONICAL_RESULT_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json"
)

CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
CONFIGURATION_SOURCE_COMMIT = "d2f24a13b0c42cabb531dbcf9d87ac9c0f766987"
CONFIGURATION_SOURCE_PARENT = "e37382150e4bc7d5edc05eff6432e3cd8c0a33e6"
COMMITTED_CONFIGURATION = {
    "requirements.active.lock": {
        "git_blob_oid": "ccae5044059a1a5607fd8e7760092a1a72873c9d",
        "sha256_of_committed_bytes": (
            "eefb37359a4d4fcbe1df8f87c6ee786974f27d8d338dd59b413d418948d7ab9a"
        ),
    },
    "formal/toe_formal/lean-toolchain": {
        "git_blob_oid": "bd19bde0ce12df3a11c3f4fd0b7513c30693d72c",
        "sha256_of_committed_bytes": (
            "194fcae7a59d3268baa175bd3e352dafab6954fe08a5b7caec13bedf36f80315"
        ),
    },
    "formal/toe_formal/lake-manifest.json": {
        "git_blob_oid": "e90c7d8e2adffdc5772a0e21ac104966ac3238f4",
        "sha256_of_committed_bytes": (
            "19e09b5f13d32af5353532484e6b3040d4cccdd2c8b5961ec5663d7de8b2d36b"
        ),
    },
    ".gitattributes": {
        "git_blob_oid": "ea3dfdc75c63ac76dae704e3ea02b6502a44ed17",
        "sha256_of_committed_bytes": (
            "8c8a2238ce1b6bed96c371fd58b47008ab7a9373eb89f670458e0203c1b4e6de"
        ),
    },
}
TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0"
)
REVIEW_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0_result"
)
SELECTED_NEXT_TARGET = REVIEW_TARGET
POST_ACCEPTANCE_TARGET = (
    "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_v0_once"
)
BLOCKED_TARGET = (
    "repair_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0"
)

EXPERIMENT_OUTPUT_ROOT = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)
CANONICAL_OUTPUT_ROOT = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)
EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256 = (
    "886541953dfcfecfffa44b2ff9e2ee62c14c468139042bf4f3477ef3a1f2a721"
)

EXPECTED_SOURCE_HASHES = {
    DESIGN_PACKET_RELATIVE_PATH: "a06e25fb53bed76df140cda935be1e878e0aa0dc437bf2aba4addcd687fb93d1",
    DESIGN_MANIFEST_RELATIVE_PATH: "f6f737c7a6c22c33e84f42547f439b80b4068bfb1ebbf7ee2e00e31eb14944b9",
    DESIGN_REPORT_RELATIVE_PATH: "2f188f785a4fa18e4213ab4e252df75773e7eb917a29705c73c4a06b7ab2eeb8",
    DESIGN_REVIEW_RELATIVE_PATH: "29a61d4c019861df1d6807f8410a805d7d099ebc2805b7392103c86aa9850afc",
    DESIGN_GENERATOR_RELATIVE_PATH: "30f0ac96cda91b1f928998f7615b7c6125e8a5c70876d0588694863395355946",
    DESIGN_REVIEW_GENERATOR_RELATIVE_PATH: "9c0d4b5efcf868be7c0d2261b9f4bd22f71c6699d98253507432c799e60c8b56",
    CANONICAL_FREEZE_V2_RELATIVE_PATH: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    CANONICAL_FREEZE_V3_RELATIVE_PATH: "7d4c78ef15a24045a16d0fbed3ebcb4cabf77d2b8dbfddc4d6dbafe7739bc5af",
    CANONICAL_FREEZE_V3_REVIEW_RELATIVE_PATH: "cbafbed9e17f97bb3218a30bd9d31c6c2f1f3c512f57e8a6b66cd485c28ea77d",
    CANONICAL_MATRIX_RELATIVE_PATH: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    CANONICAL_IDENTITY_RELATIVE_PATH: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    CANONICAL_EXECUTION_PACKET_RELATIVE_PATH: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
    CANONICAL_EXECUTION_MANIFEST_RELATIVE_PATH: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    CANONICAL_RESULT_REVIEW_RELATIVE_PATH: "cacbd77f3ef18a80d8d15686dd8f385f73a634038fddb5010058f2e144ef3c85",
    ROBUSTNESS_IMPLEMENTATION_RELATIVE_PATH: "05e7015499e3d15bc172840ac637fd0fa86b6c50f87489d6b555657ac290adb6",
    BASE_IMPLEMENTATION_RELATIVE_PATH: "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
}
EXPECTED_CLASSIFIER_SHA256 = (
    "6f860716f29da107cd8f70a009d62d6003fce5fc9eb1cc316a3ab9d50171fdca"
)
EXPECTED_IMPLEMENTATION_SHA256 = (
    "f4bdd5cd0f725f135060e1fe7476ef8edc5ce2a12c72ec0b0357239197006150"
)

PARENT_CANONICAL_RUN_IDS = {
    "R13_LOOSE": "R13_CORNER_STRONG_LOW:SOLVER_TOL1eM08",
    "R13_TIGHT": "R13_CORNER_STRONG_LOW:SOLVER_TOL1eM12",
    "R10_LOOSE_NEIGHBOR": "R10_MU_HIGH:SOLVER_TOL1eM08",
}
EXPECTED_PARENT_INPUT_HASHES = {
    "R13_LOOSE": "7d652ed58bfca8cacd32ccb7706c85ea686d8f5890a555036854b30c27387b76",
    "R13_TIGHT": "bfc40ca5cbe5c416528fc68c000b05c50a5e40a37d9d12442a82875cef223658",
    "R10_LOOSE_NEIGHBOR": "b0b792481371d9728b9562fbbcae0d0832206c8844736a2f9764fa049fd1e2d3",
}

RUN_SPECS = [
    ("MECHv0:R13_LOOSE:INSTRUMENTED", "R13_LOOSE", True),
    ("MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL", "R13_LOOSE", False),
    ("MECHv0:R13_TIGHT:INSTRUMENTED", "R13_TIGHT", True),
    ("MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL", "R13_TIGHT", False),
    ("MECHv0:R10_LOOSE:INSTRUMENTED", "R10_LOOSE_NEIGHBOR", True),
    ("MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL", "R10_LOOSE_NEIGHBOR", False),
]

OBSERVABLE_IDS = [
    "EXCHANGE_FIELD_LONGITUDINAL_RAW",
    "EXCHANGE_MATTER_LONGITUDINAL_RAW",
    "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
    "EXCHANGE_CANCELLATION_KAPPA",
    "SOLVER_BLOCK_RESIDUAL_RAW",
    "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
    "SOLVER_BLOCK_DOMINANCE_FRACTION",
    "SOLVER_ITERATION_METADATA",
    "GAUSS_RESIDUAL_FIELD",
    "CONTINUITY_RESIDUAL_FIELD",
    "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
    "DISCRETE_OPERATOR_OUTPUTS",
    "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
    "INSTRUMENTATION_TRAJECTORY_IDENTITY",
]

BLOCK_IDS = [
    "THETA_KINEMATIC",
    "P_LONGITUDINAL_MAXWELL",
    "PHI2_KINEMATIC",
    "P2_DYNAMIC",
    "PHI3_KINEMATIC",
    "P3_DYNAMIC",
    "DIRAC_PLUS",
    "DIRAC_MINUS",
]

FLOAT64_UNIT_ROUNDOFF = 2.0**-53


def gamma_n(operation_count: int) -> float:
    product = operation_count * FLOAT64_UNIT_ROUNDOFF
    return product / (1.0 - product)


GAMMA32 = gamma_n(32)
GAMMA64 = gamma_n(64)


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def literal_constant(relative_path: str, name: str) -> Any:
    source = (REPO_ROOT / relative_path).read_text(encoding="utf-8")
    tree = ast.parse(source, filename=relative_path)
    for statement in tree.body:
        if isinstance(statement, (ast.Assign, ast.AnnAssign)):
            targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
            if any(isinstance(target, ast.Name) and target.id == name for target in targets):
                value = statement.value
                if value is None:
                    break
                try:
                    return ast.literal_eval(value)
                except (ValueError, TypeError) as error:
                    raise ValueError(
                        f"implementation constant is not literal: {name}"
                    ) from error
    raise ValueError(f"implementation constant missing: {name}")


def _canonical_root_inventory() -> list[dict[str, str]]:
    return [
        {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for path in sorted((REPO_ROOT / CANONICAL_OUTPUT_ROOT).glob("*.json"))
    ]


def canonical_root_digest() -> str:
    return sha256_bytes(canonical_json_bytes(_canonical_root_inventory()))


def canonical_directory_tree_sha256() -> str:
    root = REPO_ROOT / CANONICAL_OUTPUT_ROOT
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


def _source_custody() -> dict[str, Any]:
    observed = {
        path: sha256_path(REPO_ROOT / path) for path in EXPECTED_SOURCE_HASHES
    }
    mismatches = [
        path
        for path, expected in EXPECTED_SOURCE_HASHES.items()
        if observed[path] != expected
    ]
    if mismatches:
        raise ValueError(f"accepted source custody mismatch: {mismatches}")
    review = load_json(DESIGN_REVIEW_RELATIVE_PATH)
    if not (
        review.get("verdict")
        == "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN"
        and review.get("selected_next_target") == TARGET
        and review.get("target")
        == "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
        "instrumented_r13_mechanism_experiment_design_packet_v1_result"
        and review.get("root_numerical_mechanism_status") == "UNRESOLVED"
    ):
        raise ValueError("accepted design-v1 review does not authorize this freeze preparation")
    root_inventory = _canonical_root_inventory()
    root_digest = sha256_bytes(canonical_json_bytes(root_inventory))
    if len(root_inventory) != 205 or root_digest != EXPECTED_CANONICAL_ROOT_DIGEST:
        raise ValueError("canonical output root custody mismatch")
    directory_digest = canonical_directory_tree_sha256()
    if directory_digest != EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256:
        raise ValueError("canonical directory-tree preflight digest mismatch")
    if (REPO_ROOT / EXPERIMENT_OUTPUT_ROOT).exists():
        raise ValueError("future mechanism experiment output root already exists")
    return {
        "accepted_design_review_verdict": review["verdict"],
        "accepted_design_review_target_consumed": review["target"],
        "accepted_design_review_selected_next_target": review["selected_next_target"],
        "source_artifact_hashes": observed,
        "all_source_artifact_hashes_exact": True,
        "canonical_output_root": CANONICAL_OUTPUT_ROOT,
        "canonical_root_file_count": len(root_inventory),
        "canonical_run_output_count_checked": 203,
        "canonical_root_digest": root_digest,
        "canonical_root_digest_domain": "AUTHORITY_CHAIN_CANONICAL_JSON_INVENTORY",
        "canonical_root_digest_exact": True,
        "canonical_directory_tree_sha256": directory_digest,
        "canonical_directory_tree_sha256_domain": (
            "R13-MECHANISM-DIRECTORY-TREE-v0"
        ),
        "canonical_directory_tree_sha256_exact": True,
        "future_execution_preflight_uses_directory_tree_sha256": True,
        "future_experiment_output_root": EXPERIMENT_OUTPUT_ROOT,
        "future_experiment_output_root_absent": True,
        "canonical_output_mutation_count": 0,
        "new_simulation_run_count": 0,
        "passed": True,
    }


def _git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(
        ["git", "show", f"{commit}:{path}"], cwd=REPO_ROOT
    )


def _committed_configuration_custody() -> dict[str, Any]:
    observed_parent = subprocess.check_output(
        ["git", "rev-parse", f"{CONFIGURATION_SOURCE_COMMIT}^"],
        cwd=REPO_ROOT,
    ).decode("ascii").strip()
    if observed_parent != CONFIGURATION_SOURCE_PARENT:
        raise ValueError("configuration source-commit parent mismatch")

    records: list[dict[str, Any]] = []
    for path, expected in COMMITTED_CONFIGURATION.items():
        raw = _git_bytes(CONFIGURATION_SOURCE_COMMIT, path)
        observed_blob = subprocess.check_output(
            ["git", "rev-parse", f"{CONFIGURATION_SOURCE_COMMIT}:{path}"],
            cwd=REPO_ROOT,
        ).decode("ascii").strip()
        observed_sha256 = sha256_bytes(raw)
        if (
            observed_blob != expected["git_blob_oid"]
            or observed_sha256 != expected["sha256_of_committed_bytes"]
        ):
            raise ValueError(f"committed configuration custody mismatch: {path}")
        records.append(
            {
                "path": path,
                "source_commit": CONFIGURATION_SOURCE_COMMIT,
                "git_blob_oid": observed_blob,
                "sha256": observed_sha256,
                "normalization_mode": (
                    "committed Git blob bytes; no working-tree conversion"
                ),
                "read_contract": f"git show {CONFIGURATION_SOURCE_COMMIT}:{path}",
                "working_tree_hash_is_regeneration_input": False,
            }
        )
    return {
        "source_commit": CONFIGURATION_SOURCE_COMMIT,
        "source_commit_parent": CONFIGURATION_SOURCE_PARENT,
        "records": records,
        "all_authoritative_hashes_use_committed_bytes": True,
        "working_tree_line_endings_cannot_change_artifact_bytes": True,
    }


def _implementation_binding() -> dict[str, Any]:
    path = REPO_ROOT / IMPLEMENTATION_RELATIVE_PATH
    if not path.is_file():
        raise ValueError("instrumented implementation source is not yet present")
    implementation_sha256 = sha256_path(path)
    if implementation_sha256 != EXPECTED_IMPLEMENTATION_SHA256:
        raise ValueError("instrumented implementation source hash mismatch")
    implementation_id = literal_constant(IMPLEMENTATION_RELATIVE_PATH, "IMPLEMENTATION_ID")
    output_schema = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "OUTPUT_SCHEMA_VERSION"
    )
    implementation_blocks = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "BLOCK_REGISTRY"
    )
    implementation_observables = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "OBSERVABLE_IDS"
    )
    discrete_closure = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "DISCRETE_CLOSURE_CONTRACT"
    )
    exact_run_ids = literal_constant(IMPLEMENTATION_RELATIVE_PATH, "EXACT_MATRIX_RUN_IDS")
    expected_rows = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "EXPECTED_ROW_PARAMETERS"
    )
    expected_tolerances = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "EXPECTED_TOLERANCE_BY_RUN_ID"
    )
    expected_numerics = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "EXPECTED_EXPERIMENT_NUMERICS"
    )
    expected_output_root = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH,
        "EXPECTED_EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH",
    )
    expected_output_paths = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "EXPECTED_OUTPUT_PATHS_BY_RUN_ID"
    )
    expected_canonical_tree = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256"
    )
    mandatory_event_families = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "MANDATORY_INSTRUMENTED_EVENT_FAMILIES"
    )
    run_payload_schema_id = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "RUN_ROLE_PAYLOAD_SCHEMA_ID"
    )
    matrix_result_schema_id = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "MATRIX_RESULT_SCHEMA_ID"
    )
    bound_historical_sources = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "BOUND_SOURCE_SHA256"
    )
    expected_python_version = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "EXPECTED_PYTHON_VERSION"
    )
    expected_numpy_version = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "EXPECTED_NUMPY_VERSION"
    )
    required_execution_environment = literal_constant(
        IMPLEMENTATION_RELATIVE_PATH, "REQUIRED_EXECUTION_ENVIRONMENT"
    )
    implementation_block_ids = [
        item["block_id"] if isinstance(item, dict) else item
        for item in implementation_blocks
    ]
    if implementation_block_ids != BLOCK_IDS:
        raise ValueError(
            f"instrumentation block registry mismatch: {implementation_block_ids}"
        )
    if list(implementation_observables) != OBSERVABLE_IDS:
        raise ValueError("instrumentation observable registry mismatch")
    if list(exact_run_ids) != list(classifier.EXPECTED_RUN_IDS):
        raise ValueError("implementation/classifier run-ID closure mismatch")
    if expected_output_root != EXPERIMENT_OUTPUT_ROOT:
        raise ValueError("implementation output-root closure mismatch")
    if expected_canonical_tree != EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256:
        raise ValueError("implementation canonical-tree digest closure mismatch")
    if expected_numerics != {
        "n": 16,
        "dt": 0.003125,
        "duration": 0.05,
        "max_iterations": 80,
    }:
        raise ValueError("implementation numerical closure mismatch")
    if bound_historical_sources != {
        ROBUSTNESS_IMPLEMENTATION_RELATIVE_PATH: EXPECTED_SOURCE_HASHES[
            ROBUSTNESS_IMPLEMENTATION_RELATIVE_PATH
        ],
        BASE_IMPLEMENTATION_RELATIVE_PATH: EXPECTED_SOURCE_HASHES[
            BASE_IMPLEMENTATION_RELATIVE_PATH
        ],
    }:
        raise ValueError("implementation historical-source binding mismatch")
    if expected_python_version != platform.python_version():
        raise ValueError("implementation Python-version closure mismatch")
    if expected_numpy_version != np.__version__:
        raise ValueError("implementation NumPy-version closure mismatch")
    return {
        "path": IMPLEMENTATION_RELATIVE_PATH,
        "sha256": implementation_sha256,
        "implementation_id": implementation_id,
        "output_schema_version": output_schema,
        "literal_block_registry": copy.deepcopy(implementation_blocks),
        "literal_observable_ids": list(implementation_observables),
        "literal_discrete_closure_contract": copy.deepcopy(discrete_closure),
        "literal_exact_run_ids": list(exact_run_ids),
        "literal_expected_row_parameters": copy.deepcopy(expected_rows),
        "literal_expected_tolerances": copy.deepcopy(expected_tolerances),
        "literal_expected_numerics": copy.deepcopy(expected_numerics),
        "literal_expected_output_root": expected_output_root,
        "literal_expected_output_paths_by_run_id": copy.deepcopy(
            expected_output_paths
        ),
        "literal_expected_canonical_directory_tree_sha256": expected_canonical_tree,
        "literal_mandatory_instrumented_event_families": list(
            mandatory_event_families
        ),
        "literal_run_role_payload_schema_id": run_payload_schema_id,
        "literal_matrix_result_schema_id": matrix_result_schema_id,
        "literal_bound_historical_sources": copy.deepcopy(bound_historical_sources),
        "literal_expected_python_version": expected_python_version,
        "literal_expected_numpy_version": expected_numpy_version,
        "literal_required_execution_environment": copy.deepcopy(
            required_execution_environment
        ),
        "implementation_imported_only_for_pure_schema_and_matrix_validation": True,
        "evolution_or_execution_runner_invocation_count": 0,
    }


def _environment_identity() -> dict[str, Any]:
    committed_configuration = _committed_configuration_custody()
    numpy_config = np.__config__.CONFIG
    build_dependencies = numpy_config.get("Build Dependencies", {})
    blas = build_dependencies.get("blas", {})
    lapack = build_dependencies.get("lapack", {})
    normalized_numpy_config = {
        "blas": {
            key: blas.get(key)
            for key in (
                "name",
                "found",
                "version",
                "detection method",
                "openblas configuration",
            )
        },
        "lapack": {
            key: lapack.get(key)
            for key in (
                "name",
                "found",
                "version",
                "detection method",
                "openblas configuration",
            )
        },
        "compilers": copy.deepcopy(numpy_config.get("Compilers", {})),
        "machine_information": copy.deepcopy(
            numpy_config.get("Machine Information", {})
        ),
        "SIMD_extensions": copy.deepcopy(numpy_config.get("SIMD Extensions", {})),
        "excluded_build_path_fields": [
            "include directory",
            "lib directory",
            "pc file directory",
            "Python Information.path",
        ],
    }
    if not (
        np.__version__ == "2.2.6"
        and blas.get("version") == "0.3.29"
        and "USE64BITINT" in str(blas.get("openblas configuration"))
        and "Haswell" in str(blas.get("openblas configuration"))
    ):
        raise ValueError("NumPy/OpenBLAS environment identity mismatch")
    return {
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "operating_system": platform.system(),
        "os_release": platform.release(),
        "machine": platform.machine(),
        "architecture": list(platform.architecture()),
        "processor": platform.processor(),
        "normalized_numpy_configuration": normalized_numpy_config,
        "canonical_serialization": (
            "sorted-key UTF-8 NFC JSON with LF and finite numbers only"
        ),
        "required_process_environment": {
            "PYTHONHASHSEED": "0",
            "TZ": "UTC",
            "LC_ALL": "C",
            "LANG": "C",
            "OPENBLAS_NUM_THREADS": "1",
            "OMP_NUM_THREADS": "1",
            "MKL_NUM_THREADS": "1",
            "NUMEXPR_NUM_THREADS": "1",
        },
        "bound_files": committed_configuration["records"],
        "committed_configuration_custody": committed_configuration,
        "floating_point_contract": {
            "format": "IEEE-754 binary64",
            "unit_roundoff": FLOAT64_UNIT_ROUNDOFF,
            "gamma_32": GAMMA32,
            "gamma_64": GAMMA64,
            "nonfinite_output_behavior": "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
        },
    }


def _block_registry() -> list[dict[str, Any]]:
    records = [
        (
            "THETA_KINEMATIC",
            "theta",
            "theta_next - theta_previous - dt * (p_mid / a)",
            "longitudinal gauge-link angle update",
        ),
        (
            "P_LONGITUDINAL_MAXWELL",
            "p",
            "p_next - p_previous + dt * grad_theta_mid",
            "longitudinal Maxwell momentum update",
        ),
        (
            "PHI2_KINEMATIC",
            "phi2",
            "phi2_next - phi2_previous - dt * (P2_mid / a)",
            "phi2 descendant kinematic update",
        ),
        (
            "P2_DYNAMIC",
            "P2",
            "P2_next - P2_previous - dt * a * (laplacian_phi2_mid - j2_mid)",
            "phi2 descendant sourced wave update",
        ),
        (
            "PHI3_KINEMATIC",
            "phi3",
            "phi3_next - phi3_previous - dt * (P3_mid / a)",
            "phi3 descendant kinematic update",
        ),
        (
            "P3_DYNAMIC",
            "P3",
            "P3_next - P3_previous - dt * a * (laplacian_phi3_mid - j3_mid)",
            "phi3 descendant sourced wave update",
        ),
        (
            "DIRAC_PLUS",
            "psi_plus",
            "psi_plus_next - psi_plus_previous + i * dt * H_plus(midpoint)",
            "positive-charge Wilson-Dirac update; real and imaginary packed entries share one block",
        ),
        (
            "DIRAC_MINUS",
            "psi_minus",
            "psi_minus_next - psi_minus_previous + i * dt * H_minus(midpoint)",
            "negative-charge Wilson-Dirac update; real and imaginary packed entries share one block",
        ),
    ]
    return [
        {
            "block_index": index,
            "block_id": block_id,
            "packed_state_key": state_key,
            "block_kind": "IMPLEMENTED_IMPLICIT_MIDPOINT_UPDATE_BLOCK",
            "mathematical_residual": formula,
            "discrete_residual_expression": formula,
            "meaning": meaning,
            "raw_units": "dimensionless packed code-state update unit",
            "raw_norm": "L_infinity over every packed-real entry in this block",
            "normalization_scale": (
                "max(requested_solver_tolerance, gamma_64); the requested tolerance is "
                "the per-role scale because the fixed-point solver stops in the same packed-real L_infinity norm"
            ),
            "normalization_floor": GAMMA64,
            "normalized_residual_formula": (
                "raw_block_Linf / max(requested_solver_tolerance, gamma_64)"
            ),
            "spatial_aggregation": (
                "L_infinity over packed-real entries; Dirac real and imaginary components remain separate entries"
            ),
            "time_aggregation": (
                "preserve every postinitial step; classifier summaries use the terminal nonlinear iteration per step"
            ),
            "solver_iteration_aggregation": (
                "preserve every iteration including iteration zero; terminal block values are separately registered"
            ),
            "missing_data_behavior": "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
        }
        for index, (block_id, state_key, formula, meaning) in enumerate(records)
    ]


def _observable_registry(output_schema_version: str) -> list[dict[str, Any]]:
    common = {
        "required_for_instrumented_roles": True,
        "missing_nonfinite_or_shape_mismatch_behavior": (
            "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
        ),
        "schema_version": output_schema_version,
    }
    records = [
        {
            "observable_id": "EXCHANGE_FIELD_LONGITUDINAL_RAW",
            "payload_field": (
                "raw_events.exchange[*].x_field_cell_contribution and x_field_integral"
            ),
            "hypothesis_links": ["H_A_CANCELLATION_CONDITIONING"],
            "meaning": "field-sector longitudinal exchange increment before cancellation",
            "formula": (
                "X_field[step] = E_electric_next - E_electric_previous"
            ),
            "unit": "canonical dimensionless code-energy unit",
            "dtype": "finite float64",
            "shape": {
                "cell_contribution": [16, 16],
                "spatial_integral": [16],
            },
            "aggregation": (
                "preserve all 16x16 cell contributions and the registered per-step spatial sum; independently "
                "recompute and require exact sum closure"
            ),
        },
        {
            "observable_id": "EXCHANGE_MATTER_LONGITUDINAL_RAW",
            "payload_field": (
                "raw_events.exchange[*].x_matter_cell_contribution and x_matter_integral"
            ),
            "hypothesis_links": ["H_A_CANCELLATION_CONDITIONING"],
            "meaning": "longitudinal matter-field work-channel increment in the frozen sign convention",
            "formula": "X_matter[step] = dt * sum_x(grad_theta_mid * theta_dot_mid)",
            "unit": "same canonical dimensionless code-energy unit as X_field",
            "dtype": "finite float64",
            "shape": {
                "cell_contribution": [16, 16],
                "spatial_integral": [16],
            },
            "aggregation": (
                "preserve all 16x16 cell contributions and the registered per-step spatial sum; independently "
                "recompute and require exact sum closure"
            ),
        },
        {
            "observable_id": "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
            "payload_field": "raw_events.exchange[*].remainder_integral",
            "hypothesis_links": ["H_A_CANCELLATION_CONDITIONING"],
            "meaning": "field-energy plus work-channel increment remainder",
            "formula": "R_exchange[step] = X_field[step] + X_matter[step]",
            "unit": "canonical dimensionless code-energy unit",
            "dtype": "finite float64",
            "shape": [16],
            "aggregation": "preserve all 16 postinitial steps; median and maximum are derived without point selection",
        },
        {
            "observable_id": "EXCHANGE_CANCELLATION_KAPPA",
            "payload_field": "raw_events.exchange[*].kappa",
            "hypothesis_links": ["H_A_CANCELLATION_CONDITIONING"],
            "meaning": "additively roundoff-floored cancellation conditioning",
            "formula": (
                "S=abs(X_field)+abs(X_matter); kappa=0 when S=0, otherwise "
                "S/(abs(X_field+X_matter)+gamma_64*S)"
            ),
            "unit": "dimensionless",
            "dtype": "finite float64",
            "shape": [16],
            "floor": {
                "kind": "ADDITIVE_SCALE_RELATIVE_HIGHAM_GAMMA",
                "operation_count": 64,
                "unit_roundoff": FLOAT64_UNIT_ROUNDOFF,
                "gamma_64": GAMMA64,
                "numerator_zero_value": 0.0,
            },
            "aggregation": (
                "median across exactly 16 postinitial steps; severe-step fraction counts kappa >= 1e6"
            ),
        },
        {
            "observable_id": "SOLVER_BLOCK_RESIDUAL_RAW",
            "payload_field": (
                "raw_events.solver_steps[*].iteration_events[*].packed_real_block_maxima "
                "and raw_events.terminal_equation_blocks[*].packed_real_block_maxima"
            ),
            "hypothesis_links": [
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "packed-real implicit-midpoint update defect by exact implemented block",
            "formula": "the eight block formulas in equation_block_registry",
            "unit": "dimensionless packed code-state update unit by block",
            "dtype": "finite float64",
            "shape": {
                "iteration_update_blocks": [16, "1..80 update events indexed from 0", 8],
                "terminal_equation_blocks": [16, 8],
            },
            "aggregation": "L_infinity within each block; preserve every step and iteration",
        },
        {
            "observable_id": "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
            "payload_field": (
                "raw_events.solver_steps[*].iteration_events[*].normalized_block_magnitudes "
                "and raw_events.terminal_equation_blocks[*].normalized_block_magnitudes"
            ),
            "hypothesis_links": [
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "raw block defect divided by the frozen per-role solver scale",
            "formula": "raw / max(requested_solver_tolerance, gamma_64)",
            "unit": "dimensionless",
            "dtype": "finite nonnegative float64",
            "shape": {
                "iteration_update_blocks": [16, "1..80 update events indexed from 0", 8],
                "terminal_equation_blocks": [16, 8],
            },
            "floor": GAMMA64,
            "aggregation": "preserve every step and iteration; terminal iteration is decision-bearing",
        },
        {
            "observable_id": "SOLVER_BLOCK_DOMINANCE_FRACTION",
            "payload_field": (
                "raw_events.solver_steps[*].iteration_events[*].dominance_share_by_block "
                "and raw_events.terminal_equation_blocks[*].dominance_share_by_block"
            ),
            "hypothesis_links": [
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "relative normalized defect share by block",
            "formula": "D_b = normalized_b / (sum_c(normalized_c) + gamma_64)",
            "unit": "dimensionless",
            "dtype": "finite nonnegative float64",
            "shape": {
                "iteration_update_blocks": [16, "1..80 update events indexed from 0", 8],
                "terminal_equation_blocks": [16, 8],
            },
            "floor": GAMMA64,
            "aggregation": (
                "terminal-iteration shares per step; median by block uses all 16 steps; block-id ties use registry order"
            ),
        },
        {
            "observable_id": "SOLVER_ITERATION_METADATA",
            "payload_field": "raw_events.solver_steps[*]",
            "hypothesis_links": [
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "exact fixed-point iteration and stopping history",
            "formula": "direct implementation metadata; no inferred iteration records",
            "unit": "mixed registered metadata",
            "dtype": "JSON records with finite numeric members",
            "shape": [16, "per-step record with 1..80 iteration records"],
            "required_fields": [
                "requested_tolerance",
                "iteration_count",
                "terminal_solver_residual",
                "terminal_update_residual",
                "terminal_equation_residual",
                "stopping_reason",
                "converged",
                "step_accepted",
                "damping",
                "line_search",
                "jacobian",
                "preconditioner",
                "conditioning_estimate",
                "iteration_events",
            ],
            "aggregation": "no omitted iterations; unsupported damping or conditioning is explicit NOT_APPLICABLE",
        },
        {
            "observable_id": "GAUSS_RESIDUAL_FIELD",
            "payload_field": "raw_events.spatial_constraints[*].gauss_residual_field",
            "hypothesis_links": [
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_C_DISCRETE_CLOSURE_MISMATCH",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "actual periodic discrete Gauss residual field",
            "formula": "G = roll(p, 1) - p + a*rho",
            "unit": "canonical dimensionless Gauss equation-residual unit",
            "dtype": "finite float64",
            "shape": [16, 16],
            "aggregation": (
                "preserve all 16 postinitial raw fields and separately store L_infinity, grid-weighted L2, "
                "and lowest-index argmax; every summary is recomputable from the raw field"
            ),
        },
        {
            "observable_id": "CONTINUITY_RESIDUAL_FIELD",
            "payload_field": "raw_events.spatial_constraints[*].continuity_residual_field",
            "hypothesis_links": [
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_C_DISCRETE_CLOSURE_MISMATCH",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "actual midpoint discrete current-continuity field",
            "formula": (
                "C = (rho_next-rho_previous)/dt + "
                "(grad_theta_mid-roll(grad_theta_mid,1))/a"
            ),
            "unit": "canonical dimensionless charge-rate residual unit",
            "dtype": "finite float64",
            "shape": [16, 16],
            "aggregation": (
                "preserve each raw field and separately store L_infinity, grid-weighted L2, and lowest-index "
                "argmax; every summary is recomputable from the raw field"
            ),
        },
        {
            "observable_id": "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
            "payload_field": (
                "raw_events.spatial_constraints[*].longitudinal_theta_equation_defect and "
                "raw_events.spatial_constraints[*].longitudinal_p_equation_defect"
            ),
            "hypothesis_links": [
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_C_DISCRETE_CLOSURE_MISMATCH",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "theta-kinematic and p-Maxwell packed update-defect fields",
            "formula": "the THETA_KINEMATIC and P_LONGITUDINAL_MAXWELL block fields",
            "unit": "dimensionless packed code-state update unit by component",
            "dtype": "finite float64",
            "shape": [16, 2, 16],
            "component_order": ["THETA_KINEMATIC", "P_LONGITUDINAL_MAXWELL"],
            "aggregation": (
                "preserve both raw component fields; separately store grid-weighted L2 and lowest-index argmax; "
                "cross-check packed-real L_infinity against terminal block maxima"
            ),
        },
        {
            "observable_id": "DISCRETE_OPERATOR_OUTPUTS",
            "payload_field": (
                "raw_events.discrete_closure[*].operator_inputs, actual_discrete_operator_outputs, "
                "gauss_previous, gauss_current, p_equation_defect, continuity_residual, "
                "p_defect_divergence, and continuity_increment"
            ),
            "hypothesis_links": ["H_C_DISCRETE_CLOSURE_MISMATCH"],
            "meaning": "all exact terms required to independently rebuild the implemented closure identity",
            "formula": "direct saved G_previous, G_next, p_defect, rho_previous, rho_next, and grad_theta_mid arrays",
            "unit": "registered per field",
            "dtype": "finite float64",
            "shape": [16, "registered component", 16],
            "required_components": [
                "operator_inputs.p_previous",
                "operator_inputs.p_current",
                "operator_inputs.rho_previous",
                "operator_inputs.rho_current",
                "operator_inputs.grad_theta_midpoint",
                "operator_inputs.a",
                "operator_inputs.dt",
                "gauss_previous",
                "gauss_current",
                "p_equation_defect",
                "continuity_residual",
                "p_defect_divergence",
                "continuity_increment",
                "actual_discrete_operator_outputs",
            ],
            "aggregation": "raw arrays mandatory; summaries cannot substitute",
        },
        {
            "observable_id": "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
            "payload_field": (
                "raw_events.discrete_closure[*].closure_q, roundoff_bound, and roundoff_bound_ratio"
            ),
            "hypothesis_links": ["H_C_DISCRETE_CLOSURE_MISMATCH"],
            "meaning": "scheme-derived step-integrated discrete Maxwell-to-continuity closure",
            "formula": (
                "Q = G_next - G_previous - (roll(p_defect,1)-p_defect) - a*dt*C"
            ),
            "unit": "canonical dimensionless Gauss-residual update unit",
            "dtype": "finite float64",
            "shape": [16, 16],
            "roundoff_bound": (
                "B = gamma_32 * (abs(roll(p_next,1))+abs(p_next)+abs(a*rho_next)"
                "+abs(roll(p_previous,1))+abs(p_previous)+abs(a*rho_previous)"
                "+abs(roll(p_defect,1))+abs(p_defect)+abs(a*dt*C)); "
                "ratio=0 for 0/0; positive/0 is invalid"
            ),
            "aggregation": "max ratio and maximum consecutive ratio>1 run over all 16 steps and sites",
        },
        {
            "observable_id": "INSTRUMENTATION_TRAJECTORY_IDENTITY",
            "payload_field": "physical_trajectory and physical_trajectory_sha256",
            "hypothesis_links": [
                "H_A_CANCELLATION_CONDITIONING",
                "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
                "H_C_DISCRETE_CLOSURE_MISMATCH",
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
            ],
            "meaning": "canonical hash of the physical trajectory projection for each paired role",
            "formula": (
                "domain-separated SHA-256 of the C-order bytes, shape, and dtype of exactly the 17 packed "
                "float64 physical-state snapshots; instrumentation events, convergence flags, solver metadata, "
                "and other summaries are excluded from this hash and checked separately"
            ),
            "unit": "cryptographic identity",
            "dtype": {
                "physical_trajectory": "float64",
                "physical_trajectory_sha256": "64-character lowercase SHA-256 hex",
            },
            "shape": {
                "physical_trajectory": [17, 352],
                "physical_trajectory_sha256": [1],
            },
            "aggregation": "exact equality within each of three instrumented/noninstrumented pairs",
        },
    ]
    if [item["observable_id"] for item in records] != OBSERVABLE_IDS:
        raise ValueError("internal observable registry order mismatch")
    return [{**common, **item} for item in records]


def _paired_run_id(configuration_role: str, instrumentation_enabled: bool) -> str:
    matches = [
        run_id
        for run_id, role, enabled in RUN_SPECS
        if role == configuration_role and enabled is not instrumentation_enabled
    ]
    if len(matches) != 1:
        raise ValueError(f"pairing is not unique for {configuration_role}")
    return matches[0]


def build_run_matrix(implementation: dict[str, Any]) -> dict[str, Any]:
    canonical_matrix = load_json(CANONICAL_MATRIX_RELATIVE_PATH)
    canonical_execution = load_json(CANONICAL_EXECUTION_MANIFEST_RELATIVE_PATH)
    canonical_by_run = {
        item["run_id"]: item for item in canonical_matrix["records"]
    }
    execution_by_run = {
        item["run_id"]: item for item in canonical_execution["run_outputs"]
    }
    records: list[dict[str, Any]] = []
    for execution_index, (run_id, configuration_role, instrumentation_enabled) in enumerate(RUN_SPECS):
        parent_run_id = PARENT_CANONICAL_RUN_IDS[configuration_role]
        parent = canonical_by_run[parent_run_id]
        parent_output = execution_by_run[parent_run_id]
        if parent["input_hash"] != EXPECTED_PARENT_INPUT_HASHES[configuration_role]:
            raise ValueError(f"parent canonical input hash mismatch: {configuration_role}")
        output_stem = f"{execution_index:02d}-{run_id.replace(':', '_')}"
        json_safe_filename = output_stem + ".json"
        npz_safe_filename = output_stem + ".npz"
        json_output_path = f"{EXPERIMENT_OUTPUT_ROOT}/{json_safe_filename}"
        npz_output_path = f"{EXPERIMENT_OUTPUT_ROOT}/{npz_safe_filename}"
        row = {
            "row_id": parent["scientific_row_id"],
            **copy.deepcopy(parent["requested_axis_values"]),
        }
        record: dict[str, Any] = {
            "run_id": run_id,
            "experiment_id": (
                "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
                "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_v0"
            ),
            "mechanism_configuration_role": configuration_role,
            "execution_role": (
                "INSTRUMENTED_MECHANISM_RUN"
                if instrumentation_enabled
                else "PAIRED_NONINSTRUMENTED_CONTROL"
            ),
            "instrumentation_enabled": instrumentation_enabled,
            "paired_run_id": _paired_run_id(
                configuration_role, instrumentation_enabled
            ),
            "scientific_row_id": parent["scientific_row_id"],
            "parent_canonical_run_id": parent_run_id,
            "parent_canonical_input_hash": parent["input_hash"],
            "parent_canonical_output_path": parent_output["relative_output_path"],
            "parent_canonical_output_sha256": parent_output["output_sha256"],
            "parent_initial_condition_identity": parent["initial_condition_identity"],
            "requested_axis_values": copy.deepcopy(parent["requested_axis_values"]),
            "row": row,
            "model_class": parent["model_or_comparator_class"],
            "numerical_method": "fixed-point implicit midpoint as implemented by the bound accepted source",
            "grid_size": int(parent["grid_size"]),
            "time_step": float(parent["time_step"]),
            "n": int(parent["grid_size"]),
            "dt": float(parent["time_step"]),
            "duration": float(parent["duration"]),
            "accepted_step_count": 16,
            "checkpoint_count_including_initial": 17,
            "solver_tolerance": float(parent["solver_tolerance"]),
            "iteration_cap": int(parent["iteration_cap"]),
            "tolerance": float(parent["solver_tolerance"]),
            "max_iterations": int(parent["iteration_cap"]),
            "implementation_id": implementation["implementation_id"],
            "implementation_sha256": implementation["sha256"],
            "output_schema_version": implementation["output_schema_version"],
            "instrumented_observable_ids": (
                list(OBSERVABLE_IDS) if instrumentation_enabled else []
            ),
            "trajectory_identity_required": True,
            "instrumentation_read_only": True,
            "supporting_tolerance_ladder_module_enabled": False,
            "supporting_duration_scaling_module_enabled": False,
            "execution_ordinal_zero_based": execution_index,
            "json_safe_filename": json_safe_filename,
            "npz_safe_filename": npz_safe_filename,
            "json_relative_output_path": json_output_path,
            "npz_relative_output_path": npz_output_path,
        }
        input_material = {
            key: value
            for key, value in record.items()
            if key
            not in {
                "json_safe_filename",
                "npz_safe_filename",
                "json_relative_output_path",
                "npz_relative_output_path",
                "input_hash",
                "payload_identity_contract",
            }
        }
        record["input_hash"] = sha256_bytes(canonical_json_bytes(input_material))
        record["input_hash_material_excludes"] = [
            "json_safe_filename",
            "npz_safe_filename",
            "json_relative_output_path",
            "npz_relative_output_path",
            "input_hash",
            "payload_identity_contract",
        ]
        record["payload_identity_contract"] = {
            "role_payload_required_echo_fields": [
                "role_id",
                "row_id",
                "instrumentation_enabled",
                "implementation_id",
                "configuration.N",
                "configuration.requested_dt",
                "configuration.duration",
                "configuration.solver_tolerance",
                "configuration.max_iterations",
                "configuration.row",
            ],
            "matrix_result_custody_required_fields": [
                "run_id",
                "execution_ordinal",
                "json_relative_output_path",
                "npz_relative_output_path",
                "json_sha256",
                "npz_sha256",
                "physical_trajectory_sha256",
            ],
            "input_hash_is_matrix_identity_not_role_payload_echo": True,
            "mismatch_behavior": "BLOCKED_RUN_IDENTITY",
        }
        records.append(record)
    run_ids = [item["run_id"] for item in records]
    filenames = [
        filename
        for item in records
        for filename in (item["json_safe_filename"], item["npz_safe_filename"])
    ]
    paths = [
        path
        for item in records
        for path in (
            item["json_relative_output_path"],
            item["npz_relative_output_path"],
        )
    ]
    if run_ids != classifier.EXPECTED_RUN_IDS:
        raise ValueError("six-run order does not match classifier EXPECTED_RUN_IDS")
    if not (
        len(records)
        == len(set(run_ids))
        == 6
    ):
        raise ValueError("mechanism run/output identity is not a six-element bijection")
    if len(filenames) != len(set(filenames)) or len(paths) != len(set(paths)) or len(paths) != 12:
        raise ValueError("mechanism JSON/NPZ output identity is not a twelve-path bijection")
    if len(
        {unicodedata.normalize("NFC", item).casefold() for item in filenames}
    ) != 12:
        raise ValueError("mechanism filenames collide under Windows NFC/casefold")
    for record in records:
        paired = next(item for item in records if item["run_id"] == record["paired_run_id"])
        comparison_exclusions = {
            "run_id",
            "execution_role",
            "instrumentation_enabled",
            "paired_run_id",
            "instrumented_observable_ids",
            "execution_ordinal_zero_based",
            "json_safe_filename",
            "npz_safe_filename",
            "json_relative_output_path",
            "npz_relative_output_path",
            "input_hash",
            "payload_identity_contract",
            "input_hash_material_excludes",
        }
        left = {key: value for key, value in record.items() if key not in comparison_exclusions}
        right = {key: value for key, value in paired.items() if key not in comparison_exclusions}
        if left != right:
            raise ValueError(f"paired physical configuration differs: {record['run_id']}")
        if not (
            record["grid_size"] == record["n"] == 16
            and record["time_step"] == record["dt"] == 0.003125
            and record["solver_tolerance"] == record["tolerance"]
            and record["iteration_cap"] == record["max_iterations"] == 80
            and record["row"]
            == {"row_id": record["scientific_row_id"], **record["requested_axis_values"]}
        ):
            raise ValueError(f"descriptive alias mismatch: {record['run_id']}")
        expected_paths = implementation["literal_expected_output_paths_by_run_id"][
            record["run_id"]
        ]
        if {
            "json_relative_output_path": record["json_relative_output_path"],
            "npz_relative_output_path": record["npz_relative_output_path"],
        } != expected_paths:
            raise ValueError(f"implementation output-path mismatch: {record['run_id']}")
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_RUN_MATRIX_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "generation_policy": (
            "exact minimal Route-A mechanism matrix: three physical configurations, "
            "each paired with one otherwise identical noninstrumented control"
        ),
        "record_count": 6,
        "physical_configuration_count": 3,
        "instrumented_record_count": 3,
        "noninstrumented_control_record_count": 3,
        "expected_run_id_order": list(classifier.EXPECTED_RUN_IDS),
        "unique_run_id_count": 6,
        "unique_filename_count": 12,
        "json_output_count": 6,
        "npz_output_count": 6,
        "role_counts": dict(sorted(Counter(item["execution_role"] for item in records).items())),
        "fixed_numerical_settings": {
            "grid_size": 16,
            "time_step": 0.003125,
            "duration": 0.05,
            "accepted_step_count": 16,
            "checkpoint_count_including_initial": 17,
            "iteration_cap": 80,
            "tolerances_by_configuration": {
                "R13_LOOSE": 1.0e-8,
                "R13_TIGHT": 1.0e-12,
                "R10_LOOSE_NEIGHBOR": 1.0e-8,
            },
        },
        "selection_rules_closed": {
            "tight_R13": (
                "tightest previously registered passing R13 solver-verification role"
            ),
            "matched_neighbor": (
                "unique top-ranked eligible row under accepted design-v1 tuple "
                "(-shared_axis_count, normalized_distance, scientific_row_id): R10_MU_HIGH"
            ),
            "pairing_multiplicity": "exactly one instrumented and one noninstrumented run per configuration",
            "additional_tolerance_roles": "none",
            "additional_duration_roles": "none",
        },
        "records": records,
    }


def build_output_identity(matrix: dict[str, Any]) -> dict[str, Any]:
    outputs = [
        {
            "run_id": record["run_id"],
            "json_safe_filename": record["json_safe_filename"],
            "npz_safe_filename": record["npz_safe_filename"],
            "json_relative_output_path": record["json_relative_output_path"],
            "npz_relative_output_path": record["npz_relative_output_path"],
            "input_hash": record["input_hash"],
            "mechanism_configuration_role": record["mechanism_configuration_role"],
            "execution_role": record["execution_role"],
            "instrumentation_enabled": record["instrumentation_enabled"],
            "paired_run_id": record["paired_run_id"],
            "scientific_row_id": record["scientific_row_id"],
            "parent_canonical_run_id": record["parent_canonical_run_id"],
            "implementation_id": record["implementation_id"],
            "implementation_sha256": record["implementation_sha256"],
            "output_schema_version": record["output_schema_version"],
        }
        for record in matrix["records"]
    ]
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_EXPECTED_"
            "OUTPUT_IDENTITY_MANIFEST_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "mapping_contract": (
            "run_id <-> ordered JSON and NPZ filenames <-> relative output paths <-> input hash <-> "
            "payload identity is exact, reversible, casefold-safe, and fail-closed"
        ),
        "output_root": EXPERIMENT_OUTPUT_ROOT,
        "output_root_must_be_absent_before_authorized_execution": True,
        "record_count": 6,
        "role_payload_file_count": 12,
        "auxiliary_execution_files": [
            {
                "relative_output_path": f"{EXPERIMENT_OUTPUT_ROOT}/EXECUTION-STARTED.json",
                "creation_order": "before first role",
                "exclusive_no_overwrite": True,
            },
            {
                "relative_output_path": f"{EXPERIMENT_OUTPUT_ROOT}/MATRIX-RESULT.json",
                "creation_order": "after all six roles",
                "exclusive_no_overwrite": True,
            },
        ],
        "complete_expected_file_count_after_success": 14,
        "run_id_to_json_safe_filename": {
            item["run_id"]: item["json_safe_filename"] for item in outputs
        },
        "json_safe_filename_to_run_id": {
            item["json_safe_filename"]: item["run_id"] for item in outputs
        },
        "run_id_to_npz_safe_filename": {
            item["run_id"]: item["npz_safe_filename"] for item in outputs
        },
        "npz_safe_filename_to_run_id": {
            item["npz_safe_filename"]: item["run_id"] for item in outputs
        },
        "run_id_to_json_relative_output_path": {
            item["run_id"]: item["json_relative_output_path"] for item in outputs
        },
        "json_relative_output_path_to_run_id": {
            item["json_relative_output_path"]: item["run_id"] for item in outputs
        },
        "run_id_to_npz_relative_output_path": {
            item["run_id"]: item["npz_relative_output_path"] for item in outputs
        },
        "npz_relative_output_path_to_run_id": {
            item["npz_relative_output_path"]: item["run_id"] for item in outputs
        },
        "outputs": outputs,
        "identity_failure_behavior": "BLOCKED_RUN_IDENTITY",
        "missing_duplicate_orphan_overwrite_or_retry_behavior": "BLOCKED_RUN_IDENTITY",
    }


def _base_classifier_fixture() -> dict[str, Any]:
    block_shares = {
        block_id: (0.20 if block_id == "DIRAC_PLUS" else 0.10)
        for block_id in BLOCK_IDS
    }
    return {
        "custody_passed": True,
        "observed_run_ids": list(classifier.EXPECTED_RUN_IDS),
        "required_payloads_complete": True,
        "required_observables_complete": True,
        "separate_output_custody_passed": True,
        "instrumentation_nonperturbation_passed": True,
        "observable_semantics_passed": True,
        "discrete_operator_binding_passed": True,
        "metrics": {
            "exchange_conditioning": {
                role: {
                    "median_kappa": 10.0,
                    "severe_step_fraction": 0.0,
                    "sample_count": 16,
                }
                for role in classifier.ROLE_KEYS
            },
            "block_dominance": {
                role: {
                    "dominant_block_id": "DIRAC_PLUS",
                    "median_dominance_share": 0.20,
                    "dominant_step_fraction": 0.25,
                    "median_share_by_block": copy.deepcopy(block_shares),
                }
                for role in classifier.ROLE_KEYS
            },
            "discrete_closure": {
                role: {
                    "max_roundoff_bound_ratio": 0.5,
                    "maximum_consecutive_violation_steps": 0,
                    "sample_count": 16,
                }
                for role in classifier.ROLE_KEYS
            },
            "distributed_accumulation": {
                role: {
                    "distributed_step_fraction": 0.25,
                    "linked_series_maxima_at_final_count": 3,
                    "minimum_nondecreasing_increment_count": 10,
                }
                for role in classifier.ROLE_KEYS
            },
        },
    }


def _classifier_control_suite() -> dict[str, Any]:
    fixtures: list[dict[str, Any]] = []

    def register(
        control_id: str,
        fixture: dict[str, Any],
        expected_supported: list[str],
        expected_aggregate: str,
    ) -> None:
        result = classifier.classify(fixture)
        diagnostics = classifier.validate_result(result)
        if diagnostics:
            raise ValueError(f"classifier positive control invalid: {control_id}: {diagnostics}")
        if (
            result["evidence_result"] != "EVIDENCE_ADMISSIBLE"
            or result["supported_mechanism_ids"] != expected_supported
            or result["aggregate_mechanism_result"] != expected_aggregate
        ):
            raise ValueError(f"classifier positive control mismatch: {control_id}: {result}")
        fixtures.append(
            {
                "control_id": control_id,
                "fixture": fixture,
                "expected_supported_mechanism_ids": expected_supported,
                "expected_aggregate_mechanism_result": expected_aggregate,
                "actual_result": result,
                "passed": True,
                "scientific_execution_record": False,
            }
        )

    unresolved = _base_classifier_fixture()
    register(
        "P_CLASSIFIER_COMPLETE_NONDISTINGUISHING_EVIDENCE",
        unresolved,
        [],
        "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
    )

    h_a = _base_classifier_fixture()
    h_a["metrics"]["exchange_conditioning"]["R13_LOOSE"].update(
        {"median_kappa": 1.0e7, "severe_step_fraction": 0.75}
    )
    for role in ("R13_TIGHT", "R10_LOOSE_NEIGHBOR"):
        h_a["metrics"]["exchange_conditioning"][role]["median_kappa"] = 1.0e5
    register(
        "P_CLASSIFIER_H_A_ONLY",
        h_a,
        ["H_A_CANCELLATION_CONDITIONING"],
        "SINGLE_SUPPORTED_MECHANISM",
    )

    h_b = _base_classifier_fixture()
    h_b_loose = h_b["metrics"]["block_dominance"]["R13_LOOSE"]
    h_b_loose.update(
        {
            "dominant_block_id": "P_LONGITUDINAL_MAXWELL",
            "median_dominance_share": 0.60,
            "dominant_step_fraction": 0.75,
        }
    )
    h_b_loose["median_share_by_block"]["P_LONGITUDINAL_MAXWELL"] = 0.60
    for role in ("R13_TIGHT", "R10_LOOSE_NEIGHBOR"):
        h_b["metrics"]["block_dominance"][role]["median_share_by_block"][
            "P_LONGITUDINAL_MAXWELL"
        ] = 0.20
    register(
        "P_CLASSIFIER_H_B_ONLY",
        h_b,
        ["H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE"],
        "SINGLE_SUPPORTED_MECHANISM",
    )

    h_c = _base_classifier_fixture()
    h_c["metrics"]["discrete_closure"]["R13_LOOSE"].update(
        {
            "max_roundoff_bound_ratio": 20.0,
            "maximum_consecutive_violation_steps": 2,
        }
    )
    h_c["metrics"]["discrete_closure"]["R13_TIGHT"][
        "max_roundoff_bound_ratio"
    ] = 1.0
    h_c["metrics"]["discrete_closure"]["R10_LOOSE_NEIGHBOR"][
        "max_roundoff_bound_ratio"
    ] = 5.0
    register(
        "P_CLASSIFIER_H_C_ONLY",
        h_c,
        ["H_C_DISCRETE_CLOSURE_MISMATCH"],
        "SINGLE_SUPPORTED_MECHANISM",
    )

    h_d = _base_classifier_fixture()
    h_d["metrics"]["distributed_accumulation"]["R13_LOOSE"].update(
        {
            "distributed_step_fraction": 0.75,
            "linked_series_maxima_at_final_count": 4,
            "minimum_nondecreasing_increment_count": 14,
        }
    )
    register(
        "P_CLASSIFIER_H_D_ONLY",
        h_d,
        ["H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR"],
        "SINGLE_SUPPORTED_MECHANISM",
    )

    h_a_h_b = copy.deepcopy(h_a)
    h_a_h_b["metrics"]["block_dominance"] = copy.deepcopy(
        h_b["metrics"]["block_dominance"]
    )
    register(
        "P_CLASSIFIER_MULTIPLE_H_A_H_B",
        h_a_h_b,
        [
            "H_A_CANCELLATION_CONDITIONING",
            "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
        ],
        "MULTIPLE_SUPPORTED_MECHANISMS",
    )

    negative = classifier.mutation_controls(_base_classifier_fixture())
    if not negative or not all(item["passed"] for item in negative):
        raise ValueError("classifier negative controls did not all discriminate")
    return {
        "positive_control_count": len(fixtures),
        "negative_control_count": len(negative),
        "positive_controls": fixtures,
        "negative_controls": negative,
        "all_controls_passed": True,
        "fixtures_are_classifier_unit_controls_not_scientific_runs": True,
    }


def _freeze_adversarial_control_registry() -> list[dict[str, Any]]:
    controls = [
        {
            "control_id": "M_FREEZE_CANDIDATE_RUN_OMITTED",
            "mutation": "remove the final R10 noninstrumented record from the exact matrix",
            "audit_method": "EXECUTABLE_BOUND_IMPLEMENTATION_MATRIX_AUDIT",
            "audit_entrypoint": f"{IMPLEMENTATION_RELATIVE_PATH}:validate_exact_run_matrix",
            "expected_first_diagnostic": "RUN_MATRIX_COUNT_MISMATCH",
            "expected_evidence_result": "BLOCKED_RUN_IDENTITY",
            "expected_decision_change": "EVIDENCE_ADMISSIBILITY_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
        {
            "control_id": "M_FREEZE_R10_NEIGHBOR_DISPLACED",
            "mutation": "replace the R10 row payload in MECHv0:R10_LOOSE:INSTRUMENTED with any other row",
            "audit_method": "EXECUTABLE_BOUND_IMPLEMENTATION_MATRIX_AUDIT",
            "audit_entrypoint": f"{IMPLEMENTATION_RELATIVE_PATH}:validate_exact_run_matrix",
            "expected_first_diagnostic": "RUN_MATRIX_ROW_ID_MISMATCH:MECHv0:R10_LOOSE:INSTRUMENTED",
            "expected_evidence_result": "BLOCKED_RUN_IDENTITY",
            "expected_decision_change": "EXACT_NEIGHBOR_FREEZE_TO_BLOCKED",
        },
        {
            "control_id": "M_FREEZE_MULTIPLE_AGGREGATE_IDS_REMOVED",
            "mutation": "delete supported_mechanism_ids from a MULTIPLE_SUPPORTED_MECHANISMS result",
            "audit_method": "EXECUTABLE_CLASSIFIER_RESULT_VALIDATION",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:validate_result",
            "expected_first_diagnostic": "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING",
            "expected_evidence_result": "RESULT_INVALID",
            "expected_decision_change": "MULTIPLE_SUPPORTED_MECHANISMS_TO_REJECTED_RESULT",
        },
        {
            "control_id": "M_FREEZE_SUPPORTED_IDENTITY_SET_MISMATCH",
            "mutation": "replace ordered supported_mechanism_ids with a set inconsistent with individual decisions",
            "audit_method": "EXECUTABLE_CLASSIFIER_RESULT_VALIDATION",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:validate_result",
            "expected_first_diagnostic": "SUPPORTED_MECHANISM_IDENTITY_SET_MISMATCH",
            "expected_evidence_result": "RESULT_INVALID",
            "expected_decision_change": "SUPPORTED_RESULT_TO_REJECTED_RESULT",
        },
        {
            "control_id": "M_FREEZE_H_D_WITHOUT_POSITIVE_EVIDENCE",
            "mutation": "mark H_D SUPPORTED while one or more H_D necessary criteria are FAILED",
            "audit_method": "EXECUTABLE_CLASSIFIER_RESULT_VALIDATION",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:validate_result",
            "expected_first_diagnostic": (
                "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR_AWARDED_WITHOUT_POSITIVE_EVIDENCE"
            ),
            "expected_evidence_result": "RESULT_INVALID",
            "expected_decision_change": "H_D_SUPPORTED_TO_REJECTED_RESULT",
        },
        {
            "control_id": "M_FREEZE_H_E_WITH_MISSING_OBSERVABLE",
            "mutation": (
                "after required_observables_complete=false blocks evidence, illegally mark H_E SUPPORTED "
                "and label the aggregate unresolved"
            ),
            "audit_method": "EXECUTABLE_CLASSIFIER_RESULT_VALIDATION",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:validate_result",
            "expected_first_diagnostic": "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED",
            "expected_evidence_result": "RESULT_INVALID",
            "expected_decision_change": "ILLEGAL_H_E_UNRESOLVED_TO_REJECTED_RESULT",
        },
        {
            "control_id": "M_FREEZE_CLASSIFICATION_AFTER_NONPERTURBATION_FAILURE",
            "mutation": (
                "after instrumentation_nonperturbation_passed=false blocks evidence, illegally mark one "
                "physical hypothesis SUPPORTED"
            ),
            "audit_method": "EXECUTABLE_CLASSIFIER_RESULT_VALIDATION",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:validate_result",
            "expected_first_diagnostic": "CLASSIFICATION_PERFORMED_AFTER_EVIDENCE_BLOCK",
            "expected_evidence_result": "RESULT_INVALID",
            "expected_decision_change": "POST_BLOCK_CLASSIFICATION_TO_REJECTED_RESULT",
        },
        {
            "control_id": "M_FREEZE_CONTINUUM_OPERATOR_SUBSTITUTED",
            "mutation": "set discrete_operator_binding_passed false after substituting a continuum operator",
            "audit_method": "EXECUTABLE_CLASSIFIER_GATE_MUTATION",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:classify",
            "expected_first_diagnostic": "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
            "expected_evidence_result": "BLOCKED_OPERATOR_BINDING",
            "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
        {
            "control_id": "M_FREEZE_OUTPUT_ROOT_COLLIDES_CANONICAL",
            "mutation": "set the future experiment output root equal to or inside the canonical output root",
            "audit_method": "EXECUTABLE_CLASSIFIER_GATE_AND_STATIC_PATH_AUDIT",
            "audit_entrypoint": (
                f"{CLASSIFIER_RELATIVE_PATH}:classify and "
                f"{IMPLEMENTATION_RELATIVE_PATH}:execute_exact_matrix_once preflight"
            ),
            "expected_first_diagnostic": "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL",
            "expected_evidence_result": "BLOCKED_CUSTODY",
            "expected_decision_change": "SEPARATE_OUTPUT_CUSTODY_TO_BLOCKED",
        },
        {
            "control_id": "M_FREEZE_TRAJECTORY_BYTE_MISMATCH",
            "mutation": "change one packed float64 state byte in one instrumented trajectory only",
            "audit_method": "EXECUTABLE_CLASSIFIER_GATE_AND_IMPLEMENTATION_COMPARISON",
            "audit_entrypoint": (
                f"{IMPLEMENTATION_RELATIVE_PATH}:compare_physical_trajectories and "
                f"{CLASSIFIER_RELATIVE_PATH}:classify"
            ),
            "expected_first_diagnostic": "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL",
            "expected_evidence_result": "BLOCKED_INSTRUMENTATION_PERTURBATION",
            "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; no fallback equivalence",
        },
        {
            "control_id": "M_FREEZE_OBSERVABLE_UNITS_OR_NORMALIZATION_MISSING",
            "mutation": "remove one required unit, normalization scale, floor, or aggregation binding",
            "audit_method": "EXECUTABLE_CLASSIFIER_GATE_MUTATION",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:classify",
            "expected_first_diagnostic": "OBSERVABLE_UNIT_OR_NORMALIZATION_INVALID",
            "expected_evidence_result": "BLOCKED_OBSERVABLE_SEMANTICS",
            "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
        {
            "control_id": "M_FREEZE_UNKNOWN_OR_DUPLICATE_RUN_ID",
            "mutation": "replace one expected run ID with an unknown ID or duplicate an earlier expected run ID",
            "audit_method": "EXECUTABLE_CLASSIFIER_GATE_MUTATION_WITH_TWO_REGISTERED_VARIANTS",
            "audit_entrypoint": f"{CLASSIFIER_RELATIVE_PATH}:classify",
            "expected_first_diagnostic_by_variant": {
                "UNKNOWN_RUN_ID": "EXPECTED_RUN_ID_CLOSURE_MISMATCH",
                "DUPLICATE_RUN_ID": "DUPLICATE_RUN_IDENTITY",
            },
            "expected_evidence_result": "BLOCKED_RUN_IDENTITY",
            "expected_decision_change": "EVIDENCE_ADMISSIBLE_TO_BLOCKED; hypotheses NOT_EVALUATED",
        },
    ]
    if len(controls) != 12 or len({item["control_id"] for item in controls}) != 12:
        raise ValueError("exact twelve-control freeze adversarial registry required")
    return controls


def _execute_freeze_adversarial_classifier_checks(
    classifier_controls: dict[str, Any],
) -> list[dict[str, Any]]:
    positive_by_id = {
        item["control_id"]: item for item in classifier_controls["positive_controls"]
    }
    results: list[dict[str, Any]] = []

    def result_probe(control_id: str, result: dict[str, Any], expected: str) -> None:
        observed = classifier.validate_result(result)
        passed = observed == [expected]
        if not passed:
            raise ValueError(
                f"freeze adversarial result probe mismatch {control_id}: {observed}"
            )
        results.append(
            {
                "control_id": control_id,
                "expected_first_diagnostic": expected,
                "observed_diagnostics": observed,
                "passed": True,
            }
        )

    multiple = copy.deepcopy(
        positive_by_id["P_CLASSIFIER_MULTIPLE_H_A_H_B"]["actual_result"]
    )
    del multiple["supported_mechanism_ids"]
    result_probe(
        "M_FREEZE_MULTIPLE_AGGREGATE_IDS_REMOVED",
        multiple,
        "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING",
    )

    mismatch = copy.deepcopy(
        positive_by_id["P_CLASSIFIER_H_A_ONLY"]["actual_result"]
    )
    mismatch["supported_mechanism_ids"] = [
        "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE"
    ]
    result_probe(
        "M_FREEZE_SUPPORTED_IDENTITY_SET_MISMATCH",
        mismatch,
        "SUPPORTED_MECHANISM_IDENTITY_SET_MISMATCH",
    )

    h_d = copy.deepcopy(positive_by_id["P_CLASSIFIER_H_D_ONLY"]["actual_result"])
    h_d["hypothesis_decisions"][
        "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR"
    ]["necessary_condition_decisions"][0]["status"] = "FAILED"
    result_probe(
        "M_FREEZE_H_D_WITHOUT_POSITIVE_EVIDENCE",
        h_d,
        "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR_AWARDED_WITHOUT_POSITIVE_EVIDENCE",
    )

    missing_fixture = _base_classifier_fixture()
    missing_fixture["required_observables_complete"] = False
    missing = classifier.classify(missing_fixture)
    missing["hypothesis_decisions"][classifier.H_E]["status"] = "SUPPORTED"
    missing["aggregate_mechanism_result"] = "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    result_probe(
        "M_FREEZE_H_E_WITH_MISSING_OBSERVABLE",
        missing,
        "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED",
    )

    perturbed_fixture = _base_classifier_fixture()
    perturbed_fixture["instrumentation_nonperturbation_passed"] = False
    perturbed = classifier.classify(perturbed_fixture)
    supported_h_a = copy.deepcopy(
        positive_by_id["P_CLASSIFIER_H_A_ONLY"]["actual_result"]
        ["hypothesis_decisions"]["H_A_CANCELLATION_CONDITIONING"]
    )
    perturbed["hypothesis_decisions"][
        "H_A_CANCELLATION_CONDITIONING"
    ] = supported_h_a
    perturbed["supported_mechanism_ids"] = ["H_A_CANCELLATION_CONDITIONING"]
    perturbed["aggregate_mechanism_result"] = "SINGLE_SUPPORTED_MECHANISM"
    result_probe(
        "M_FREEZE_CLASSIFICATION_AFTER_NONPERTURBATION_FAILURE",
        perturbed,
        "CLASSIFICATION_PERFORMED_AFTER_EVIDENCE_BLOCK",
    )

    def gate_probe(
        control_id: str,
        field: str,
        value: Any,
        expected_evidence: str,
        expected_diagnostic: str,
    ) -> None:
        fixture = _base_classifier_fixture()
        fixture[field] = value
        observed = classifier.classify(fixture)
        passed = (
            observed["evidence_result"] == expected_evidence
            and observed["evidence_diagnostic"] == expected_diagnostic
        )
        if not passed:
            raise ValueError(
                f"freeze adversarial gate probe mismatch {control_id}: {observed}"
            )
        results.append(
            {
                "control_id": control_id,
                "expected_first_diagnostic": expected_diagnostic,
                "observed_diagnostic": observed["evidence_diagnostic"],
                "passed": True,
            }
        )

    gate_probe(
        "M_FREEZE_CONTINUUM_OPERATOR_SUBSTITUTED",
        "discrete_operator_binding_passed",
        False,
        "BLOCKED_OPERATOR_BINDING",
        "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
    )
    gate_probe(
        "M_FREEZE_OUTPUT_ROOT_COLLIDES_CANONICAL",
        "separate_output_custody_passed",
        False,
        "BLOCKED_CUSTODY",
        "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL",
    )
    gate_probe(
        "M_FREEZE_TRAJECTORY_BYTE_MISMATCH",
        "instrumentation_nonperturbation_passed",
        False,
        "BLOCKED_INSTRUMENTATION_PERTURBATION",
        "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL",
    )
    gate_probe(
        "M_FREEZE_OBSERVABLE_UNITS_OR_NORMALIZATION_MISSING",
        "observable_semantics_passed",
        False,
        "BLOCKED_OBSERVABLE_SEMANTICS",
        "OBSERVABLE_UNIT_OR_NORMALIZATION_INVALID",
    )
    unknown = _base_classifier_fixture()
    unknown["observed_run_ids"][-1] = "MECHv0:UNKNOWN"
    unknown_result = classifier.classify(unknown)
    duplicate = _base_classifier_fixture()
    duplicate["observed_run_ids"][1] = duplicate["observed_run_ids"][0]
    duplicate_result = classifier.classify(duplicate)
    if not (
        unknown_result["evidence_diagnostic"]
        == "EXPECTED_RUN_ID_CLOSURE_MISMATCH"
        and duplicate_result["evidence_diagnostic"] == "DUPLICATE_RUN_IDENTITY"
    ):
        raise ValueError("unknown/duplicate run adversarial variants did not discriminate")
    results.append(
        {
            "control_id": "M_FREEZE_UNKNOWN_OR_DUPLICATE_RUN_ID",
            "observed_diagnostic_by_variant": {
                "UNKNOWN_RUN_ID": unknown_result["evidence_diagnostic"],
                "DUPLICATE_RUN_ID": duplicate_result["evidence_diagnostic"],
            },
            "passed": True,
        }
    )
    return results


def _execute_freeze_adversarial_matrix_checks(
    matrix: dict[str, Any],
) -> list[dict[str, Any]]:
    implementation_module = importlib.import_module(
        "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
        "robustness_instrumented_r13_mechanism_experiment_implementation_v0"
    )
    omitted = copy.deepcopy(matrix["records"][:-1])
    omitted_diagnostics = implementation_module.validate_exact_run_matrix(omitted)
    expected_omitted = "RUN_MATRIX_COUNT_MISMATCH"
    if not omitted_diagnostics or omitted_diagnostics[0] != expected_omitted:
        raise ValueError(
            f"candidate-omission matrix control mismatch: {omitted_diagnostics}"
        )
    displaced = copy.deepcopy(matrix["records"])
    displaced[4]["row"] = copy.deepcopy(displaced[0]["row"])
    displaced_diagnostics = implementation_module.validate_exact_run_matrix(displaced)
    expected_displaced = (
        "RUN_MATRIX_ROW_ID_MISMATCH:MECHv0:R10_LOOSE:INSTRUMENTED"
    )
    if not displaced_diagnostics or displaced_diagnostics[0] != expected_displaced:
        raise ValueError(
            f"R10-displacement matrix control mismatch: {displaced_diagnostics}"
        )
    return [
        {
            "control_id": "M_FREEZE_CANDIDATE_RUN_OMITTED",
            "expected_first_diagnostic": expected_omitted,
            "observed_diagnostics": omitted_diagnostics,
            "passed": True,
            "simulation_invoked": False,
        },
        {
            "control_id": "M_FREEZE_R10_NEIGHBOR_DISPLACED",
            "expected_first_diagnostic": expected_displaced,
            "observed_diagnostics": displaced_diagnostics,
            "passed": True,
            "simulation_invoked": False,
        },
    ]


DECISION_IDS = [
    "accepted_design_v1_review_is_exact_live_authority",
    "accepted_design_packet_manifest_report_and_generators_are_hash_exact",
    "canonical_205_file_root_and_203_run_outputs_remain_read_only_and_exact",
    "authority_inventory_and_execution_preflight_digest_domains_are_both_exact",
    "future_output_root_is_separate_and_absent",
    "instrumented_implementation_is_hash_bound_and_imported_only_for_pure_matrix_validation",
    "classifier_is_hash_bound_and_all_constants_are_consumed_from_source",
    "exact_six_run_order_matches_implementation_and_classifier",
    "three_instrumented_roles_have_exact_noninstrumented_pairs",
    "R13_loose_is_exact_historical_1e_minus_8_parent",
    "R13_tight_is_exact_tightest_registered_passing_1e_minus_12_parent",
    "R10_is_exact_unique_accepted_neighbor_at_1e_minus_8",
    "grid_timestep_duration_step_count_and_iteration_cap_are_exact",
    "supporting_tolerance_and_duration_modules_are_disabled",
    "run_matrix_is_directly_executable_by_bound_harness",
    "twelve_JSON_NPZ_role_paths_and_two_auxiliary_paths_are_exact",
    "all_paths_are_NFC_casefold_safe_and_bijective",
    "fourteen_observable_ids_match_design_and_implementation",
    "eight_actual_packed_solver_blocks_are_complete_and_ordered",
    "block_normalization_uses_role_tolerance_and_gamma64_floor",
    "dominance_uses_additive_gamma64_and_registry_order_ties",
    "exchange_conditioning_uses_additive_gamma64_scale_floor_and_zero_branch",
    "discrete_closure_uses_actual_roll_midpoint_gauge_and_Wilson_outputs",
    "closure_roundoff_bound_uses_gamma32_exact_term_scale",
    "trajectory_nonperturbation_requires_exact_projection_byte_identity",
    "no_bounded_equivalence_fallback_is_authorized",
    "H_A_thresholds_and_directional_contrasts_are_exact",
    "H_B_longitudinal_dominance_and_comparator_contrasts_are_exact",
    "H_C_roundoff_violation_persistence_and_contrasts_are_exact",
    "H_D_is_independently_positive_distributed_accumulation_evidence",
    "H_E_requires_complete_admissible_empty_support",
    "classifier_fail_closed_precedence_and_multiple_support_are_exact",
    "positive_and_negative_classifier_controls_all_discriminate",
    "twelve_freeze_level_adversarial_controls_have_exact_first_diagnostics",
    "one_execution_no_retry_no_overwrite_contract_is_exact",
    "canonical_historical_result_and_NUMERICALLY_BLOCKED_verdict_are_unchanged",
    "materiality_remains_NOT_EVALUATED_NUMERICAL_BLOCK",
    "no_mechanism_result_robustness_reclassification_or_E_REPRO_is_assigned",
    "packet_rotates_only_to_independent_numerical_freeze_review",
]


def _metric_configuration_template() -> dict[str, Any]:
    h_a = classifier.SUPPORT_CONSTANTS["H_A"]
    h_d = classifier.SUPPORT_CONSTANTS["H_D"]
    return {
        "block_scale_rule": "for each role and block: requested solver tolerance",
        "block_floor_rule": "for every block: gamma_64",
        "block_scales_materialized_by_execution_harness": True,
        "block_floors_materialized_by_execution_harness": True,
        "epsilon_dominance": GAMMA64,
        "severe_kappa_threshold": h_a["loose_median_kappa_minimum"],
        "distributed_per_block_share_minimum": h_d["per_block_share_minimum"],
        "distributed_minimum_contributing_block_count": h_d[
            "minimum_contributing_block_count_per_step"
        ],
        "distributed_effective_block_count_minimum": h_d[
            "effective_block_count_minimum"
        ],
        "distributed_single_block_share_maximum_exclusive": h_d[
            "single_block_share_maximum_exclusive"
        ],
        "distributed_effective_count_formula": (
            "(sum_b D_b)^2 / sum_b(D_b^2), with zero when the square sum is zero"
        ),
        "linked_structural_series": [
            "GAUSS",
            "CONTINUITY",
            "LONGITUDINAL_EXCHANGE",
            "LONGITUDINAL_MAXWELL",
        ],
        "postinitial_sample_count": 16,
        "no_posthoc_window_lag_exponent_or_point_selection": True,
    }


def _classifier_contract() -> dict[str, Any]:
    classifier_hash = sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH)
    if classifier_hash != EXPECTED_CLASSIFIER_SHA256:
        raise ValueError("mechanism classifier source hash mismatch")
    return {
        "classifier_id": classifier.CLASSIFIER_ID,
        "classifier_implementation": {
            "path": CLASSIFIER_RELATIVE_PATH,
            "sha256": classifier_hash,
        },
        "expected_run_ids": list(classifier.EXPECTED_RUN_IDS),
        "role_keys": list(classifier.ROLE_KEYS),
        "hypotheses_A_to_D": list(classifier.HYPOTHESES_A_TO_D),
        "hypothesis_E": classifier.H_E,
        "support_constants_bound_directly_from_classifier_source": copy.deepcopy(
            classifier.SUPPORT_CONSTANTS
        ),
        "required_gate_fields": list(classifier.REQUIRED_GATE_FIELDS),
        "required_metric_fields": list(classifier.REQUIRED_METRIC_FIELDS),
        "evidence_outcomes": list(classifier.EVIDENCE_OUTCOMES),
        "aggregate_outcomes": list(classifier.AGGREGATE_OUTCOMES),
        "fail_closed_precedence": list(classifier.CLASSIFIER_PRECEDENCE),
        "fail_closed_precedence_count": len(classifier.CLASSIFIER_PRECEDENCE),
        "fail_closed_precedence_bound_directly_from_classifier_source": True,
        "blocked_semantics": {
            "aggregate_mechanism_result": "BLOCKED",
            "supported_mechanism_ids": [],
            "all_hypothesis_statuses": "NOT_EVALUATED",
            "H_E_supported": False,
        },
        "multiple_mechanisms_may_be_supported": True,
        "unresolved_complete_evidence_is_admitted": True,
        "claim_ceiling": classifier.CLAIM_CEILING,
    }


def _freeze_obligation_closure(
    matrix: dict[str, Any],
    implementation: dict[str, Any],
    observables: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    closures = [
        ("exact experiment and run count", "six records in exact classifier/harness order"),
        ("exact tight R13 tolerance choice and any additional tolerances", "1e-12 tightest registered passing role; no additional tolerances"),
        ("exact matched-neighbor row identity after deterministic rule confirmation", "R10_MU_HIGH under accepted unique ranking tuple"),
        ("exact duration and checkpoint schedule", "duration 0.05; 16 accepted steps; 17 state checkpoints"),
        ("exact instrumentation pairing multiplicity", "three one-to-one instrumented/noninstrumented pairs"),
        (
            "exact grid, timestep, iteration cap, and environment identity",
            "N=16; dt=0.003125; cap=80; committed configuration blobs registered",
        ),
        ("exact equation-block registry tied to implementation", f"{len(BLOCK_IDS)} ordered literal implementation blocks"),
        ("exact output field names, shapes, schema version, and filenames", f"{len(observables)} observables; schema {implementation['output_schema_version']}; 12 role files plus 2 auxiliary files"),
        ("exact units, normalizations, numerical floors, and aggregation formulas", "observable and block registries freeze every semantic field"),
        ("exact discrete closure formula, operator hashes, and truncation remainder", "actual scheme Q with gamma32 floating-evaluation bound; no continuum substitute"),
        ("exact nonperturbation equality or fallback equivalence rule", "exact physical-trajectory projection byte equality; no fallback"),
        ("exact hypothesis thresholds, contrast rules, association metrics, and tie behavior", "classifier hash and source constants frozen; no posthoc association route"),
        ("exact positive and negative controls", "six positive aggregate controls, classifier mutation controls, and twelve freeze-level adversarial controls"),
        ("exact classifier implementation and hash", EXPECTED_CLASSIFIER_SHA256),
        ("exact implementation closure and code hash", implementation["sha256"]),
        ("exact one-execution authorization and no-retry rule", "one future exact-matrix call only after ACCEPT_FREEZE; exclusive root and start marker"),
    ]
    if len(closures) != 16 or matrix["record_count"] != 6:
        raise ValueError("sixteen freeze-deferred obligations were not exactly closed")
    return [
        {
            "obligation_index": index,
            "design_v1_deferred_item": item,
            "freeze_v0_closure": closure,
            "status": "CLOSED_PENDING_INDEPENDENT_FREEZE_REVIEW",
        }
        for index, (item, closure) in enumerate(closures, start=1)
    ]


def build_packet(
    custody: dict[str, Any] | None = None,
    implementation: dict[str, Any] | None = None,
    matrix: dict[str, Any] | None = None,
    identity: dict[str, Any] | None = None,
) -> dict[str, Any]:
    supplied = [custody, implementation, matrix, identity]
    if all(item is None for item in supplied):
        custody = _source_custody()
        implementation = _implementation_binding()
        matrix = build_run_matrix(implementation)
        identity = build_output_identity(matrix)
    elif any(item is None for item in supplied):
        raise ValueError("build_packet requires either all bound inputs or none")
    assert custody is not None
    assert implementation is not None
    assert matrix is not None
    assert identity is not None
    observables = _observable_registry(str(implementation["output_schema_version"]))
    blocks = _block_registry()
    classifier_contract = _classifier_contract()
    controls = _classifier_control_suite()
    freeze_adversarial_controls = _freeze_adversarial_control_registry()
    freeze_adversarial_classifier_checks = (
        _execute_freeze_adversarial_classifier_checks(controls)
    )
    freeze_adversarial_matrix_checks = _execute_freeze_adversarial_matrix_checks(
        matrix
    )
    matrix_raw = canonical_json_bytes(matrix)
    identity_raw = canonical_json_bytes(identity)
    decisions = [{"decision_id": decision_id, "passed": True} for decision_id in DECISION_IDS]
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "authority_basis": custody,
        "accepted_design_binding": {
            "design_packet": {
                "path": DESIGN_PACKET_RELATIVE_PATH,
                "sha256": EXPECTED_SOURCE_HASHES[DESIGN_PACKET_RELATIVE_PATH],
            },
            "design_manifest": {
                "path": DESIGN_MANIFEST_RELATIVE_PATH,
                "sha256": EXPECTED_SOURCE_HASHES[DESIGN_MANIFEST_RELATIVE_PATH],
            },
            "design_release_report": {
                "path": DESIGN_REPORT_RELATIVE_PATH,
                "sha256": EXPECTED_SOURCE_HASHES[DESIGN_REPORT_RELATIVE_PATH],
            },
            "independent_design_review": {
                "path": DESIGN_REVIEW_RELATIVE_PATH,
                "sha256": EXPECTED_SOURCE_HASHES[DESIGN_REVIEW_RELATIVE_PATH],
                "verdict": "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN",
            },
            "route_A_preserved": True,
            "scientific_questions_changed": False,
        },
        "exact_run_matrix": {
            "path": RUN_MATRIX_RELATIVE_PATH,
            "sha256": sha256_bytes(matrix_raw),
            "record_count": 6,
            "instrumented_count": 3,
            "paired_noninstrumented_count": 3,
        },
        "expected_output_identity_manifest": {
            "path": IDENTITY_RELATIVE_PATH,
            "sha256": sha256_bytes(identity_raw),
            "run_count": 6,
            "role_payload_file_count": 12,
            "auxiliary_file_count": 2,
        },
        "implementation_closure": implementation,
        "equation_block_registry": blocks,
        "equation_block_count": len(blocks),
        "mechanism_observable_registry": observables,
        "mechanism_observable_count": len(observables),
        "metric_configuration_template": _metric_configuration_template(),
        "discrete_Maxwell_continuity_closure_freeze": {
            "continuum_formula_is_not_the_audit_definition": True,
            "implementation_literal_contract": copy.deepcopy(
                implementation["literal_discrete_closure_contract"]
            ),
            "step_integrated_closure_formula": (
                "Q=(G1-G0)-(roll(Rp,1)-Rp)-a*dt*C"
            ),
            "gauss_formula": "G=roll(p,1)-p+a*rho",
            "p_equation_defect_formula": "Rp=p1-p0+dt*grad_theta_mid",
            "continuity_formula": (
                "C=(rho1-rho0)/dt+(grad_theta_mid-roll(grad_theta_mid,1))/a"
            ),
            "periodic_shift": "numpy.roll(field, 1) on lattice axis",
            "time_centering": "arithmetic implicit midpoint",
            "operator_outputs_required": list(
                next(
                    item["required_components"]
                    for item in observables
                    if item["observable_id"] == "DISCRETE_OPERATOR_OUTPUTS"
                )
            ),
            "gauge_link_Wilson_and_boundary_outputs_required": True,
            "gamma_operation_count": 32,
            "gamma_32": GAMMA32,
            "expected_remainder_class": "FLOAT64_EVALUATION_ROUNDOFF_ONLY",
            "posthoc_continuum_substitution_allowed": False,
            "operator_implementation_sha256": implementation["sha256"],
            "binding_failure": "BLOCKED_OPERATOR_BINDING",
        },
        "instrumentation_nonperturbation_freeze": {
            "pair_count": 3,
            "projection_domain": "R13-MECHANISM-PHYSICAL-TRAJECTORY-v0",
            "projection": (
                "all 17 packed float64 physical-state snapshots in time order; no instrumentation-only field"
            ),
            "required_rule": (
                "shape, dtype, C-order bytes, and domain-separated SHA-256 must be exactly identical within each pair"
            ),
            "equivalence_ceiling": 0.0,
            "bounded_equivalence_fallback_authorized": False,
            "any_pair_failure": "BLOCKED_INSTRUMENTATION_PERTURBATION",
            "instrumentation_may_modify_state_solver_order_stopping_or_parameters": False,
        },
        "classifier_freeze": classifier_contract,
        "classifier_control_suite": controls,
        "freeze_adversarial_control_registry": freeze_adversarial_controls,
        "freeze_adversarial_control_count": len(freeze_adversarial_controls),
        "freeze_adversarial_classifier_check_results": (
            freeze_adversarial_classifier_checks
        ),
        "freeze_adversarial_classifier_check_count": len(
            freeze_adversarial_classifier_checks
        ),
        "freeze_adversarial_matrix_check_results": freeze_adversarial_matrix_checks,
        "freeze_adversarial_matrix_check_count": len(
            freeze_adversarial_matrix_checks
        ),
        "freeze_adversarial_executed_check_count": (
            len(freeze_adversarial_classifier_checks)
            + len(freeze_adversarial_matrix_checks)
        ),
        "freeze_adversarial_matrix_validator_import": {
            "implementation_module_imported": True,
            "callable_used": "validate_exact_run_matrix",
            "evolution_or_execution_runner_invocation_count": 0,
        },
        "output_custody_and_execution_freeze": {
            "canonical_output_root": CANONICAL_OUTPUT_ROOT,
            "canonical_authority_inventory_digest": EXPECTED_CANONICAL_ROOT_DIGEST,
            "canonical_authority_inventory_digest_domain": (
                "AUTHORITY_CHAIN_CANONICAL_JSON_INVENTORY"
            ),
            "canonical_execution_preflight_digest": (
                EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256
            ),
            "canonical_execution_preflight_digest_domain": (
                "R13-MECHANISM-DIRECTORY-TREE-v0"
            ),
            "new_output_root": EXPERIMENT_OUTPUT_ROOT,
            "new_output_root_parent_must_preexist": "formal/output",
            "new_output_root_must_not_exist_before_execution": True,
            "freeze_preparation_created_output_root": False,
            "execution_entrypoint": (
                f"{IMPLEMENTATION_RELATIVE_PATH}:execute_exact_matrix_once"
            ),
            "implementation_module_imported_for_matrix_validator_only": True,
            "execution_entrypoint_invocation_count": 0,
            "start_marker": f"{EXPERIMENT_OUTPUT_ROOT}/EXECUTION-STARTED.json",
            "final_matrix_result": f"{EXPERIMENT_OUTPUT_ROOT}/MATRIX-RESULT.json",
            "one_call_per_run": True,
            "retry_branch": "FORBIDDEN",
            "overwrite": "FORBIDDEN",
            "dynamic_run_discovery": "FORBIDDEN",
            "partial_failure_behavior": (
                "preserve output root and partial evidence; subsequent execution refuses because root exists"
            ),
            "execution_authorized_now": False,
            "matrix_result_status_precedence": [
                "BLOCKED_CANONICAL_OUTPUT_MUTATION when canonical digest changes",
                "BLOCKED_INSTRUMENTATION_PERTURBATION when any paired trajectory differs",
                "EXECUTION_COMPLETED_ONCE only when canonical custody and all three exact pairs pass",
            ],
            "mechanism_classification_allowed_rule": (
                "true only when canonical digest is unchanged and every paired physical trajectory is byte-identical"
            ),
            "pair_mismatch_completion_label_allowed": False,
        },
        "freeze_deferred_obligation_closure": _freeze_obligation_closure(
            matrix, implementation, observables
        ),
        "freeze_deferred_obligation_count": 16,
        "decision_count": len(decisions),
        "passed_decision_count": len(decisions),
        "failed_decision_ids": [],
        "decisions": decisions,
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "blocked_target": BLOCKED_TARGET,
        "authority_boundary": {
            "numerical_freeze_packet_prepared": True,
            "exact_six_run_matrix_specified": True,
            "numerical_freeze_independently_accepted": False,
            "new_simulation_authorized": False,
            "new_experiment_execution_authorized": False,
            "new_experiment_execution_performed": False,
            "canonical_execution_count": 1,
            "canonical_robustness": "NUMERICALLY_BLOCKED",
            "blocked_row": "R13_CORNER_STRONG_LOW",
            "root_mechanism": "UNRESOLVED",
            "materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "materiality_classification_authorized": False,
            "robustness_reclassification_authorized": False,
            "threshold_change_authorized": False,
            "new_E_REPRO_claim": False,
            "new_E_REPRO_authorized": False,
            "previous_canonical_Maxwell_Dirac_E_REPRO_unchanged": True,
        },
        "claim_ceiling": (
            "Exact numerical freeze prepared for independent review only. Only an independent "
            "ACCEPT_FREEZE verdict may authorize one exact six-record execution. No mechanism result, "
            "robustness reclassification, materiality, physical claim, E-REPRO, pillar, seam, C_k, "
            "CCFT, or master-action promotion is assigned in advance."
        ),
        "nonclaims": [
            "no new output root or simulation was created",
            "no canonical output was changed or rerun",
            "no R13 root mechanism was identified",
            "no threshold was relaxed or canonical loose role removed",
            "no robustness or conditional-robustness class was assigned",
            "no materiality evaluation was performed",
            "no new E-REPRO or broader ToE claim was earned",
            "no repository-wide green claim",
        ],
        "environment_identity": _environment_identity(),
    }


def build_manifest(
    packet: dict[str, Any],
    matrix: dict[str, Any],
    identity: dict[str, Any],
    implementation: dict[str, Any],
) -> dict[str, Any]:
    packet_raw = canonical_json_bytes(packet)
    matrix_raw = canonical_json_bytes(matrix)
    identity_raw = canonical_json_bytes(identity)
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_MANIFEST_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {
            "path": SCRIPT_RELATIVE_PATH,
            "sha256": sha256_path(SCRIPT_PATH),
        },
        "classifier": {
            "path": CLASSIFIER_RELATIVE_PATH,
            "sha256": EXPECTED_CLASSIFIER_SHA256,
        },
        "instrumented_implementation": {
            "path": IMPLEMENTATION_RELATIVE_PATH,
            "sha256": implementation["sha256"],
            "implementation_imported_only_for_pure_schema_and_matrix_validation": True,
            "evolution_or_execution_runner_invocation_count": 0,
        },
        "bound_historical_implementations": implementation[
            "literal_bound_historical_sources"
        ],
        "accepted_design_and_canonical_inputs": [
            {"path": path, "sha256": digest}
            for path, digest in EXPECTED_SOURCE_HASHES.items()
        ],
        "packet": {
            "path": PACKET_RELATIVE_PATH,
            "sha256": sha256_bytes(packet_raw),
        },
        "run_matrix": {
            "path": RUN_MATRIX_RELATIVE_PATH,
            "sha256": sha256_bytes(matrix_raw),
            "record_count": 6,
        },
        "expected_output_identity_manifest": {
            "path": IDENTITY_RELATIVE_PATH,
            "sha256": sha256_bytes(identity_raw),
            "role_payload_file_count": 12,
        },
        "future_experiment_output_root": EXPERIMENT_OUTPUT_ROOT,
        "future_experiment_output_root_absent": True,
        "canonical_authority_inventory_digest": EXPECTED_CANONICAL_ROOT_DIGEST,
        "canonical_execution_preflight_digest": (
            EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256
        ),
        "decision_count": len(DECISION_IDS),
        "selected_next_target": REVIEW_TARGET,
        "execution_authorized": False,
    }


def build_report(
    packet: dict[str, Any],
    matrix: dict[str, Any],
    identity: dict[str, Any],
    manifest: dict[str, Any],
    implementation: dict[str, Any],
) -> dict[str, Any]:
    packet_raw = canonical_json_bytes(packet)
    matrix_raw = canonical_json_bytes(matrix)
    identity_raw = canonical_json_bytes(identity)
    manifest_raw = canonical_json_bytes(manifest)
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_20260715_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "artifacts": {
            "packet": {
                "path": PACKET_RELATIVE_PATH,
                "sha256": sha256_bytes(packet_raw),
            },
            "run_matrix": {
                "path": RUN_MATRIX_RELATIVE_PATH,
                "sha256": sha256_bytes(matrix_raw),
            },
            "expected_output_identity": {
                "path": IDENTITY_RELATIVE_PATH,
                "sha256": sha256_bytes(identity_raw),
            },
            "manifest": {
                "path": MANIFEST_RELATIVE_PATH,
                "sha256": sha256_bytes(manifest_raw),
            },
            "classifier": {
                "path": CLASSIFIER_RELATIVE_PATH,
                "sha256": EXPECTED_CLASSIFIER_SHA256,
            },
            "instrumented_implementation": {
                "path": IMPLEMENTATION_RELATIVE_PATH,
                "sha256": implementation["sha256"],
            },
        },
        "exact_freeze_summary": {
            "run_count": matrix["record_count"],
            "instrumented_run_count": matrix["instrumented_record_count"],
            "noninstrumented_control_count": matrix[
                "noninstrumented_control_record_count"
            ],
            "physical_configuration_count": matrix["physical_configuration_count"],
            "observable_count": packet["mechanism_observable_count"],
            "equation_block_count": packet["equation_block_count"],
            "freeze_obligation_count": packet[
                "freeze_deferred_obligation_count"
            ],
            "classifier_positive_control_count": packet[
                "classifier_control_suite"
            ]["positive_control_count"],
            "classifier_negative_control_count": packet[
                "classifier_control_suite"
            ]["negative_control_count"],
            "freeze_adversarial_control_count": packet[
                "freeze_adversarial_control_count"
            ],
            "role_payload_file_count": identity["role_payload_file_count"],
            "successful_execution_total_file_count": identity[
                "complete_expected_file_count_after_success"
            ],
        },
        "decision_ids": list(DECISION_IDS),
        "decision_count": packet["decision_count"],
        "passed_decision_count": packet["passed_decision_count"],
        "failed_decision_ids": packet["failed_decision_ids"],
        "preparation_validation_status": {
            "accepted_input_hashes_exact": True,
            "canonical_authority_inventory_digest_exact": True,
            "canonical_execution_preflight_digest_exact": True,
            "implementation_literal_registry_parse_passed": True,
            "implementation_classifier_run_identity_closure_passed": True,
            "classifier_controls_passed": True,
            "freeze_adversarial_control_count": packet[
                "freeze_adversarial_control_count"
            ],
            "freeze_adversarial_executed_check_count": packet[
                "freeze_adversarial_executed_check_count"
            ],
            "pure_matrix_validator_imported": True,
            "evolution_or_execution_runner_invocation_count": 0,
            "run_matrix_pairing_and_executable_schema_passed": True,
            "JSON_NPZ_path_bijection_passed": True,
            "artifact_regeneration_mode_available": True,
            "simulation_invocation_count": 0,
            "new_output_root_created": False,
            "canonical_output_mutation_count": 0,
            "focused_tests": "NOT_RECORDED_BY_GENERATOR",
            "affected_Lean_build": "NOT_RECORDED_BY_GENERATOR",
            "historical_repository_wide_Lean": {
                "status": "INCOMPLETE_TIMEOUT",
                "completed_jobs": 8441,
                "total_jobs": 8507,
                "repository_wide_green_claim": False,
            },
        },
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "authority_boundary": packet["authority_boundary"],
        "claim_ceiling": packet["claim_ceiling"],
        "nonclaims": packet["nonclaims"],
    }


def build_artifacts() -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    custody = _source_custody()
    implementation = _implementation_binding()
    matrix = build_run_matrix(implementation)
    identity = build_output_identity(matrix)
    packet = build_packet(custody, implementation, matrix, identity)
    manifest = build_manifest(packet, matrix, identity, implementation)
    report = build_report(packet, matrix, identity, manifest, implementation)
    return packet, matrix, identity, manifest, report


def artifact_bytes() -> dict[str, bytes]:
    packet, matrix, identity, manifest, report = build_artifacts()
    return {
        PACKET_RELATIVE_PATH: canonical_json_bytes(packet),
        RUN_MATRIX_RELATIVE_PATH: canonical_json_bytes(matrix),
        IDENTITY_RELATIVE_PATH: canonical_json_bytes(identity),
        MANIFEST_RELATIVE_PATH: canonical_json_bytes(manifest),
        REPORT_RELATIVE_PATH: canonical_json_bytes(report),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the exact instrumented R13 mechanism experiment numerical-freeze packet v0."
        )
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    canonical_before = canonical_root_digest()
    canonical_tree_before = canonical_directory_tree_sha256()
    experiment_root = REPO_ROOT / EXPERIMENT_OUTPUT_ROOT
    if experiment_root.exists():
        print("ERROR: future mechanism output root already exists", file=sys.stderr)
        return 1
    try:
        artifacts = artifact_bytes()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    if args.write:
        for relative_path, raw in artifacts.items():
            path = REPO_ROOT / relative_path
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    elif args.check:
        stale = [
            relative_path
            for relative_path, raw in artifacts.items()
            if not (REPO_ROOT / relative_path).is_file()
            or (REPO_ROOT / relative_path).read_bytes() != raw
        ]
        if stale:
            print(f"stale or missing numerical-freeze artifacts: {stale}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(artifacts[REPORT_RELATIVE_PATH])
    canonical_after = canonical_root_digest()
    canonical_tree_after = canonical_directory_tree_sha256()
    if (
        canonical_before != canonical_after
        or canonical_tree_before != canonical_tree_after
        or canonical_after != EXPECTED_CANONICAL_ROOT_DIGEST
        or canonical_tree_after != EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256
    ):
        print("ERROR: canonical output root changed during freeze preparation", file=sys.stderr)
        return 1
    if experiment_root.exists():
        print("ERROR: freeze preparation created future experiment output root", file=sys.stderr)
        return 1
    if args.write:
        print(
            f"wrote instrumented R13 numerical freeze v0: {len(artifacts)} artifacts; "
            f"{len(DECISION_IDS)}/{len(DECISION_IDS)} decisions; execution unauthorized"
        )
    elif args.check:
        print(
            f"instrumented R13 numerical freeze v0 verified: {len(artifacts)} artifacts; "
            "canonical outputs unchanged and experiment root absent"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
