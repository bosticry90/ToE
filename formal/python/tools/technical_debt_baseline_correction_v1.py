from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import types
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "887d1b2f3a4faa249430078280cc65914651e7bb"
V0_COMMIT = "f8c648602d18360d45c76368bfb3e3ef830f2842"
V0_REL = "formal/docs/release/TECHNICAL_DEBT_BASELINE_20260711_v0.json"
V0_TOOL_REL = "formal/python/tools/technical_debt_baseline.py"
V0_INTEGRITY_TOOL_REL = "formal/python/tools/loop_control_registry_integrity.py"
OUTPUT_PATH = REPO_ROOT / "formal/docs/release/TECHNICAL_DEBT_BASELINE_20260711_v1.json"
REVIEW_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)
EXPECTED_V0_SHA256 = "7e9dd29378d70ae51de4a456ecf9745c59a8e40da36df50fa7515baa24f53ac6"
EXPECTED_REVIEW_SHA256 = "5e43181b11a4d302a301bd915a43a40636bf947d93edc9f327e9c0a7beceb485"

CORRECTED_AXIOM_RE = re.compile(
    r"^[ \t]*axiom[ \t]+([A-Za-z_][A-Za-z0-9_'.]*)\b", re.MULTILINE
)
CORRECTED_OPAQUE_RE = re.compile(
    r"^[ \t]*opaque[ \t]+([A-Za-z_][A-Za-z0-9_'.]*)\b", re.MULTILINE
)
CORRECTED_DECLARATION_START_RE = re.compile(
    r"^[ \t]*(?:axiom|theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance)[ \t]+",
    re.MULTILINE,
)


class BaselineCorrectionError(ValueError):
    pass


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git_blob(commit: str, relative_path: str) -> bytes:
    completed = subprocess.run(
        ["git", "show", f"{commit}:{relative_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise BaselineCorrectionError(
            f"cannot read source blob {commit}:{relative_path}: "
            + completed.stderr.decode("utf-8", errors="replace")
        )
    return completed.stdout


def _load_reviewed_legacy_module() -> types.ModuleType:
    dependency_name = "formal.python.tools.loop_control_registry_integrity"
    dependency = types.ModuleType(dependency_name)
    dependency.__file__ = str(REPO_ROOT / V0_INTEGRITY_TOOL_REL)
    exec(
        compile(
            _git_blob(V0_COMMIT, V0_INTEGRITY_TOOL_REL),
            dependency.__file__,
            "exec",
        ),
        dependency.__dict__,
    )

    module = types.ModuleType("reviewed_technical_debt_baseline_f8c64860")
    module.__file__ = str(REPO_ROOT / V0_TOOL_REL)
    prior_dependency = sys.modules.get(dependency_name)
    try:
        sys.modules[dependency_name] = dependency
        exec(
            compile(_git_blob(V0_COMMIT, V0_TOOL_REL), module.__file__, "exec"),
            module.__dict__,
        )
    finally:
        if prior_dependency is None:
            del sys.modules[dependency_name]
        else:
            sys.modules[dependency_name] = prior_dependency
    return module


legacy = _load_reviewed_legacy_module()


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise BaselineCorrectionError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _json_bytes(data: bytes) -> dict[str, Any]:
    value = json.loads(data.decode("utf-8"), object_pairs_hook=_strict_object)
    if not isinstance(value, dict):
        raise BaselineCorrectionError("expected JSON object")
    return value


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _repo_rel(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def _source_paths() -> dict[str, Path]:
    return {
        "axiom_ledger": legacy.AXIOM_LEDGER_PATH,
        "local_preservation_custody": legacy.CUSTODY_PATH,
        "registry": legacy.REGISTRY_PATH,
        "retirements_source_ledger": legacy.RETIREMENTS_PATH,
        "snapshot_inventory": legacy.SNAPSHOT_INDEX_PATH,
    }


def _assert_working_sources_semantically_match_review_boundary() -> None:
    for role, path in _source_paths().items():
        relative = _repo_rel(path)
        reviewed = _git_blob(SOURCE_COMMIT, relative)
        working = path.read_bytes()
        if working == reviewed:
            continue
        if path.suffix == ".json":
            if _json_bytes(working) != _json_bytes(reviewed):
                raise BaselineCorrectionError(
                    f"working JSON source differs semantically from review boundary: {role}"
                )
        elif working.replace(b"\r\n", b"\n") != reviewed.replace(b"\r\n", b"\n"):
            raise BaselineCorrectionError(
                f"working text source differs from review boundary: {role}"
            )


def _corrected_legacy_payload() -> dict[str, Any]:
    prior = (legacy.AXIOM_RE, legacy.OPAQUE_RE, legacy.DECLARATION_START_RE)
    try:
        legacy.AXIOM_RE = CORRECTED_AXIOM_RE
        legacy.OPAQUE_RE = CORRECTED_OPAQUE_RE
        legacy.DECLARATION_START_RE = CORRECTED_DECLARATION_START_RE
        return legacy.build_baseline()
    finally:
        legacy.AXIOM_RE, legacy.OPAQUE_RE, legacy.DECLARATION_START_RE = prior


def build_baseline() -> dict[str, Any]:
    _assert_working_sources_semantically_match_review_boundary()
    v0_raw = _git_blob(V0_COMMIT, V0_REL)
    if _sha256_bytes(v0_raw) != EXPECTED_V0_SHA256:
        raise BaselineCorrectionError("reviewed v0 baseline blob drift")
    if _sha256_bytes(_git_blob(SOURCE_COMMIT, REVIEW_REL)) != EXPECTED_REVIEW_SHA256:
        raise BaselineCorrectionError("independent review blob drift")

    payload = _corrected_legacy_payload()
    debt = payload["technical_debt_baselines"]
    v0 = _json_bytes(v0_raw)
    v0_debt = v0["technical_debt_baselines"]
    empty_sha = _sha256_bytes(b"")

    source_bindings = {
        role: {
            "path": _repo_rel(path),
            "reviewed_blob_sha256": _sha256_bytes(
                _git_blob(SOURCE_COMMIT, _repo_rel(path))
            ),
            "reviewed_commit": SOURCE_COMMIT,
        }
        for role, path in sorted(_source_paths().items())
    }
    debt["lean_axioms"]["ledger_sha256"] = source_bindings["axiom_ledger"][
        "reviewed_blob_sha256"
    ]
    debt["loop_control_registry"]["sha256"] = source_bindings["registry"][
        "reviewed_blob_sha256"
    ]
    debt["quarantined_assertions"]["source_ledger_sha256"] = source_bindings[
        "retirements_source_ledger"
    ]["reviewed_blob_sha256"]
    debt["tooling_snapshots"]["inventory_sha256"] = source_bindings[
        "snapshot_inventory"
    ]["reviewed_blob_sha256"]
    payload["verification_contract"][
        "local_preservation_custody_sha256"
    ] = source_bindings["local_preservation_custody"]["reviewed_blob_sha256"]

    if debt["lean_axioms"]["stable_identity_set_sha256"] != v0_debt[
        "lean_axioms"
    ]["stable_identity_set_sha256"]:
        raise BaselineCorrectionError("axiom identity set changed during evidence correction")
    if debt["lean_opaque_definitions"]["stable_identity_set_sha256"] != v0_debt[
        "lean_opaque_definitions"
    ]["stable_identity_set_sha256"]:
        raise BaselineCorrectionError("opaque identity set changed during evidence correction")

    payload["correction_contract"] = {
        "corrected_review_findings": ["REGISTRY-REVIEW-009", "REGISTRY-REVIEW-011"],
        "independent_review_path": REVIEW_REL,
        "independent_review_sha256": EXPECTED_REVIEW_SHA256,
        "generator_bindings": {
            "reviewed_integrity_dependency_sha256": _sha256_bytes(
                _git_blob(V0_COMMIT, V0_INTEGRITY_TOOL_REL)
            ),
            "reviewed_v0_generator_sha256": _sha256_bytes(
                _git_blob(V0_COMMIT, V0_TOOL_REL)
            ),
            "reviewed_v0_generator_commit": V0_COMMIT,
        },
        "retained_scientific_target": legacy.SCIENTIFIC_TARGET,
        "retained_maintenance_target": legacy.MAINTENANCE_TARGET,
        "source_bindings": source_bindings,
        "statement_line_hash_corrections": {
            "axiom_rows_previously_empty": sum(
                row["statement_line_sha256"] == empty_sha
                for row in v0_debt["lean_axioms"]["axioms"]
            ),
            "axiom_rows_empty_after_correction": sum(
                row["statement_line_sha256"] == empty_sha
                for row in debt["lean_axioms"]["axioms"]
            ),
            "opaque_rows_previously_empty": sum(
                row["statement_line_sha256"] == empty_sha
                for row in v0_debt["lean_opaque_definitions"]["candidates"]
            ),
            "opaque_rows_empty_after_correction": sum(
                row["statement_line_sha256"] == empty_sha
                for row in debt["lean_opaque_definitions"]["candidates"]
            ),
        },
        "superseded_v0_path": V0_REL,
        "superseded_v0_sha256": EXPECTED_V0_SHA256,
    }
    payload["schema_id"] = "TECHNICAL_DEBT_BASELINE_20260711_v1"
    payload["source_commit"] = SOURCE_COMMIT
    payload["status"] = (
        "VERSIONED_EVIDENCE_CORRECTION_COUNTS_AND_AUTHORITY_UNCHANGED_"
        "NO_REMEDIATION_OR_MIGRATION_EXECUTION"
    )
    payload["verification_contract"]["clean_checkout_reproducible_source_binding"] = True
    payload["verification_contract"]["source_binding_mode"] = (
        "immutable_git_blob_at_review_commit"
    )
    return payload


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_name, path)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or verify the v1 debt-baseline correction.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = canonical_json_bytes(build_baseline())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != data:
            raise BaselineCorrectionError("v1 technical-debt baseline correction mismatch")
        print(f"technical_debt_baseline_v1: OK sha256={_sha256_bytes(data)}")
        return 0
    _atomic_write(OUTPUT_PATH, data)
    print(f"technical_debt_baseline_v1: wrote {OUTPUT_PATH} sha256={_sha256_bytes(data)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
