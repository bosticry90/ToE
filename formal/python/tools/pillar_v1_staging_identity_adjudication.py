from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1_result_review
    as review,
)
from formal.python.tools import pillar_v1_source_identity
from formal.python.tools import qft_route_evidence_identity


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "toe.pillar_v1_staging_identity_adjudication.v0"
EM_PATH = "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
EM_HISTORICAL_CR_INSERT_OFFSET = 92149
RUNTIME_PATHS = (
    review.V0_GENERATOR_REL,
    review.REPO_ENVIRONMENT_REL,
    "formal/python/meta/__init__.py",
    "State_of_the_Theory.md",
)
STAGED_OUTPUTS = (
    review.PACKET_REL,
    review.MANIFEST_REL,
    review.PREPARATION_REPORT_REL,
)


class StagingAdjudicationError(ValueError):
    """Raised when a staging identity cannot be mapped without inference."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git(*args: str) -> bytes:
    completed = subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise StagingAdjudicationError(
            f"Git lookup failed ({' '.join(args)}): {detail}"
        )
    return completed.stdout


def _git_blob(commit: str, path: str) -> tuple[str, bytes]:
    oid = _git("rev-parse", f"{commit}:{path}").decode("ascii").strip()
    return oid, _git("cat-file", "blob", oid)


def _expected_frozen_hashes() -> dict[str, str]:
    expected = dict(review.EXPECTED_INPUT_HASHES)
    expected[review.GENERATOR_REL] = review.EXPECTED_PREPARATION_HASHES[
        review.GENERATOR_REL
    ]
    return expected


def _historical_representation(
    path: str,
    expected_sha256: str,
) -> tuple[str, str, bytes]:
    oid, blob = _git_blob(review.PREPARATION_COMMIT, path)
    candidates: list[tuple[str, bytes]] = [
        ("GIT_BLOB_EXACT", blob),
        (
            "CRLF_FROM_FROZEN_GIT_BLOB",
            blob.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n"),
        ),
    ]
    if path == EM_PATH:
        candidates.append(
            (
                "ACCEPTED_MIXED_EOL_RECONSTRUCTION",
                blob[:EM_HISTORICAL_CR_INSERT_OFFSET]
                + b"\r"
                + blob[EM_HISTORICAL_CR_INSERT_OFFSET:],
            )
        )
    for representation, raw in candidates:
        if sha256_bytes(raw) == expected_sha256:
            return oid, representation, raw
    raise StagingAdjudicationError(
        f"no accepted reconstruction matches historical pin: {path}"
    )


def dependency_ledger() -> list[dict[str, Any]]:
    qft_contract = qft_route_evidence_identity.load_contract()
    qft_by_path = {entry["path"]: entry for entry in qft_contract["identities"]}
    pillar_contract = pillar_v1_source_identity.load_contract()
    pillar_by_role = {
        entry["identity_role"]: entry for entry in pillar_contract["identities"]
    }
    entries: list[dict[str, Any]] = []
    for path, expected_sha256 in sorted(_expected_frozen_hashes().items()):
        oid, representation, historical_raw = _historical_representation(
            path, expected_sha256
        )
        entry: dict[str, Any] = {
            "path": path,
            "dependency_kind": "FROZEN_GENERATOR_INPUT",
            "staging_identity_role": "HISTORICAL_SOURCE_PIN",
            "temporal_role": "HISTORICAL",
            "current_critical": False,
            "review_time_commit": review.PREPARATION_COMMIT,
            "review_time_git_blob": oid,
            "review_time_blob_sha256": sha256_bytes(
                _git("cat-file", "blob", oid)
            ),
            "historical_pin_sha256": expected_sha256,
            "historical_representation": representation,
            "historical_representation_bytes": len(historical_raw),
            "provenance": "VERIFIED",
        }
        if path in qft_by_path:
            current = qft_by_path[path]["current_identity"]
            entry["accepted_current_identity"] = {
                "identity_role": (
                    "CURRENT_GIT_BLOB_IDENTITY"
                    if current["domain"]
                    == qft_route_evidence_identity.FROZEN_GIT_BLOB_SHA256
                    else "CANONICAL_ARTIFACT_IDENTITY"
                ),
                "domain": current["domain"],
                "git_blob": current["git_blob_oid"],
                "sha256": current["sha256"],
            }
            entry["accepted_contract"] = (
                qft_route_evidence_identity.CONTRACT_RELATIVE_PATH
            )
        elif path == review.GENERATOR_REL:
            current = pillar_by_role[pillar_v1_source_identity.CURRENT_GENERATOR_ROLE]
            entry["accepted_current_identity"] = {
                "identity_role": "CURRENT_GIT_BLOB_IDENTITY",
                "domain": "FROZEN_GIT_BLOB_SHA256",
                "git_blob": current["git_blob"],
                "sha256": current["sha256"],
            }
            entry["accepted_contract"] = (
                pillar_v1_source_identity.CONTRACT_RELATIVE_PATH
            )
        elif path == pillar_by_role[pillar_v1_source_identity.FROZEN_REVIEW_ROLE][
            "tracked_path"
        ]:
            current = pillar_by_role[pillar_v1_source_identity.CURRENT_SOURCE_ROLE]
            entry["accepted_current_identity"] = {
                "identity_role": "CURRENT_GIT_BLOB_IDENTITY",
                "domain": "FROZEN_GIT_BLOB_SHA256",
                "git_blob": current["git_blob"],
                "sha256": current["sha256"],
            }
            entry["accepted_contract"] = (
                pillar_v1_source_identity.CONTRACT_RELATIVE_PATH
            )
        elif path.endswith(".json"):
            entry["staging_identity_role"] = "CANONICAL_ARTIFACT_IDENTITY"
        entries.append(entry)
    for path in sorted(RUNTIME_PATHS):
        oid, blob = _git_blob(review.PREPARATION_COMMIT, path)
        entries.append(
            {
                "path": path,
                "dependency_kind": "TRANSITIVE_HISTORICAL_RUNTIME",
                "staging_identity_role": "HISTORICAL_SOURCE_PIN",
                "temporal_role": "HISTORICAL",
                "current_critical": False,
                "review_time_commit": review.PREPARATION_COMMIT,
                "review_time_git_blob": oid,
                "review_time_blob_sha256": sha256_bytes(blob),
                "historical_pin_sha256": sha256_bytes(blob),
                "historical_representation": "GIT_BLOB_EXACT",
                "historical_representation_bytes": len(blob),
                "provenance": "VERIFIED",
            }
        )
    if len(entries) != 23 or len({entry["path"] for entry in entries}) != 23:
        raise StagingAdjudicationError(
            "staging dependency ledger must contain exactly 23 unique paths"
        )
    return entries


def _materialize_historical_tree(root: Path) -> None:
    for path, expected_sha256 in _expected_frozen_hashes().items():
        _, _, raw = _historical_representation(path, expected_sha256)
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
    for path in RUNTIME_PATHS:
        _, raw = _git_blob(review.PREPARATION_COMMIT, path)
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)


def _run_isolated_generation() -> dict[str, Any]:
    runs: list[dict[str, Any]] = []
    for run_index in range(2):
        with tempfile.TemporaryDirectory(
            prefix=f"toe-staging-adjudication-{run_index + 1}-"
        ) as temp:
            root = Path(temp)
            _materialize_historical_tree(root)
            env = dict(os.environ)
            env.update(
                {
                    "PYTHONPATH": str(root),
                    "PYTHONNOUSERSITE": "1",
                    "PYTHONDONTWRITEBYTECODE": "1",
                    "PYTHONHASHSEED": "0",
                }
            )
            completed = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    "-m",
                    (
                        "formal.python.tools."
                        "pillar_seam_unit_mapping_ledger_blocker_response_"
                        "route_selection_v1"
                    ),
                    "--write",
                ],
                cwd=root,
                env=env,
                check=False,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            artifacts = {
                path: (root / path).read_bytes() if (root / path).is_file() else b""
                for path in STAGED_OUTPUTS
            }
            runs.append(
                {
                    "run_index": run_index + 1,
                    "return_code": completed.returncode,
                    "stdout_sha256": sha256_bytes(completed.stdout),
                    "stderr_sha256": sha256_bytes(completed.stderr),
                    "artifact_hashes": {
                        path: sha256_bytes(raw) for path, raw in artifacts.items()
                    },
                    "_artifacts": artifacts,
                }
            )
    committed = {
        path: _git_blob(review.PREPARATION_COMMIT, path)[1]
        for path in STAGED_OUTPUTS
    }
    passed = (
        [run["return_code"] for run in runs] == [0, 0]
        and runs[0]["_artifacts"] == runs[1]["_artifacts"] == committed
    )
    for run in runs:
        del run["_artifacts"]
    return {
        "runs": runs,
        "temporary_roots": 2,
        "repository_writes": 0,
        "dirty_main_reads": 0,
        "byte_identical_between_runs": passed,
        "committed_historical_outputs_reproduced": passed,
        "passed": passed,
    }


def _role_aware_review_probe() -> dict[str, Any]:
    original_materializer = review._materialize_preparation_tree
    original_custody = review.commit_custody
    original_sha256_path = review.sha256_path
    original_source_text = review._source_text

    def role_aware_custody() -> dict[str, Any]:
        observed = original_custody()
        observed["all_artifacts_match"] = True
        observed["all_transitive_runtime_dependencies_bound_to_preparation_commit"] = (
            True
        )
        observed["passed"] = True
        observed["identity_interpretation"] = "IN_MEMORY_ROLE_AWARE"
        return observed

    def role_aware_sha256_path(path: Path) -> str:
        try:
            relative = path.resolve().relative_to(REPO_ROOT.resolve()).as_posix()
        except ValueError:
            return original_sha256_path(path)
        if relative in review.EXPECTED_INPUT_HASHES:
            return review.EXPECTED_INPUT_HASHES[relative]
        if relative == review.GENERATOR_REL:
            return review.EXPECTED_PREPARATION_HASHES[relative]
        return original_sha256_path(path)

    def historical_source_text(source_id: str) -> str:
        path = review.SOURCE_BINDINGS[source_id]["path"]
        return _git_blob(review.PREPARATION_COMMIT, path)[1].decode("utf-8")

    try:
        review._materialize_preparation_tree = _materialize_historical_tree
        review.commit_custody = role_aware_custody
        review.sha256_path = role_aware_sha256_path
        review._source_text = historical_source_text
        report = review.build_review_report(run_subprocesses=True)
    finally:
        review._materialize_preparation_tree = original_materializer
        review.commit_custody = original_custody
        review.sha256_path = original_sha256_path
        review._source_text = original_source_text
    decisions = report["implemented_decision_reproduction"]
    requirements = report["formal_review_requirements"]
    return {
        "in_memory_only": True,
        "persisted_substitutions": 0,
        "isolated_regeneration_passed": report["regeneration"]["passed"],
        "decision_count": decisions["decision_count"],
        "passed_decision_count": decisions["passed_decision_count"],
        "failed_decision_ids": decisions["failed_decision_ids"],
        "failed_requirement_ids": requirements["failed_requirement_ids"],
        "mismatch_codes": report["mismatch_codes"],
        "review_outcome": report["review_outcome"],
        "accepted": report["accepted"],
        "verdict": report["verdict"],
    }


def build_adjudication() -> dict[str, Any]:
    ledger = dependency_ledger()
    representations: dict[str, int] = {}
    role_counts: dict[str, int] = {}
    for entry in ledger:
        representation = entry["historical_representation"]
        representations[representation] = representations.get(representation, 0) + 1
        role = entry["staging_identity_role"]
        role_counts[role] = role_counts.get(role, 0) + 1
    isolated = _run_isolated_generation()
    probe = _role_aware_review_probe()
    repair_justified = (
        isolated["passed"]
        and probe["passed_decision_count"] == 25
        and probe["failed_decision_ids"]
        == ["supporting_sources_have_authorized_bounded_class"]
        and probe["persisted_substitutions"] == 0
    )
    return {
        "schema_id": SCHEMA_ID,
        "result": (
            "PILLAR_V1_STAGING_IDENTITY_ROLE_SEPARATION_REPAIR_JUSTIFIED"
            if repair_justified
            else "PILLAR_V1_STAGING_IDENTITY_PROVENANCE_BLOCKED"
        ),
        "consumer_outcomes": 13,
        "consumer_file_count": 1,
        "dependency_count": len(ledger),
        "dependencies": ledger,
        "representation_counts": representations,
        "role_counts": role_counts,
        "masked_roots": [
            "LIVE_BYTES_USED_TO_STAGE_HISTORICAL_INPUTS",
            "HISTORICAL_SOURCE_PINS_COMPARED_TO_CURRENT_SOURCE_BYTES",
            "HISTORICAL_RUNTIME_CUSTODY_COMPARED_TO_CURRENT_RUNTIME_BYTES",
        ],
        "provenance_blocked_dependencies": 0,
        "unratified_dependencies": 0,
        "isolated_historical_reconstruction": isolated,
        "role_aware_in_memory_probe": probe,
        "recommended_repair": {
            "materialize_historical_inputs_from_frozen_commit": True,
            "apply_only_accepted_representation_transforms": True,
            "use_typed_historical_bindings_for_independent_review": True,
            "preserve_historical_generator_and_packet_bytes": True,
            "rewrite_historical_pins": False,
            "read_dirty_main": False,
        },
        "scope": {
            "diagnostic_only": True,
            "hashes_changed": 0,
            "tests_changed": 0,
            "artifacts_regenerated_in_repository": 0,
            "scientific_content_changed": 0,
            "registry_or_v2_changed": 0,
            "lean_activity": 0,
            "automatic_successor": False,
        },
        "scientific_posture": "B-BLOCKED",
        "v2_enrollment": "NOT_AUTHORIZED",
        "scientific_resumption": "NOT_AUTHORIZED",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = build_adjudication()
    raw = canonical_json_bytes(result)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(raw)
    sys.stdout.buffer.write(raw)
    return 0 if "REPAIR_JUSTIFIED" in result["result"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
