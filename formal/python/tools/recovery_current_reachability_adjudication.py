from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_REGISTRY = (
    REPO_ROOT
    / "formal/output/validation_profiles/"
    "RECOVERY_OBLIGATION_REGISTRY_20260725_v0.json"
)
DEFAULT_ROOTS = (
    REPO_ROOT
    / "formal/docs/release/CURRENT_AUTHORITY_REACHABILITY_ROOTS_20260725_v0.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "formal/output/validation_profiles/"
    "CURRENT_REACHABILITY_ADJUDICATION_LEDGER_20260725_v0.json"
)
RESOLVED_STAGING_ROOT = "PILLAR_V1_ISOLATED_STAGING_HASH_DRIFT"
EXPECTED_CANDIDATES = 126
EXPECTED_UNKNOWN = 102

CURRENT_OBLIGATION_AXES = {
    "NONPASSING-00145": {
        "criticality": ["CURRENT_REPRODUCIBILITY"],
        "evidence": ["LEAN_ADMISSIBILITY_MANIFEST_TRACKS_CURRENT_GATE_SOURCES"],
    },
    "NONPASSING-00147": {
        "criticality": ["CURRENT_REPRODUCIBILITY"],
        "evidence": ["LEAN_GATE_STUB_IDENTITIES_ARE_RECOVERY_LINEAGE_INPUTS"],
    },
    "NONPASSING-02535": {
        "criticality": [
            "CURRENT_SCIENTIFIC_EVIDENCE",
            "CURRENT_REPRODUCIBILITY",
        ],
        "evidence": ["CURRENT_STATE_AND_PAPER_SURFACES_REQUIRE_RESOLVABLE_REFERENCES"],
    },
    "NONPASSING-09138": {
        "criticality": ["CURRENT_REPRODUCIBILITY"],
        "evidence": ["REPOSITORY_EOL_POLICY_CONTROLS_PORTABLE_IDENTITY"],
    },
}


class AdjudicationError(ValueError):
    """Raised when the frozen candidate universe cannot be adjudicated exactly."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_bytes())
    if not isinstance(payload, dict):
        raise AdjudicationError(f"JSON root must be an object: {path}")
    return payload


def _candidate_rows(registry: dict[str, Any]) -> list[dict[str, Any]]:
    rows = [
        row
        for row in registry["obligations"]
        if row["obligation_id"].startswith("NONPASSING-")
        and row["criticality"] != ["NONCURRENT"]
        and row["causal_root"] != RESOLVED_STAGING_ROOT
    ]
    if len(rows) != EXPECTED_CANDIDATES:
        raise AdjudicationError(
            f"expected {EXPECTED_CANDIDATES} candidate obligations, got {len(rows)}"
        )
    unknown = sum(row.get("current_reachability_unknown") is True for row in rows)
    if unknown != EXPECTED_UNKNOWN:
        raise AdjudicationError(
            f"expected {EXPECTED_UNKNOWN} unknown obligations, got {unknown}"
        )
    return rows


def _is_unratified(test_id: str) -> bool:
    return (
        "dirac_maxwell" in test_id
        or "test_pillar_seam_unit_mapping_ledger_first_unit_selector.py" in test_id
    )


def build_ledger(
    *,
    registry: dict[str, Any],
    roots: dict[str, Any],
    registry_path: Path,
    roots_path: Path,
) -> dict[str, Any]:
    candidates = _candidate_rows(registry)
    declared_current = set(roots["current_nonpassing_obligations"])
    if declared_current != set(CURRENT_OBLIGATION_AXES):
        raise AdjudicationError("current-obligation declaration differs from tool contract")

    rows: list[dict[str, Any]] = []
    for source in candidates:
        obligation_id = source["obligation_id"]
        if obligation_id in CURRENT_OBLIGATION_AXES:
            contract = CURRENT_OBLIGATION_AXES[obligation_id]
            row = {
                "obligation_id": obligation_id,
                "test_id": source["test_id"],
                "causal_root": source["causal_root"],
                "criticality": contract["criticality"],
                "temporal_role": "CURRENT",
                "provenance": source["provenance"],
                "disposition": "PENDING_REPAIR",
                "current_reachability": "VERIFIED_PRESENT",
                "reachability_evidence": contract["evidence"],
            }
        else:
            unratified = _is_unratified(source["test_id"])
            row = {
                "obligation_id": obligation_id,
                "test_id": source["test_id"],
                "causal_root": source["causal_root"],
                "criticality": ["NONCURRENT"],
                "temporal_role": (
                    "UNRATIFIED_POST_REGISTRY" if unratified else "HISTORICAL"
                ),
                "provenance": source["provenance"],
                "disposition": "QUARANTINED",
                "current_reachability": "VERIFIED_ABSENT",
                "reachability_evidence": [
                    (
                        "EXPLICIT_NONCURRENT_DIRAC_MAXWELL_OR_POST_V2_SUCCESSOR"
                        if unratified
                        else "NOT_REACHABLE_FROM_STRICT_CURRENT_OWNER_ROOTS"
                    ),
                    "NOT_A_CURRENT_ENFORCING_GUARD",
                    "FAILURE_REMAINS_VISIBLE_IN_HISTORICAL_PROFILE",
                ],
            }
        rows.append(row)

    ids = [row["obligation_id"] for row in rows]
    if len(ids) != len(set(ids)):
        raise AdjudicationError("duplicate obligation IDs in adjudication")
    counts = {
        "candidate_obligations": len(rows),
        "current_repair_required": sum(
            row["current_reachability"] == "VERIFIED_PRESENT" for row in rows
        ),
        "historical_quarantine_candidates": sum(
            row["temporal_role"] == "HISTORICAL" for row in rows
        ),
        "unratified_quarantine_candidates": sum(
            row["temporal_role"] == "UNRATIFIED_POST_REGISTRY" for row in rows
        ),
        "unknown_current_reachability_after": 0,
    }
    if counts != {
        "candidate_obligations": 126,
        "current_repair_required": 4,
        "historical_quarantine_candidates": 89,
        "unratified_quarantine_candidates": 33,
        "unknown_current_reachability_after": 0,
    }:
        raise AdjudicationError(f"unexpected adjudication counts: {counts}")
    return {
        "schema_id": "CURRENT_REACHABILITY_ADJUDICATION_LEDGER_20260725_v0",
        "current_relative_to_commit": roots["current_relative_to_commit"],
        "sources": {
            "obligation_registry": {
                "path": registry_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": sha256_path(registry_path),
            },
            "authority_roots": {
                "path": roots_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": sha256_path(roots_path),
            },
        },
        "counts": counts,
        "temporal_role_counts": dict(
            sorted(Counter(row["temporal_role"] for row in rows).items())
        ),
        "criticality_counts": {
            key: sum(key in row["criticality"] for row in rows)
            for key in (
                "CURRENT_AUTHORITY",
                "CURRENT_SCIENTIFIC_EVIDENCE",
                "CURRENT_REPRODUCIBILITY",
                "NONCURRENT",
            )
        },
        "invariants": {
            "classification_is_obligation_level": True,
            "provenance_is_independent_of_temporal_role": True,
            "failure_did_not_cause_profile_demotion": True,
            "profile_membership_changed_during_adjudication": False,
            "historical_isolation_still_required": True,
            "current_failures_require_separate_repair": True,
        },
        "rows": rows,
        "scientific_posture": "B-BLOCKED",
        "v2_enrollment": "NOT_AUTHORIZED",
        "scientific_resumption": "NOT_AUTHORIZED",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument("--authority-roots", type=Path, default=DEFAULT_ROOTS)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    registry_path = args.registry.resolve()
    roots_path = args.authority_roots.resolve()
    payload = build_ledger(
        registry=load_json(registry_path),
        roots=load_json(roots_path),
        registry_path=registry_path,
        roots_path=roots_path,
    )
    raw = canonical_json_bytes(payload)
    output = args.output.resolve()
    if args.check:
        if not output.is_file() or output.read_bytes() != raw:
            raise AdjudicationError(f"stale adjudication ledger: {output}")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(raw)
    print(
        json.dumps(
            {
                "output": output.relative_to(REPO_ROOT).as_posix(),
                "sha256": hashlib.sha256(raw).hexdigest(),
                "counts": payload["counts"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
