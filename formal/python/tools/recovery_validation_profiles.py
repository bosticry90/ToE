from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_VERSION = "v0"
RECOVERED_ROOT_IDS = {
    "PILLAR_V1_FROZEN_REVIEW_SOURCE_PIN_DRIFT",
    "DUPLICATE_MAINTENANCE_AUTHORITY_SELECTOR_KEY",
}
CURRENT_AUTHORITY_PATTERNS = (
    "CURRENT_MAINTENANCE_AUTHORITY_v0.json",
    "current_projection_v0",
    "CURRENT_LIVE_",
    "CURRENT_AUTHORITATIVE_SURFACES_v0",
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_"
    "PACKET_RESULT_REVIEW_20260712_v1",
)
CURRENT_SCIENTIFIC_PATTERNS = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_"
    "PACKET_RESULT_REVIEW_20260712_v1",
    "PillarSeamUnitMappingLedgerBlockerResponseRouteSelectionPacketV1ResultReview",
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_"
    "packet_v2",
)
CURRENT_REPRODUCIBILITY_PATTERNS = (
    "governance_json",
    "recovery_validation_profiles",
    "CURRENT_ACCEPTANCE_INVENTORY",
    "FROZEN_COMPARABILITY_INVENTORY",
    "validation_source_cleanliness",
    "test_repository_tracked_json_integrity_gate.py",
    "test_recovery_accepted_lineage_completeness.py",
    "test_maintenance_authority_duplicate_selector_repair",
    "test_pillar_v1_source_identity",
    "test_pillar_v1_staging_identity_adjudication",
)


class ProfileError(ValueError):
    """Raised when obligation or execution-profile coverage is incomplete."""


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def read_nodeids(path: Path) -> list[str]:
    nodeids = [
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if not nodeids or len(nodeids) != len(set(nodeids)):
        raise ProfileError(f"node-id inventory is empty or duplicated: {path}")
    return nodeids


def load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_bytes())
    if not isinstance(payload, dict):
        raise ProfileError(f"JSON root must be an object: {path}")
    return payload


def _test_path(nodeid: str) -> str:
    return nodeid.split("::", 1)[0]


def _test_source(repo_root: Path, nodeid: str, cache: dict[str, str]) -> str:
    path = _test_path(nodeid)
    if path not in cache:
        source_path = repo_root / path
        cache[path] = (
            source_path.read_text(encoding="utf-8", errors="replace")
            if source_path.is_file()
            else ""
        )
    return cache[path]


def _current_reachability(
    *,
    repo_root: Path,
    nodeid: str,
    added_over_frozen: set[str],
    cache: dict[str, str],
) -> tuple[list[str], list[str]]:
    source = _test_source(repo_root, nodeid, cache)
    test_path = _test_path(nodeid)
    criticality: set[str] = set()
    evidence: list[str] = []
    for pattern in CURRENT_AUTHORITY_PATTERNS:
        if pattern in source or pattern in test_path:
            criticality.add("CURRENT_AUTHORITY")
            criticality.add("CURRENT_REPRODUCIBILITY")
            evidence.append(f"CURRENT_AUTHORITY_PATTERN:{pattern}")
    for pattern in CURRENT_SCIENTIFIC_PATTERNS:
        if pattern in source or pattern in test_path:
            criticality.add("CURRENT_SCIENTIFIC_EVIDENCE")
            criticality.add("CURRENT_REPRODUCIBILITY")
            evidence.append(f"CURRENT_SCIENTIFIC_PATTERN:{pattern}")
    for pattern in CURRENT_REPRODUCIBILITY_PATTERNS:
        if pattern in source or pattern in test_path:
            criticality.add("CURRENT_REPRODUCIBILITY")
            if "recovery_validation_profiles" in pattern or "governance_json" in pattern:
                criticality.add("CURRENT_AUTHORITY")
            evidence.append(f"CURRENT_REPRODUCIBILITY_PATTERN:{pattern}")
    if nodeid in added_over_frozen:
        criticality.add("CURRENT_REPRODUCIBILITY")
        evidence.append("ACCEPTED_GUARD_ADDED_AFTER_FROZEN_COMPARABILITY_INVENTORY")
    return sorted(criticality), sorted(set(evidence))


def _missing_by_nodeid(missing_ledger: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        row["outcome_nodeid"]: row
        for row in missing_ledger.get("expectation_rows", [])
        if isinstance(row, dict) and isinstance(row.get("outcome_nodeid"), str)
    }


def _unratified_nodeids(cluster_ledger: dict[str, Any]) -> set[str]:
    custody = cluster_ledger.get("custody_currency_outcomes", {})
    return set(custody.get("nodeids", []))


def _nonpassing_rows(
    outcomes: dict[str, Any],
    *,
    recovered_root_ids: set[str] | None = None,
    expected_count: int = 370,
) -> list[dict[str, Any]]:
    recovered = (
        RECOVERED_ROOT_IDS if recovered_root_ids is None else recovered_root_ids
    )
    rows = [
        row
        for row in outcomes.get("entries", [])
        if isinstance(row, dict) and row.get("root_id") not in recovered
    ]
    if len(rows) != expected_count:
        raise ProfileError(
            "adjusted accepted nonpassing inventory must contain "
            f"{expected_count} outcomes, got {len(rows)}"
        )
    return rows


def _adjudication_by_obligation_id(
    adjudication_ledger: dict[str, Any] | None,
) -> dict[str, dict[str, Any]]:
    if adjudication_ledger is None:
        return {}
    rows = adjudication_ledger.get("rows", [])
    mapped = {
        row["obligation_id"]: row
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("obligation_id"), str)
    }
    if len(mapped) != len(rows):
        raise ProfileError("reachability adjudication contains duplicate obligation IDs")
    if adjudication_ledger.get("counts", {}).get(
        "unknown_current_reachability_after"
    ) != 0:
        raise ProfileError("reachability adjudication has unresolved current reachability")
    return mapped


def _nonpassing_axes(
    row: dict[str, Any],
    *,
    reachable_criticality: list[str],
    reachability_evidence: list[str],
    missing_row: dict[str, Any] | None,
    unratified: bool,
) -> dict[str, Any]:
    family = row["root_family"]
    root_id = row["root_id"]
    if reachable_criticality:
        temporal_role = (
            "HISTORICAL"
            if root_id == "PILLAR_V1_ISOLATED_STAGING_HASH_DRIFT"
            else "CURRENT"
        )
        return {
            "criticality": reachable_criticality,
            "temporal_role": temporal_role,
            "provenance": "VERIFIED",
            "disposition": "PENDING_REPAIR",
            "current_reachability_unknown": False,
            "reachability_evidence": reachability_evidence,
        }
    if family == "missing_artifacts":
        authority = (
            missing_row.get("authority_classification")
            if missing_row is not None
            else "PROVENANCE_INCOMPLETE"
        )
        provenance = (
            "BLOCKED" if authority == "PROVENANCE_INCOMPLETE" else "VERIFIED"
        )
        temporal_role = (
            "OBSOLETE"
            if authority == "STALE_EXPECTATION_TO_RETIRE"
            else "HISTORICAL"
        )
        return {
            "criticality": ["NONCURRENT"],
            "temporal_role": temporal_role,
            "provenance": provenance,
            "disposition": "QUARANTINED",
            "current_reachability_unknown": False,
            "reachability_evidence": [
                "ACCEPTED_MISSING_ARTIFACT_ADJUDICATION_CURRENT_DECISION_BEARING_ZERO"
            ],
        }
    if unratified:
        return {
            "criticality": ["NONCURRENT"],
            "temporal_role": "UNRATIFIED_POST_REGISTRY",
            "provenance": "VERIFIED",
            "disposition": "QUARANTINED",
            "current_reachability_unknown": False,
            "reachability_evidence": [
                "ACCEPTED_POST_DECOUPLING_CUSTODY_CURRENCY_CLASSIFICATION"
            ],
        }
    if root_id == "PILLAR_V1_ISOLATED_STAGING_HASH_DRIFT":
        return {
            "criticality": [
                "CURRENT_AUTHORITY",
                "CURRENT_SCIENTIFIC_EVIDENCE",
                "CURRENT_REPRODUCIBILITY",
            ],
            "temporal_role": "HISTORICAL",
            "provenance": "VERIFIED",
            "disposition": "PENDING_REPAIR",
            "current_reachability_unknown": False,
            "reachability_evidence": [
                "REGISTRY_CURRENT_PROJECTION_DEPENDS_ON_V1_RESULT_REVIEW"
            ],
        }
    if family == "authority_expectations":
        return {
            "criticality": ["CURRENT_AUTHORITY", "CURRENT_REPRODUCIBILITY"],
            "temporal_role": "CURRENT",
            "provenance": "INCOMPLETE",
            "disposition": "BLOCKING",
            "current_reachability_unknown": False,
            "reachability_evidence": ["AUTHORITY_EXPECTATION_ROOT"],
        }
    if family == "environment_or_path_identity":
        return {
            "criticality": ["CURRENT_REPRODUCIBILITY"],
            "temporal_role": "CURRENT",
            "provenance": "INCOMPLETE",
            "disposition": "BLOCKING",
            "current_reachability_unknown": False,
            "reachability_evidence": ["CLEAN_CLONE_REPRODUCIBILITY_ROOT"],
        }
    return {
        "criticality": ["CURRENT_REPRODUCIBILITY"],
        "temporal_role": "CURRENT",
        "provenance": "INCOMPLETE",
        "disposition": "BLOCKING",
        "current_reachability_unknown": True,
        "reachability_evidence": [
            "CONSERVATIVE_BLOCK_UNTIL_CURRENT_REACHABILITY_ADJUDICATED"
        ],
    }


def build_profiles(
    *,
    repo_root: Path,
    current_nodeids: list[str],
    frozen_nodeids: list[str],
    outcome_ledger: dict[str, Any],
    missing_ledger: dict[str, Any],
    cluster_ledger: dict[str, Any],
    relative_to_commit: str,
    adjudication_ledger: dict[str, Any] | None = None,
    recovered_root_ids: set[str] | None = None,
    expected_nonpassing: int = 370,
    schema_version: str = SCHEMA_VERSION,
) -> dict[str, Any]:
    current_set = set(current_nodeids)
    frozen_set = set(frozen_nodeids)
    if not frozen_set <= current_set:
        raise ProfileError("frozen comparability inventory is not a subset of current")
    added_over_frozen = current_set - frozen_set
    missing = _missing_by_nodeid(missing_ledger)
    unratified = _unratified_nodeids(cluster_ledger)
    nonpassing = _nonpassing_rows(
        outcome_ledger,
        recovered_root_ids=recovered_root_ids,
        expected_count=expected_nonpassing,
    )
    adjudication = _adjudication_by_obligation_id(adjudication_ledger)
    nonpassing_by_nodeid = {row["nodeid"]: row for row in nonpassing}
    if len(nonpassing_by_nodeid) != len(nonpassing):
        raise ProfileError("adjusted nonpassing inventory contains duplicate node IDs")

    cache: dict[str, str] = {}
    reachability: dict[str, tuple[list[str], list[str]]] = {
        nodeid: _current_reachability(
            repo_root=repo_root,
            nodeid=nodeid,
            added_over_frozen=added_over_frozen,
            cache=cache,
        )
        for nodeid in current_nodeids
    }
    obligations: list[dict[str, Any]] = []
    profile_by_nodeid: dict[str, str] = {}
    for index, nodeid in enumerate(current_nodeids, start=1):
        criticality, evidence = reachability[nodeid]
        if criticality:
            obligations.append(
                {
                    "obligation_id": f"CURRENT-{index:05d}",
                    "test_id": nodeid,
                    "causal_root": "CURRENT_REACHABILITY_COVERAGE",
                    "dependency": evidence,
                    "reachability_evidence": evidence,
                    "criticality": criticality,
                    "temporal_role": "CURRENT",
                    "provenance": "VERIFIED",
                    "disposition": "BLOCKING",
                }
            )
        if nodeid in nonpassing_by_nodeid:
            row = nonpassing_by_nodeid[nodeid]
            obligation_id = f"NONPASSING-{row['order_index']:05d}"
            accepted_axes = adjudication.get(obligation_id)
            if accepted_axes is None:
                axes = _nonpassing_axes(
                    row,
                    reachable_criticality=criticality,
                    reachability_evidence=evidence,
                    missing_row=missing.get(nodeid),
                    unratified=nodeid in unratified,
                )
            else:
                if accepted_axes["test_id"] != nodeid:
                    raise ProfileError(
                        f"adjudication node ID mismatch for {obligation_id}"
                    )
                axes = {
                    "criticality": accepted_axes["criticality"],
                    "temporal_role": accepted_axes["temporal_role"],
                    "provenance": accepted_axes["provenance"],
                    "disposition": accepted_axes["disposition"],
                    "current_reachability_unknown": False,
                    "reachability_evidence": accepted_axes[
                        "reachability_evidence"
                    ],
                }
            obligations.append(
                {
                    "obligation_id": obligation_id,
                    "test_id": nodeid,
                    "causal_root": row["root_id"],
                    "dependency": row.get("first_exception", ""),
                    **axes,
                }
            )
            if accepted_axes is not None and axes["criticality"] == ["NONCURRENT"]:
                criticality = []
            elif axes["criticality"] != ["NONCURRENT"]:
                criticality = sorted(
                    set(criticality) | set(axes["criticality"])
                )
        profile_by_nodeid[nodeid] = (
            "current_control_plane" if criticality else "historical_debt"
        )

    current_profile = [
        nodeid
        for nodeid in current_nodeids
        if profile_by_nodeid[nodeid] == "current_control_plane"
    ]
    historical_profile = [
        nodeid
        for nodeid in current_nodeids
        if profile_by_nodeid[nodeid] == "historical_debt"
    ]
    if (
        set(current_profile) & set(historical_profile)
        or set(current_profile) | set(historical_profile) != current_set
        or len(current_profile) + len(historical_profile) != len(current_nodeids)
    ):
        raise ProfileError("execution profiles do not exactly partition collection")
    current_nonpassing = [
        row["nodeid"]
        for row in nonpassing
        if profile_by_nodeid[row["nodeid"]] == "current_control_plane"
    ]
    historical_nonpassing = [
        row["nodeid"]
        for row in nonpassing
        if profile_by_nodeid[row["nodeid"]] == "historical_debt"
    ]
    registry = {
        "schema_id": f"RECOVERY_OBLIGATION_REGISTRY_20260725_{schema_version}",
        "current_relative_to_commit": relative_to_commit,
        "classification_universe": {
            "current_authority_reachable": sum(
                "CURRENT_AUTHORITY" in criticality
                for criticality, _ in reachability.values()
            ),
            "current_scientific_evidence_reachable": sum(
                "CURRENT_SCIENTIFIC_EVIDENCE" in criticality
                for criticality, _ in reachability.values()
            ),
            "current_reproducibility_reachable": sum(
                "CURRENT_REPRODUCIBILITY" in criticality
                for criticality, _ in reachability.values()
            ),
            "adjusted_nonpassing": len(nonpassing),
            "obligations": len(obligations),
        },
        "axes": {
            "criticality": [
                "CURRENT_AUTHORITY",
                "CURRENT_SCIENTIFIC_EVIDENCE",
                "CURRENT_REPRODUCIBILITY",
                "NONCURRENT",
            ],
            "temporal_role": [
                "CURRENT",
                "HISTORICAL",
                "UNRATIFIED_POST_REGISTRY",
                "OBSOLETE",
            ],
            "provenance": ["VERIFIED", "INCOMPLETE", "BLOCKED"],
            "disposition": ["BLOCKING", "QUARANTINED", "RETIRED", "PENDING_REPAIR"],
        },
        "obligations": obligations,
    }
    profile_common = {
        "current_relative_to_commit": relative_to_commit,
        "inventory_count": len(current_nodeids),
        "inventory_sha256": sha256_bytes(
            ("\n".join(current_nodeids) + "\n").encode("utf-8")
        ),
        "membership_basis": "AUTHORITY_AND_EVIDENCE_REACHABILITY_NOT_TEST_OUTCOME",
        "membership_change_requires_independent_review": True,
        "tests_may_modify_membership": False,
    }
    current_manifest = {
        "schema_id": f"CURRENT_CONTROL_PLANE_PROFILE_20260725_{schema_version}",
        **profile_common,
        "profile": "current_control_plane",
        "nodeid_count": len(current_profile),
        "nodeids": current_profile,
        "known_nonpassing_count": len(current_nonpassing),
        "known_nonpassing_nodeids": current_nonpassing,
        "required_verdict": "PASS",
    }
    historical_manifest = {
        "schema_id": f"HISTORICAL_DEBT_PROFILE_20260725_{schema_version}",
        **profile_common,
        "profile": "historical_debt",
        "nodeid_count": len(historical_profile),
        "nodeids": historical_profile,
        "known_nonpassing_count": len(historical_nonpassing),
        "known_nonpassing_nodeids": historical_nonpassing,
        "permitted_verdict": "COMPLETE_WITH_RECORDED_FAILURES",
    }
    unresolved_unknown = sum(
        obligation.get("current_reachability_unknown") is True
        for obligation in obligations
    )
    reconciliation = {
        "schema_id": f"VALIDATION_PROFILE_RECONCILIATION_20260725_{schema_version}",
        **profile_common,
        "collected_count": len(current_nodeids),
        "current_control_plane_count": len(current_profile),
        "historical_debt_count": len(historical_profile),
        "intersection_count": 0,
        "unassigned_count": 0,
        "excluded_count": 0,
        "adjusted_nonpassing_count": len(nonpassing),
        "current_control_plane_known_nonpassing": len(current_nonpassing),
        "historical_debt_known_nonpassing": len(historical_nonpassing),
        "unknown_current_reachability_obligations": unresolved_unknown,
        "profile_machinery_current_critical": True,
        "exact_partition": True,
    }
    return {
        "registry": registry,
        "current": current_manifest,
        "historical": historical_manifest,
        "reconciliation": reconciliation,
    }


def write_profiles(
    output_root: Path,
    profiles: dict[str, Any],
    *,
    schema_version: str = SCHEMA_VERSION,
) -> dict[str, str]:
    output_root.mkdir(parents=True, exist_ok=True)
    filenames = {
        "registry": f"RECOVERY_OBLIGATION_REGISTRY_20260725_{schema_version}.json",
        "current": f"CURRENT_CONTROL_PLANE_PROFILE_20260725_{schema_version}.json",
        "historical": f"HISTORICAL_DEBT_PROFILE_20260725_{schema_version}.json",
        "reconciliation": (
            f"VALIDATION_PROFILE_RECONCILIATION_20260725_{schema_version}.json"
        ),
    }
    hashes: dict[str, str] = {}
    for key, filename in filenames.items():
        path = output_root / filename
        raw = canonical_json_bytes(profiles[key])
        path.write_bytes(raw)
        hashes[filename] = sha256_bytes(raw)
    return hashes


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--current-inventory", type=Path, required=True)
    parser.add_argument("--frozen-inventory", type=Path, required=True)
    parser.add_argument("--outcome-ledger", type=Path, required=True)
    parser.add_argument("--missing-ledger", type=Path, required=True)
    parser.add_argument("--cluster-ledger", type=Path, required=True)
    parser.add_argument("--relative-to-commit", required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--adjudication-ledger", type=Path)
    parser.add_argument("--expected-nonpassing", type=int, default=370)
    parser.add_argument("--schema-version", default=SCHEMA_VERSION)
    parser.add_argument(
        "--recovered-root-id",
        action="append",
        default=sorted(RECOVERED_ROOT_IDS),
    )
    args = parser.parse_args()
    profiles = build_profiles(
        repo_root=REPO_ROOT,
        current_nodeids=read_nodeids(args.current_inventory),
        frozen_nodeids=read_nodeids(args.frozen_inventory),
        outcome_ledger=load_json(args.outcome_ledger),
        missing_ledger=load_json(args.missing_ledger),
        cluster_ledger=load_json(args.cluster_ledger),
        relative_to_commit=args.relative_to_commit,
        adjudication_ledger=(
            load_json(args.adjudication_ledger)
            if args.adjudication_ledger is not None
            else None
        ),
        recovered_root_ids=set(args.recovered_root_id),
        expected_nonpassing=args.expected_nonpassing,
        schema_version=args.schema_version,
    )
    hashes = write_profiles(
        args.output_root,
        profiles,
        schema_version=args.schema_version,
    )
    sys.stdout.buffer.write(
        canonical_json_bytes(
            {
                "hashes": hashes,
                "reconciliation": profiles["reconciliation"],
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
