#!/usr/bin/env python3
"""Build or verify the July 16--19 dirty-checkout classification record.

Generation is intentionally custody-bound: it accepts only the immutable
manifest captured before repository integration began. Verification of the
committed release record does not require access to the external archive.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
OUTPUT_RELATIVE_PATH = (
    "formal/docs/release/"
    "JULY_16_19_DIRTY_CHECKOUT_TRANCHE_CLASSIFICATION_20260727_v0.json"
)
EXPECTED_CUSTODY_MANIFEST_SHA256 = (
    "5ef2a369f40e37b41d6bad5dc1e1f442bc0f8344811386fdf27acadfc5c4ae39"
)
EXPECTED_ARCHIVE_SHA256 = (
    "83c634813cad11de1a8d0389ef9de32526c291b609d498d8c7d6118becfa2902"
)
EXPECTED_ROW_COUNT = 629
EXPECTED_EXTERNAL_DATA_COUNT = 24

FRONT_DOOR_PATHS = {
    "MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md",
    "PUBLIC_OVERVIEW.md",
    "TECHNICAL_REPOSITORY_GUIDE.md",
}
AUTHORITY_MIRROR_PATHS = {
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _packet_family(path: str) -> str:
    normalized = "".join(ch for ch in Path(path).name.lower() if ch.isalnum())
    if "diracmaxwell" in normalized or "postr13fulltoe" in normalized:
        return "DIRAC_MAXWELL_R13_CLOSEOUT"
    if "srpillar" in normalized or "postsrtooling" in normalized:
        return "SR_RESTORATION_TOOLING"
    if (
        "externalrelatedwork" in normalized
        or "gferelativeentropy" in normalized
        or "grfield" in normalized
        or "grnative" in normalized
        or "grweak" in normalized
        or "minimalnativecontinuum" in normalized
        or "nativecontinuumaction" in normalized
        or "toecandidatemaster" in normalized
    ):
        return "GR_CONTINUUM_AND_AUTHORITY_RECONCILIATION"
    if (
        "exploratorynativegravitational" in normalized
        or "nativegravitationalprinciple" in normalized
    ):
        return "NATIVE_GRAVITATIONAL_REQUIREMENTS"
    if "quadraticgravity" in normalized:
        return "QUADRATIC_GRAVITY_COMPARISON"
    if "eotwash" in normalized or "outboundresearchcontact" in normalized:
        return "EOTWASH_EVIDENCE_CUSTODY"
    if "scalaronlyyukawa" in normalized:
        return "SCALAR_ONLY_YUKAWA"
    if path.startswith("formal/docs/paper/"):
        return "SCIENTIFIC_METHODS_DOCUMENTATION"
    return "CROSS_PACKET_OR_UNCLASSIFIED"


def _classify(row: dict[str, Any]) -> dict[str, Any]:
    path = str(row["path"])
    common = {
        "path": path,
        "snapshot_git_state": row["git_state"],
        "size_bytes": row["size_bytes"],
        "sha256": row.get("sha256"),
        "packet_family": _packet_family(path),
    }
    if path.startswith(
        "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
    ):
        return {
            **common,
            "provenance": "REMOTE_ACQUISITION_CAPTURED_BY_HISTORICAL_PACKET",
            "licensing_and_redistribution": "UNRESOLVED_PER_FILE",
            "privacy": "NOT_CLEARED_FOR_REPOSITORY_RETENTION",
            "security": "PASSIVE_EXTERNAL_BYTES_NOT_CLEARED",
            "material_kind": "EXTERNAL_SOURCE_EVIDENCE_OR_FETCH_METADATA",
            "repository_disposition": (
                "INTENTIONALLY_IGNORED_EXTERNAL_CUSTODY_ONLY_PENDING_RIGHTS_REVIEW"
            ),
            "scientific_status": "PRESERVED_EXTERNAL_CUSTODY_NOT_ADOPTED",
        }
    if path in FRONT_DOOR_PATHS:
        return {
            **common,
            "provenance": "TRACKED_BASE_VERSION_WITH_DIRTY_CHECKOUT_DELETION",
            "material_kind": "PUBLIC_ENTRY_DOCUMENT",
            "repository_disposition": "PENDING_FRONT_DOOR_DISPOSITION",
            "scientific_status": "NOT_APPLICABLE_MAINTENANCE_SURFACE",
        }
    if path == "README.md":
        return {
            **common,
            "provenance": "MODIFIED_TRACKED_REPOSITORY_SURFACE",
            "material_kind": "PUBLIC_ENTRY_DOCUMENT",
            "repository_disposition": "PENDING_FRONT_DOOR_REPAIR",
            "scientific_status": "NOT_APPLICABLE_MAINTENANCE_SURFACE",
        }
    if path in AUTHORITY_MIRROR_PATHS:
        return {
            **common,
            "provenance": "MODIFIED_TRACKED_SCIENTIFIC_MIRROR",
            "material_kind": "SCIENTIFIC_AUTHORITY_MIRROR",
            "repository_disposition": (
                "MAINTENANCE_INTEGRATED_RESTORED_TO_CANONICAL_REGISTRY"
            ),
            "scientific_status": "NO_SCIENTIFIC_AUTHORITY_ROTATION",
        }
    return {
        **common,
        "provenance": "DIRTY_CHECKOUT_AT_IMMUTABLE_CUSTODY_SNAPSHOT",
        "material_kind": (
            "GENERATED_OUTPUT"
            if path.startswith("formal/output/")
            else "PROJECT_ARTIFACT"
        ),
        "repository_disposition": "PRESERVE_IN_REPOSITORY",
        "scientific_status": "PRESERVED_NOT_ADOPTED",
    }


def build_record(custody_manifest_path: Path) -> dict[str, Any]:
    observed_manifest_hash = _sha256(custody_manifest_path)
    if observed_manifest_hash != EXPECTED_CUSTODY_MANIFEST_SHA256:
        raise ValueError(
            "unexpected custody manifest: "
            f"{observed_manifest_hash} != {EXPECTED_CUSTODY_MANIFEST_SHA256}"
        )
    custody = _load_object(custody_manifest_path)
    source_rows = custody.get("files")
    if not isinstance(source_rows, list) or len(source_rows) != EXPECTED_ROW_COUNT:
        raise ValueError("custody manifest file inventory is incomplete")
    rows = [_classify(row) for row in source_rows]
    disposition_counts = Counter(row["repository_disposition"] for row in rows)
    family_counts = Counter(row["packet_family"] for row in rows)
    external_rows = [
        row
        for row in rows
        if row["repository_disposition"].startswith("INTENTIONALLY_IGNORED_")
    ]
    if len(external_rows) != EXPECTED_EXTERNAL_DATA_COUNT:
        raise ValueError("external-data quarantine count changed")
    return {
        "schema_id": "JULY_16_19_DIRTY_CHECKOUT_TRANCHE_CLASSIFICATION_v0",
        "status": "MAINTENANCE_CLASSIFICATION_NOT_SCIENTIFIC_ADOPTION",
        "custody_manifest": {
            "filename": custody_manifest_path.name,
            "sha256": observed_manifest_hash,
            "row_count": len(rows),
            "preservation_timestamp_utc": custody["preservation_timestamp_utc"],
        },
        "extant_byte_archive": {
            "filename": "toe_dirty_checkout_extant_files.zip",
            "sha256": EXPECTED_ARCHIVE_SHA256,
            "location_policy": "EXTERNAL_IMMUTABLE_CUSTODY",
        },
        "classification_policy": {
            "project_artifacts": "PRESERVE_IN_REPOSITORY_AS_PRESERVED_NOT_ADOPTED",
            "external_acquisition_bytes": (
                "INTENTIONALLY_IGNORE_AND_RETAIN_ONLY_IN_EXTERNAL_CUSTODY_"
                "UNTIL_RIGHTS_PRIVACY_AND_SECURITY_REVIEW"
            ),
            "commitment_semantics": (
                "BYTE_PRESERVATION_DOES_NOT_CONSTITUTE_SCIENTIFIC_ADOPTION"
            ),
            "scientific_authority_rotation": "PROHIBITED",
            "new_physics": "PROHIBITED",
            "yukawa_rerun": "PROHIBITED",
        },
        "counts": {
            "inventory_rows": len(rows),
            "by_repository_disposition": dict(sorted(disposition_counts.items())),
            "by_packet_family": dict(sorted(family_counts.items())),
        },
        "external_custody_only_rows": external_rows,
        "snapshot_inventory": rows,
    }


def validate_record(record: dict[str, Any]) -> None:
    if record.get("schema_id") != (
        "JULY_16_19_DIRTY_CHECKOUT_TRANCHE_CLASSIFICATION_v0"
    ):
        raise ValueError("classification schema mismatch")
    if record.get("status") != (
        "MAINTENANCE_CLASSIFICATION_NOT_SCIENTIFIC_ADOPTION"
    ):
        raise ValueError("classification status mismatch")
    custody = record.get("custody_manifest", {})
    if custody.get("sha256") != EXPECTED_CUSTODY_MANIFEST_SHA256:
        raise ValueError("custody manifest hash mismatch")
    if custody.get("row_count") != EXPECTED_ROW_COUNT:
        raise ValueError("classification inventory row count mismatch")
    external_rows = record.get("external_custody_only_rows")
    if not isinstance(external_rows, list):
        raise ValueError("external-custody rows missing")
    if len(external_rows) != EXPECTED_EXTERNAL_DATA_COUNT:
        raise ValueError("external-custody row count mismatch")
    paths = {row.get("path") for row in external_rows}
    if len(paths) != EXPECTED_EXTERNAL_DATA_COUNT:
        raise ValueError("external-custody paths are missing or duplicated")
    if not all(
        str(path).startswith(
            "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
        )
        for path in paths
    ):
        raise ValueError("external-custody scope escaped the acquisition root")
    policy = record.get("classification_policy", {})
    if policy.get("scientific_authority_rotation") != "PROHIBITED":
        raise ValueError("classification improperly rotates scientific authority")
    if policy.get("yukawa_rerun") != "PROHIBITED":
        raise ValueError("classification improperly authorizes a Yukawa rerun")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--custody-manifest",
        type=Path,
        help="immutable external custody_manifest.json used for generation",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=REPO_ROOT / OUTPUT_RELATIVE_PATH,
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="verify the committed classification record",
    )
    args = parser.parse_args()
    if args.verify:
        validate_record(_load_object(args.output))
        print(f"PASS: {args.output}")
        return 0
    if args.custody_manifest is None:
        parser.error("--custody-manifest is required unless --verify is used")
    record = build_record(args.custody_manifest)
    validate_record(record)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"WROTE: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
