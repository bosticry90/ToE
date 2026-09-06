from __future__ import annotations

"""Profile the census indexer on a generated, nonauthoritative corpus."""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import hashlib
import json
import tempfile
from collections import Counter
from pathlib import Path

from formal.python.tools.native_hypothesis_census_index_v1 import (
    build_maintenance_trial,
)


def _synthetic_bytes(index: int, extension: str) -> bytes:
    duplicate_group = index // 8
    if extension == "json":
        text = json.dumps(
            {
                "synthetic": True,
                "group": duplicate_group,
                "values": list(range(32)),
            },
            sort_keys=True,
        )
    elif extension == "csv":
        text = "key,value\n" + "\n".join(
            f"{row},{duplicate_group + row}" for row in range(64)
        )
    elif extension == "py":
        text = (
            '"""Synthetic passive-content trial; never execute."""\n'
            f"GROUP = {duplicate_group}\n"
        )
    elif extension == "zip":
        return b"PK\x03\x04synthetic-container-metadata-only-" + str(
            duplicate_group
        ).encode("ascii")
    else:
        text = (
            f"# Synthetic record {duplicate_group}\n\n"
            + ("bounded maintenance content\n" * 64)
        )
    return text.encode("utf-8")


def build_profile(file_count: int) -> dict:
    if file_count <= 0 or file_count > 4096:
        raise ValueError("synthetic file count must be between 1 and 4096")
    extensions = ("md", "json", "csv", "py", "zip")
    with tempfile.TemporaryDirectory(
        prefix="toe-census-maintenance-profile-"
    ) as temporary:
        temporary_root = Path(temporary)
        source_root = temporary_root / "synthetic-corpus"
        source_root.mkdir()
        corpus_digest = hashlib.sha256()
        type_counts: Counter[str] = Counter()
        total_bytes = 0
        for index in range(file_count):
            extension = extensions[index % len(extensions)]
            data = _synthetic_bytes(index, extension)
            path = source_root / f"source-{index:04d}.{extension}"
            path.write_bytes(data)
            corpus_digest.update(path.name.encode("utf-8"))
            corpus_digest.update(data)
            type_counts[extension] += 1
            total_bytes += len(data)
        trial = build_maintenance_trial(
            source_root,
            temporary_root / "cache.sqlite3",
            "SYNTHETIC_PERFORMANCE_PROFILE",
        )
    cold = trial["initial_snapshot"]["performance"]
    warm = trial["cache_reuse_trial"]
    verified = trial["final_snapshot"]["performance"]
    wall = float(verified["elapsed_wall_seconds"])
    cpu = float(verified["elapsed_cpu_seconds"])
    return {
        "schema_id": "toe.native_hypothesis_census.maintenance_profile.v1",
        "status": "SYNTHETIC_NONAUTHORITATIVE_PROFILE_COMPLETE",
        "scientific_archive_traversed": False,
        "authoritative_census_index_generated": False,
        "synthetic_corpus": {
            "file_count": file_count,
            "aggregate_bytes": total_bytes,
            "type_counts": dict(sorted(type_counts.items())),
            "corpus_sha256": corpus_digest.hexdigest(),
        },
        "cold_verified_scan": cold,
        "warm_metadata_hint_cache_scan": warm,
        "final_verified_scan": verified,
        "snapshot_stability": trial["mutation_comparison"]["stability_status"],
        "batch_coverage": trial["aggregate_manifest"][
            "coverage_without_overlap_or_omission"
        ],
        "bottleneck_classification": (
            "CPU_OR_PROCESS_OVERHEAD_DOMINANT_ON_SYNTHETIC_CORPUS"
            if wall and cpu / wall >= 0.75
            else "DISK_OR_WAIT_DOMINANT_ON_SYNTHETIC_CORPUS"
        ),
        "recommended_maintenance_worker_count": 1,
        "recommendation_boundary": (
            "Stage-1 worker count must be re-profiled on authorized metadata "
            "batches; this synthetic profile does not characterize archive IO."
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--files", type=int, default=512)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    payload = build_profile(args.files)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
