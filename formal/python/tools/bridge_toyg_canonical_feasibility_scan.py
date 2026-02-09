from __future__ import annotations

"""Toy-G -> canonical feasibility scan (quarantine-safe).

Goal
- Determine whether canonical, non-archive surfaces can supply typed,
  deterministic inputs needed to compute Toy-G topological observables.
- Gate ticket creation: feasibility first, tickets later.
"""

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
import re
from pathlib import Path
from typing import Optional


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_bytes(data: bytes) -> str:
    h = hashlib.sha256()
    h.update(data)
    return h.hexdigest()


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="ignore")


def _has_any(text: str, patterns: list[str]) -> bool:
    return any(re.search(pat, text, flags=re.IGNORECASE) is not None for pat in patterns)


def _target_specs() -> list[dict]:
    return [
        {
            "target_id": "C6",
            "label": "CRFT CP-NLSE 2D",
            "surface_path": "formal/python/crft/cp_nlse_2d.py",
            "typed_patterns": [r"\bclass\s+Grid2D\b", r"\bclass\s+CPParams2D\b"],
            "grid_patterns": [r"\bGrid2D\b", r"\bmeshgrid\b", r"\bdx\b", r"\bdy\b"],
            "phase_patterns": [r"complex", r"np\.complex", r"\bgrad2_2d\b", r"\blaplacian_2d\b"],
            "determinism_patterns": [r"\bfrom_box\b", r"\brhs_cp_nlse_2d\b"],
        },
        {
            "target_id": "C7",
            "label": "CRFT acoustic metric (MT-01a)",
            "surface_path": "formal/python/crft/acoustic_metric.py",
            "typed_patterns": [r"\b@dataclass\b", r"\bAcousticMetric1D\b", r"\bAcousticMetric2D\b"],
            "grid_patterns": [r"\bGrid2D\b", r"\bmeshgrid\b"],
            "phase_patterns": [r"complex", r"np\.complex", r"\bphase\b"],
            "determinism_patterns": [r"\bcompute_acoustic_metric_1d\b", r"\bcompute_acoustic_metric_2d\b"],
        },
        {
            "target_id": "UCFF",
            "label": "UCFF core front door",
            "surface_path": "formal/python/toe/ucff/core_front_door.py",
            "typed_patterns": [r"\b@dataclass\b", r"\bUcffCoreInput\b", r"\bUcffCoreReport\b"],
            "grid_patterns": [r"\bGrid2D\b", r"\bmeshgrid\b", r"\bspatial\b"],
            "phase_patterns": [r"\bphase\b", r"complex", r"np\.complex"],
            "determinism_patterns": [r"\bsort_keys=True\b", r"\bdumps_ucff_core_report\b"],
        },
    ]


def _evaluate_target(repo_root: Path, spec: dict) -> dict:
    surface_rel = str(spec["surface_path"])
    surface_abs = repo_root / surface_rel

    if not surface_abs.exists():
        return {
            "target_id": str(spec["target_id"]),
            "label": str(spec["label"]),
            "found": False,
            "canonical_surface": {"path": surface_rel, "sha256": None},
            "capabilities": {
                "typed_input_output": False,
                "spatial_grid_surface": False,
                "phase_like_observable_surface": False,
                "deterministic_front_door_behavior": False,
            },
            "reason_code": "MISSING_CANONICAL_SURFACE",
            "prerequisite": f"Canonical non-archive surface not found: {surface_rel}",
        }

    text = _read_text(surface_abs)

    typed_io = _has_any(text, list(spec["typed_patterns"]))
    has_grid = _has_any(text, list(spec["grid_patterns"]))
    has_phase = _has_any(text, list(spec["phase_patterns"]))
    deterministic = _has_any(text, list(spec["determinism_patterns"]))

    found = bool(typed_io and has_grid and has_phase and deterministic)

    if found:
        reason_code = "FOUND_MINIMAL_TOYG_COMPATIBLE_SURFACE"
        prerequisite = ""
    elif not has_grid:
        reason_code = "BLOCKED_NO_SPATIAL_GRID_SURFACE"
        prerequisite = (
            "Surface lacks explicit spatial-grid field support required for Toy-G invariant probes "
            "(need typed grid/field front-door inputs)."
        )
    elif not has_phase:
        reason_code = "BLOCKED_NO_PHASE_LIKE_OBSERVABLE"
        prerequisite = (
            "Surface lacks phase-like/complex-field observables required for Toy-G winding/defect-style proxies."
        )
    elif not typed_io:
        reason_code = "BLOCKED_NO_TYPED_INPUT_OUTPUT"
        prerequisite = "Surface lacks explicit typed input/output front-door contract for deterministic Toy-G probes."
    else:
        reason_code = "BLOCKED_NONDETERMINISTIC_SURFACE"
        prerequisite = "Surface lacks deterministic front-door behavior needed for pinned Toy-G feasibility gating."

    return {
        "target_id": str(spec["target_id"]),
        "label": str(spec["label"]),
        "found": found,
        "canonical_surface": {"path": surface_rel, "sha256": _sha256_path(surface_abs)},
        "capabilities": {
            "typed_input_output": typed_io,
            "spatial_grid_surface": has_grid,
            "phase_like_observable_surface": has_phase,
            "deterministic_front_door_behavior": deterministic,
        },
        "reason_code": reason_code,
        "prerequisite": prerequisite,
    }


def scan_bridge_toyg_canonical_feasibility(*, repo_root: Path) -> dict:
    targets = [_evaluate_target(repo_root, s) for s in _target_specs()]
    found_targets = [t["target_id"] for t in targets if bool(t.get("found"))]
    blocked_targets = [t["target_id"] for t in targets if not bool(t.get("found"))]
    found = len(found_targets) > 0

    prerequisite = ""
    if not found:
        prerequisite = (
            "No canonical non-archive surface satisfies Toy-G feasibility requirements. "
            "Prerequisite: introduce a typed, deterministic canonical front door that exposes "
            "a phase-like field on a spatial grid for topological invariant probes."
        )

    payload = {
        "schema_version": 1,
        "bridge_family": "BRIDGE_TOYG_CANONICAL_FEASIBILITY",
        "toy_family": "TOY-G",
        "targets_scanned": [t["target_id"] for t in targets],
        "found": found,
        "found_targets": found_targets,
        "blocked_targets": blocked_targets,
        "targets": targets,
        "prerequisite": prerequisite,
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyg_canonical_feasibility_scan_determinism.py::test_bridge_toyg_canonical_feasibility_scan_is_deterministic",
                "formal/python/tests/test_bridge_toyg_canonical_feasibility_artifact_pointers_exist.py::test_bridge_toyg_canonical_feasibility_artifact_pointers_exist",
            ]
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Deterministic feasibility scan for Toy-G -> canonical bridge lane.")
    parser.add_argument(
        "--out",
        default="formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/feasibility/BRIDGE_TOYG_CANONICAL_feasibility.json)"
        ),
    )
    parser.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = parser.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = scan_bridge_toyg_canonical_feasibility(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
