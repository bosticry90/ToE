from __future__ import annotations

"""Feasibility + design pre-gate for BRIDGE_TICKET_TOYG_0002 (Toy-G -> C6 mode index)."""

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
from pathlib import Path
from typing import Optional

import numpy as np

from formal.python.crft.cp_nlse_2d import Grid2D

SURFACE_PATH = "formal/python/crft/cp_nlse_2d.py"
PROGRAM_MISMATCH_PATH = "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json"


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


def _peak_mode_index_demo(*, n: int = 32, mode_index: int = 3) -> dict:
    L = float(2.0 * np.pi)
    grid = Grid2D.from_box(Nx=int(n), Ny=int(n), Lx=L, Ly=L)
    x = np.asarray(grid.x[:, 0], dtype=float)

    k = (2.0 * np.pi * float(mode_index)) / L
    psi = np.exp(1j * k * x)

    spec = np.fft.fft(psi)
    idx = int(np.argmax(np.abs(spec)))
    # Negative-frequency alias for wrapped positive bins.
    idx_signed = idx if idx <= (n // 2) else idx - n
    stable = bool(idx_signed == int(mode_index))
    return {
        "n": int(n),
        "mode_index_target": int(mode_index),
        "mode_index_peak": int(idx_signed),
        "stable": stable,
    }


def build_bridge_toyg_c6_mode_index_feasibility(*, repo_root: Path) -> dict:
    surface_abs = repo_root / SURFACE_PATH
    mismatch_abs = repo_root / PROGRAM_MISMATCH_PATH

    if not surface_abs.exists():
        return {
            "schema_version": 1,
            "bridge_id": "BRIDGE_TICKET_TOYG_0002",
            "mode": "design_only_preimplementation",
            "selected_target_reason_code": "fail_not_integer_close",
            "canonical_surface": {"path": SURFACE_PATH, "sha256": None},
            "program_mismatch_source": {"path": PROGRAM_MISMATCH_PATH, "sha256": None},
            "found": False,
            "checks": {},
            "prerequisite": f"Canonical surface not found: {SURFACE_PATH}",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_determinism.py::test_bridge_toyg_c6_mode_index_feasibility_is_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist.py::test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist",
                ]
            },
        }

    if not mismatch_abs.exists():
        return {
            "schema_version": 1,
            "bridge_id": "BRIDGE_TICKET_TOYG_0002",
            "mode": "design_only_preimplementation",
            "selected_target_reason_code": "fail_not_integer_close",
            "canonical_surface": {"path": SURFACE_PATH, "sha256": _sha256_path(surface_abs)},
            "program_mismatch_source": {"path": PROGRAM_MISMATCH_PATH, "sha256": None},
            "found": False,
            "checks": {},
            "prerequisite": f"Program mismatch artifact not found: {PROGRAM_MISMATCH_PATH}",
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_determinism.py::test_bridge_toyg_c6_mode_index_feasibility_is_deterministic",
                    "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist.py::test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist",
                ]
            },
        }

    text = surface_abs.read_text(encoding="utf-8", errors="ignore")
    has_grid_type = ("class Grid2D" in text) and ("class CPParams2D" in text)
    has_fft = ("np.fft" in text) or ("fft" in text)

    mismatch_payload = json.loads(mismatch_abs.read_text(encoding="utf-8"))
    reason_counts = dict(mismatch_payload.get("summary", {}).get("reason_code_counts", {}))
    source_summary = dict(mismatch_payload.get("source_report", {}).get("summary", {}))
    targeted_resolution = dict(source_summary.get("targeted_resolution", {}))
    resolved_by_mode_count = int(targeted_resolution.get("n_winding_not_integer_close_resolved_by_mode", 0))

    toyg_reason_counts: dict[str, int] = {}
    for it in mismatch_payload.get("items", []):
        channels = dict(it.get("channels", {}))
        toyg = dict(channels.get("toyg_winding", {}))
        if not bool(toyg.get("pass", True)):
            rc = str(toyg.get("reason_code", "UNKNOWN"))
            toyg_reason_counts[rc] = int(toyg_reason_counts.get(rc, 0)) + 1

    # Design choice (pinned): first eliminate the dominant "not integer close" region.
    selected = "fail_not_integer_close"
    selected_present = int(toyg_reason_counts.get(selected, 0)) > 0 or resolved_by_mode_count > 0

    mode_demo_1 = _peak_mode_index_demo(n=32, mode_index=3)
    mode_demo_2 = _peak_mode_index_demo(n=32, mode_index=3)
    mode_demo_stable = bool(mode_demo_1 == mode_demo_2 and bool(mode_demo_1["stable"]))

    found = bool(has_grid_type and has_fft and selected_present and mode_demo_stable)
    prerequisite = ""
    if not found:
        if not has_grid_type:
            prerequisite = "C6 surface lacks required typed grid/parameter structures."
        elif not has_fft:
            prerequisite = "C6 surface lacks deterministic FFT-capable tooling for mode-index proxy."
        elif not selected_present:
            prerequisite = (
                "Program mismatch report does not currently expose fail_not_integer_close for Toy-G channel and "
                "does not record a resolved-by-mode count; cannot target planned ambiguity region."
            )
        else:
            prerequisite = "Mode-index demo failed deterministic peak-index stability check."

    payload = {
        "schema_version": 1,
        "bridge_id": "BRIDGE_TICKET_TOYG_0002",
        "mode": "design_only_preimplementation",
        "targeted_mismatch_region": {
            "source_report": PROGRAM_MISMATCH_PATH,
            "reason_code_counts": reason_counts,
            "toyg_winding_reason_code_counts": toyg_reason_counts,
            "resolved_by_mode_count": int(resolved_by_mode_count),
        },
        "selected_target_reason_code": selected,
        "observable_plan": {
            "observable_id": "TOYG_C6_mode_index_quantization_v1",
            "definition": "dominant FFT mode-index on pinned periodic loop from C6 complex field specimen",
            "scope_limits": [
                "design_only",
                "no_bridge_implementation_in_this_ticket",
                "no_physics_claim",
            ],
        },
        "canonical_surface": {"path": SURFACE_PATH, "sha256": _sha256_path(surface_abs)},
        "program_mismatch_source": {"path": PROGRAM_MISMATCH_PATH, "sha256": _sha256_path(mismatch_abs)},
        "checks": {
            "has_grid_type": has_grid_type,
            "has_fft_tooling": has_fft,
            "selected_target_present": selected_present,
            "selected_target_resolved_by_mode_count": int(resolved_by_mode_count),
            "mode_index_demo": mode_demo_1,
            "mode_index_demo_deterministic": mode_demo_stable,
        },
        "orthogonality_expectation": {
            "expected_effect": (
                "reduce mismatch_toyg_winding_only mass attributable to fail_not_integer_close without collapsing "
                "program-level nonredundancy."
            ),
            "success_rule": (
                "program nonredundant remains true AND targeted mismatch region decreases under pinned probes."
            ),
        },
        "found": found,
        "prerequisite": prerequisite,
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_determinism.py::test_bridge_toyg_c6_mode_index_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist.py::test_bridge_toyg_c6_mode_index_feasibility_artifact_pointers_exist",
            ]
        },
    }
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Feasibility + design pre-gate for BRIDGE_TICKET_TOYG_0002.")
    parser.add_argument(
        "--out",
        default="formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/feasibility/BRIDGE_TOYG_C6_mode_index_feasibility.json)"
        ),
    )
    parser.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = parser.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyg_c6_mode_index_feasibility(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
