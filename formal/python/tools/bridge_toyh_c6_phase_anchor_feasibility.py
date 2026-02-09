from __future__ import annotations

"""Feasibility + design pre-gate for BRIDGE_TICKET_TOYH_0003 (Toy-H phase-anchor)."""

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


SURFACE_PATH = "formal/python/crft/cp_nlse_2d.py"
ORTHOGONALITY_REPORT_PATH = "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json"
MISMATCH_REPORT_PATH = "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json"
MISMATCH_SUMMARY_PATH = "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json"


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


def build_bridge_toyh_c6_phase_anchor_feasibility(*, repo_root: Path) -> dict:
    selected_target = "mismatch_toyh_phase_only"
    primary_probe = "stress_toyh_phase_control"
    secondary_probe = "baseline_all_pass"

    surface_abs = repo_root / SURFACE_PATH
    orth_abs = repo_root / ORTHOGONALITY_REPORT_PATH
    mismatch_abs = repo_root / MISMATCH_REPORT_PATH
    summary_abs = repo_root / MISMATCH_SUMMARY_PATH

    block_reasons: list[str] = []

    if not surface_abs.exists():
        block_reasons.append(f"Canonical surface not found: {SURFACE_PATH}")
    if not orth_abs.exists():
        block_reasons.append(f"Program orthogonality report not found: {ORTHOGONALITY_REPORT_PATH}")
    if not mismatch_abs.exists():
        block_reasons.append(f"Program mismatch report not found: {MISMATCH_REPORT_PATH}")
    if not summary_abs.exists():
        block_reasons.append(f"Program mismatch summary not found: {MISMATCH_SUMMARY_PATH}")

    if block_reasons:
        return {
            "schema_version": 1,
            "bridge_id": "BRIDGE_TICKET_TOYH_0003",
            "mode": "design_only_preimplementation",
            "selected_target_reason_code": selected_target,
            "implementable": False,
            "found": False,
            "block_reasons": block_reasons,
            "canonical_surface": {"path": SURFACE_PATH, "sha256": _sha256_path(surface_abs) if surface_abs.exists() else None},
            "source_artifacts": {
                "orthogonality_report": {"path": ORTHOGONALITY_REPORT_PATH, "sha256": _sha256_path(orth_abs) if orth_abs.exists() else None},
                "mismatch_report": {"path": MISMATCH_REPORT_PATH, "sha256": _sha256_path(mismatch_abs) if mismatch_abs.exists() else None},
                "mismatch_summary": {"path": MISMATCH_SUMMARY_PATH, "sha256": _sha256_path(summary_abs) if summary_abs.exists() else None},
            },
            "checks": {},
            "evidence": {
                "pytest_nodes": [
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_determinism.py::test_bridge_toyh_c6_phase_anchor_feasibility_is_deterministic",
                    "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_pointers_exist.py::test_bridge_toyh_c6_phase_anchor_feasibility_artifact_pointers_exist",
                ]
            },
        }

    surface_text = surface_abs.read_text(encoding="utf-8", errors="ignore")
    has_grid_type = ("class Grid2D" in surface_text) and ("class CPParams2D" in surface_text)
    has_rhs = "rhs_cp_nlse_2d" in surface_text

    orth_payload = json.loads(orth_abs.read_text(encoding="utf-8"))
    mismatch_payload = json.loads(mismatch_abs.read_text(encoding="utf-8"))
    summary_payload = json.loads(summary_abs.read_text(encoding="utf-8"))

    reason_counts = {
        str(k): int(v)
        for k, v in dict(summary_payload.get("summary", {}).get("reason_code_counts", {})).items()
    }
    orth_summary = dict(orth_payload.get("summary", {}))
    targeted_resolution = dict(orth_summary.get("targeted_resolution", {}))
    resolved_by_phase_anchor_count = int(targeted_resolution.get("n_phase_control_fail_resolved_by_phase_anchor", 0))
    target_reason_count = int(reason_counts.get(selected_target, 0))

    mismatch_items = [dict(it) for it in mismatch_payload.get("items", [])]
    target_items = [it for it in mismatch_items if str(it.get("reason_code")) == selected_target]
    target_probe_ids = sorted({str(it.get("probe_id")) for it in target_items})
    selected_present = bool(target_reason_count > 0 or resolved_by_phase_anchor_count > 0)

    has_primary_probe = primary_probe in target_probe_ids

    def _phase_reason(it: dict) -> str:
        channels = dict(it.get("channels", {}))
        phase = dict(channels.get("toyh_phase", {}))
        return str(phase.get("reason_code", ""))

    target_has_phase_control_fail = any(_phase_reason(it) == "FAIL_PHASE_CHANNEL_CONTROL_MIN" for it in target_items)

    orth_items = [dict(it) for it in orth_payload.get("items", [])]
    orth_probe_ids = {str(it.get("probe_id")) for it in orth_items}
    has_secondary_probe = secondary_probe in orth_probe_ids
    orth_primary = next((it for it in orth_items if str(it.get("probe_id")) == primary_probe), None)

    # Post-resolution fallback: targeted mismatch can disappear after implementation.
    if (not has_primary_probe) and (orth_primary is not None) and selected_present:
        target_probe_ids = [primary_probe]
        has_primary_probe = True
        target_has_phase_control_fail = (
            str(dict(orth_primary.get("toyh_phase", {})).get("reason_code", "")) == "FAIL_PHASE_CHANNEL_CONTROL_MIN"
        )

    shared_probe_set = dict(orth_payload.get("shared_probe_set", {}))
    grid_sizes = list(shared_probe_set.get("grid_sizes", []))
    toyh_tol = shared_probe_set.get("toyh_tolerance")
    phase_control_min = shared_probe_set.get("phase_channel_control_min")

    has_pinned_grid = list(grid_sizes) == [7, 9, 11]
    has_tolerance_bundle = (
        toyh_tol is not None
        and phase_control_min is not None
    )

    if not has_grid_type:
        block_reasons.append("C6 surface lacks required typed grid/parameter structures.")
    if not has_rhs:
        block_reasons.append("C6 surface lacks deterministic RHS evaluator required for phase-anchor invariance checks.")
    if not selected_present:
        block_reasons.append(
            "Selected target region mismatch_toyh_phase_only is absent from mismatch summary and has no resolved-by-anchor count."
        )
    if not has_primary_probe:
        block_reasons.append("Primary targeted probe stress_toyh_phase_control is absent from selected mismatch region.")
    if not target_has_phase_control_fail:
        block_reasons.append("Selected mismatch region does not contain FAIL_PHASE_CHANNEL_CONTROL_MIN on Toy-H phase channel.")
    if not has_secondary_probe:
        block_reasons.append("Secondary comparison probe baseline_all_pass is absent from orthogonality report.")
    if not has_pinned_grid:
        block_reasons.append("Pinned resolution set [7,9,11] not found in shared probe set.")
    if not has_tolerance_bundle:
        block_reasons.append("Pinned tolerance bundle (toyh_tolerance, phase_channel_control_min) is incomplete.")

    implementable = len(block_reasons) == 0

    payload = {
        "schema_version": 1,
        "bridge_id": "BRIDGE_TICKET_TOYH_0003",
        "mode": "design_only_preimplementation",
        "selected_target_reason_code": selected_target,
        "target_region": {
            "reason_code": selected_target,
            "reason_code_counts": reason_counts,
            "count": int(target_reason_count),
            "resolved_by_phase_anchor_count": int(resolved_by_phase_anchor_count),
            "probe_ids": target_probe_ids,
        },
        "pinned_plan": {
            "primary_probe_ids": [primary_probe],
            "secondary_probe_ids": [secondary_probe],
            "grid_sizes": [7, 9, 11],
            "theta_values": [1e-6, 1.0471975511965976],
            "amplitude_scales": {"admissible": [1.0], "inadmissible": [1.1]},
            "tolerances": {
                "toyh_tolerance": float(toyh_tol) if toyh_tol is not None else None,
                "phase_channel_control_min": float(phase_control_min) if phase_control_min is not None else None,
                "phase_anchor_tolerance": 1e-7,
            },
        },
        "canonical_surface": {"path": SURFACE_PATH, "sha256": _sha256_path(surface_abs)},
        "source_artifacts": {
            "orthogonality_report": {"path": ORTHOGONALITY_REPORT_PATH, "sha256": _sha256_path(orth_abs)},
            "mismatch_report": {"path": MISMATCH_REPORT_PATH, "sha256": _sha256_path(mismatch_abs)},
            "mismatch_summary": {"path": MISMATCH_SUMMARY_PATH, "sha256": _sha256_path(summary_abs)},
        },
        "checks": {
            "has_grid_type": has_grid_type,
            "has_rhs_tooling": has_rhs,
            "selected_target_present": bool(selected_present),
            "target_reason_count": int(target_reason_count),
            "selected_target_resolved_by_phase_anchor_count": int(resolved_by_phase_anchor_count),
            "primary_probe_present": has_primary_probe,
            "target_has_phase_control_fail_reason": target_has_phase_control_fail,
            "secondary_probe_present": has_secondary_probe,
            "has_pinned_resolution_set": has_pinned_grid,
            "has_pinned_tolerance_bundle": has_tolerance_bundle,
        },
        "implementable": bool(implementable),
        "found": bool(implementable),
        "block_reasons": block_reasons,
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_determinism.py::test_bridge_toyh_c6_phase_anchor_feasibility_is_deterministic",
                "formal/python/tests/test_bridge_toyh_c6_phase_anchor_feasibility_pointers_exist.py::test_bridge_toyh_c6_phase_anchor_feasibility_artifact_pointers_exist",
            ]
        },
    }
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Feasibility + design pre-gate for BRIDGE_TICKET_TOYH_0003.")
    parser.add_argument(
        "--out",
        default="formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_anchor_feasibility.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/feasibility/BRIDGE_TOYH_C6_phase_anchor_feasibility.json)"
        ),
    )
    parser.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = parser.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyh_c6_phase_anchor_feasibility(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
