from __future__ import annotations

"""Deterministic v5 tolerance-tightening delta manifest for bridge-program frontier."""

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

from formal.python.tools.bridge_program_orthogonality_mismatch_report_generate import (
    build_bridge_program_orthogonality_mismatch_report,
)
from formal.python.tools.bridge_program_orthogonality_report_generate import (
    build_bridge_program_orthogonality_report,
)

_REASON_PRIORITY = {
    "mismatch_toyhg_pair_only": 0,
    "mismatch_toyh_phase_only": 1,
    "mismatch_toyh_current_only": 2,
    "mismatch_toyh_pair_only": 3,
    "mismatch_phase_and_pair": 4,
    "mismatch_current_and_pair": 5,
}

_TOLERANCE_FAILURE_REASON_CODES = {
    "FAIL_PHASE_INVARIANCE_TOL",
    "FAIL_CURRENT_INVARIANCE_TOL",
}


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_bytes(data: bytes) -> str:
    h = hashlib.sha256()
    h.update(data)
    return h.hexdigest()


def _ticket_for_reason(reason: str) -> str:
    if reason == "mismatch_toyhg_pair_only":
        return "BRIDGE_TICKET_TOYHG_0001"
    if reason == "mismatch_toyh_pair_only":
        return "BRIDGE_TICKET_TOYHG_0001"
    if reason in {"mismatch_phase_and_pair", "mismatch_current_and_pair"}:
        return "BRIDGE_TICKET_TOYHG_0001"
    if reason == "mismatch_toyg_bridge_only":
        return "BRIDGE_TICKET_TOYG_0003"
    if reason == "mismatch_toyh_phase_only":
        return "BRIDGE_TICKET_TOYH_0003"
    if reason == "mismatch_toyh_current_only":
        return "BRIDGE_TICKET_TOYH_0004"
    if reason == "none":
        return "BRIDGE_TICKET_PROGRAM_COMPLETE"
    return "BRIDGE_TICKET_PROGRAM_TBD"


def _recommended_next_target(reason_counts: dict[str, int]) -> dict:
    ranked = sorted(
        [(str(k), int(v)) for k, v in reason_counts.items()],
        key=lambda kv: (-int(kv[1]), int(_REASON_PRIORITY.get(str(kv[0]), 99)), str(kv[0])),
    )
    if not ranked:
        return {
            "reason_code": "none",
            "count": 0,
            "suggested_design_ticket": _ticket_for_reason("none"),
        }
    reason, count = ranked[0]
    return {
        "reason_code": str(reason),
        "count": int(count),
        "suggested_design_ticket": _ticket_for_reason(str(reason)),
    }


def _profile_snapshot(*, repo_root: Path, profile: str) -> dict:
    orth = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile=str(profile))
    mismatch = build_bridge_program_orthogonality_mismatch_report(repo_root=repo_root, tolerance_profile=str(profile))
    reason_counts = {
        str(k): int(v) for k, v in dict(mismatch.get("summary", {}).get("reason_code_counts", {})).items()
    }
    return {
        "profile": str(profile),
        "orthogonality_report": orth,
        "mismatch_report": mismatch,
        "snapshot": {
            "effective_tolerances_v5": dict(orth.get("shared_probe_set", {}).get("effective_tolerances_v5", {})),
            "n_probes": int(orth.get("summary", {}).get("n_probes", 0)),
            "signature_counts": dict(orth.get("summary", {}).get("signature_counts", {})),
            "n_mismatch": int(mismatch.get("summary", {}).get("n_mismatch", 0)),
            "reason_code_counts": {k: reason_counts[k] for k in sorted(reason_counts.keys())},
            "recommended_next_target": _recommended_next_target(reason_counts),
            "orthogonality_artifact_sha256": str(orth.get("artifact_sha256", "")),
            "mismatch_artifact_sha256": str(mismatch.get("artifact_sha256", "")),
        },
    }


def _tolerance_delta(*, from_tol: dict, to_tol: dict) -> dict:
    out: dict[str, dict] = {}
    for key in sorted(set(from_tol.keys()) | set(to_tol.keys())):
        a = float(from_tol.get(key, 0.0))
        b = float(to_tol.get(key, 0.0))
        out[str(key)] = {
            "from": float(a),
            "to": float(b),
            "ratio_to_from": float(b / a) if a != 0.0 else None,
        }
    return out


def _transition_summary(*, src_items: list[dict], dst_items: list[dict]) -> dict:
    dst_map = {str(it.get("probe_id")): it for it in dst_items}
    transitioned: list[dict] = []
    for src in src_items:
        probe_id = str(src.get("probe_id"))
        dst = dst_map.get(probe_id)
        if dst is None:
            continue
        src_sig = str(src.get("signature"))
        dst_sig = str(dst.get("signature"))
        if src_sig == dst_sig:
            continue
        transitioned.append(
            {
                "probe_id": probe_id,
                "from_signature": src_sig,
                "to_signature": dst_sig,
                "to_reason_codes": {
                    "toyh_phase": str(dst["toyh_phase"]["reason_code"]),
                    "toyh_phase_anchor": str(dst["toyh_phase_anchor"]["reason_code"]),
                    "toyh_current": str(dst["toyh_current"]["reason_code"]),
                    "toyh_current_anchor": str(dst["toyh_current_anchor"]["reason_code"]),
                },
            }
        )
    transitioned.sort(key=lambda it: str(it["probe_id"]))
    return {
        "n_signature_transitions": len(transitioned),
        "transitioned_probes": transitioned,
    }


def build_bridge_program_tolerance_tightening_delta_manifest(*, repo_root: Path) -> dict:
    baseline = _profile_snapshot(repo_root=repo_root, profile="baseline")
    t1 = _profile_snapshot(repo_root=repo_root, profile="v5_t1")
    t2 = _profile_snapshot(repo_root=repo_root, profile="v5_t2")

    baseline_items = list(baseline["orthogonality_report"].get("items", []))
    t1_items = list(t1["orthogonality_report"].get("items", []))
    t2_items = list(t2["orthogonality_report"].get("items", []))

    baseline_by_probe = {str(it.get("probe_id")): it for it in baseline_items}
    t2_by_probe = {str(it.get("probe_id")): it for it in t2_items}
    formerly_pass = [pid for pid, it in baseline_by_probe.items() if str(it.get("signature")) == "P-P-P"]
    flipped_from_pass = [pid for pid in formerly_pass if str(t2_by_probe[pid].get("signature")) != "P-P-P"]

    pinned_probe_id = "baseline_all_pass"
    pinned_baseline = baseline_by_probe[pinned_probe_id]
    pinned_t2 = t2_by_probe[pinned_probe_id]
    pinned_failure_reasons = sorted(
        {
            str(pinned_t2["toyh_phase"]["reason_code"]),
            str(pinned_t2["toyh_phase_anchor"]["reason_code"]),
            str(pinned_t2["toyh_current"]["reason_code"]),
            str(pinned_t2["toyh_current_anchor"]["reason_code"]),
        }
    )

    expected_break_passes = bool(
        str(pinned_baseline.get("signature")) == "P-P-P"
        and str(pinned_t2.get("signature")) != "P-P-P"
        and str(pinned_t2["toyh_phase"]["reason_code"]) in _TOLERANCE_FAILURE_REASON_CODES
        and str(pinned_t2["toyh_phase_anchor"]["reason_code"]) in _TOLERANCE_FAILURE_REASON_CODES
    )

    payload = {
        "schema_version": 1,
        "report_id": "BRIDGE_PROGRAM_TOLERANCE_TIGHTENING_DELTA_MANIFEST",
        "profiles": {
            "baseline": dict(baseline["snapshot"]),
            "v5_t1": dict(t1["snapshot"]),
            "v5_t2": dict(t2["snapshot"]),
        },
        "tightening_delta": {
            "baseline_to_v5_t1": _tolerance_delta(
                from_tol=baseline["snapshot"]["effective_tolerances_v5"],
                to_tol=t1["snapshot"]["effective_tolerances_v5"],
            ),
            "v5_t1_to_v5_t2": _tolerance_delta(
                from_tol=t1["snapshot"]["effective_tolerances_v5"],
                to_tol=t2["snapshot"]["effective_tolerances_v5"],
            ),
            "baseline_to_v5_t2": _tolerance_delta(
                from_tol=baseline["snapshot"]["effective_tolerances_v5"],
                to_tol=t2["snapshot"]["effective_tolerances_v5"],
            ),
        },
        "signature_transitions": {
            "baseline_to_v5_t1": _transition_summary(src_items=baseline_items, dst_items=t1_items),
            "v5_t1_to_v5_t2": _transition_summary(src_items=t1_items, dst_items=t2_items),
            "baseline_to_v5_t2": _transition_summary(src_items=baseline_items, dst_items=t2_items),
        },
        "expected_break_controls": {
            "v5_t1_closure_expected": {
                "n_mismatch": int(t1["snapshot"]["n_mismatch"]),
                "reason_code_counts": dict(t1["snapshot"]["reason_code_counts"]),
                "recommended_next_target": dict(t1["snapshot"]["recommended_next_target"]),
                "passes": bool(
                    int(t1["snapshot"]["n_mismatch"]) == 0
                    and dict(t1["snapshot"]["reason_code_counts"]) == {}
                    and str(t1["snapshot"]["recommended_next_target"]["reason_code"]) == "none"
                ),
            },
            "v5_t2_expected_break": {
                "pinned_probe_id": pinned_probe_id,
                "baseline_signature": str(pinned_baseline.get("signature")),
                "v5_t2_signature": str(pinned_t2.get("signature")),
                "v5_t2_reason_codes": pinned_failure_reasons,
                "allowed_tolerance_failure_reason_codes": sorted(_TOLERANCE_FAILURE_REASON_CODES),
                "n_formerly_pass_probes_flipped": int(len(flipped_from_pass)),
                "flipped_probe_ids": sorted(flipped_from_pass),
                "passes": bool(expected_break_passes and len(flipped_from_pass) >= 1),
            },
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_program_tolerance_tightening_delta_manifest_generate_determinism.py::test_bridge_program_tolerance_tightening_delta_manifest_is_deterministic",
                "formal/python/tests/test_bridge_program_tolerance_tightening_delta_manifest_semantics.py::test_bridge_program_tolerance_tightening_delta_manifest_v5_t1_closure",
                "formal/python/tests/test_bridge_program_tolerance_tightening_delta_manifest_semantics.py::test_bridge_program_tolerance_tightening_delta_manifest_v5_t2_expected_break",
            ]
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate deterministic bridge-program v5 tolerance tightening delta manifest.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_TOLERANCE_TIGHTENING_DELTA_MANIFEST.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_TOLERANCE_TIGHTENING_DELTA_MANIFEST.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))
    payload = build_bridge_program_tolerance_tightening_delta_manifest(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
