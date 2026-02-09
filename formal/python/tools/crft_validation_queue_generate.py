from __future__ import annotations

"""CRFT validation queue generator (quarantine-safe).

Goal
- Convert a CRFT claims-extraction artifact (with a deterministic validation_shortlist)
  into a bounded, reviewable validation queue artifact.

Policy alignment
- Read-only: reads a JSON artifact (typically under formal/quarantine/claims).
- Does not import from the archive directory.
- Output is bookkeeping only (no status upgrades).

Output schema (v3)
{
        "schema_version": 3,
  "source": {"path": "...", "sha256": "..."},
  "items": [
    {
      "claim_id": "CLM-0051",
      "section": "C6 — ...",
      "kind": "equation",
      "text": "...",
      "target_surface": "formal/python/...",
            "claim_family": "C6_CP_NLSE_2D",
            "evidence_strength": "bounded_multi",
            "evidence": {
                "pytest_nodes": ["path/to/test_file.py::test_fn"],
                "canonical_surface_refs": ["CP-NLSE-2D"]
            },
      "tasks": ["..."],
      "exit_condition": "...",
      "status": "pending"
    }
  ]
}
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
from pathlib import Path
from typing import Dict, List, Optional


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


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _read_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8"))


def _evidence_for_ticket(target_surface: str) -> dict:
    """Deterministic evidence mapping.

    IMPORTANT: This is intentionally static (no runtime discovery).
    If you add a new validation ticket, extend this mapping explicitly.
    """

    target_surface = str(target_surface)

    if target_surface.endswith("formal/python/crft/cp_nlse_2d.py"):
        return {
            "pytest_nodes": [
                "formal/python/crft/tests/test_c6_cp_nlse_2d_norm_drift.py::test_c6_cp_nlse_2d_norm_drift_is_small_for_plane_wave",
                "formal/python/crft/tests/test_c6_cp_nlse_2d_dispersion_eigenfunction.py::test_c6_cp_nlse_2d_plane_wave_is_rhs_eigenfunction_when_linear",
            ],
            "canonical_surface_refs": ["CP-NLSE-2D"],
        }

    if target_surface.endswith("formal/python/crft/acoustic_metric.py"):
        return {
            "pytest_nodes": [
                "formal/python/tests/test_c7_acoustic_metric_inequalities.py::test_c7_acoustic_metric_1d_has_timelike_gtt_and_negative_det_when_subsonic",
                "formal/python/tests/test_c7_acoustic_metric_inequalities.py::test_c7_acoustic_metric_2d_has_timelike_gtt_and_negative_det_when_subsonic",
                "formal/python/tests/test_c7_acoustic_metric_perturbation_stability.py::test_c7_acoustic_metric_sign_invariants_stable_under_small_perturbations_2d",
                "formal/python/tests/test_mt01_acoustic_metric_lock.py::test_mt01_acoustic_metric_1d_lock_identities",
                "formal/python/tests/test_mt01_acoustic_metric_lock.py::test_mt01_acoustic_metric_2d_lock_identities_and_det_reduction",
            ],
            "canonical_surface_refs": ["MT-01a"],
        }

    return {"pytest_nodes": [], "canonical_surface_refs": []}


def _claim_family_for_ticket(target_surface: str) -> str:
    target_surface = str(target_surface)
    if target_surface.endswith("formal/python/crft/cp_nlse_2d.py"):
        return "C6_CP_NLSE_2D"
    if target_surface.endswith("formal/python/crft/acoustic_metric.py"):
        return "C7_MT_01A"
    return "UNKNOWN"


def _evidence_strength_for_ticket(target_surface: str) -> str:
    # Deterministic policy:
    # - C6 tickets are "bounded_multi" because we require multiple complementary bounded checks.
    # - C7 tickets are "bounded_multi" because we require independent bounded invariants against MT-01a.
    target_surface = str(target_surface)
    if target_surface.endswith("formal/python/crft/cp_nlse_2d.py"):
        return "bounded_multi"
    if target_surface.endswith("formal/python/crft/acoustic_metric.py"):
        return "bounded_multi"
    return "bounded_single"


def build_queue_payload(claims_payload: dict, source_path: str, source_sha256: str, max_items: int) -> dict:
    claims_by_id: Dict[str, dict] = {c["id"]: c for c in claims_payload.get("claims", [])}

    shortlist = list(claims_payload.get("validation_shortlist", []))

    items: List[dict] = []
    for entry in shortlist:
        claim_id = str(entry.get("claim_id"))
        claim = claims_by_id.get(claim_id)
        if claim is None:
            # Preserve determinism: include a placeholder row rather than dropping.
            items.append(
                {
                    "claim_id": claim_id,
                    "section": "(missing)",
                    "kind": "(missing)",
                    "text": "(claim id not present in claims list)",
                    "target_surface": str(entry.get("target_surface", "")),
                    "tasks": list(entry.get("plan", [])),
                    "exit_condition": str(entry.get("exit_condition", "")),
                    "status": "blocked_missing_claim",
                }
            )
            continue

        items.append(
            {
                "claim_id": claim_id,
                "section": str(claim.get("section", "")),
                "kind": str(claim.get("kind", "")),
                "text": str(claim.get("text", "")),
                "target_surface": str(entry.get("target_surface", "")),
                "claim_family": _claim_family_for_ticket(str(entry.get("target_surface", ""))),
                "evidence_strength": _evidence_strength_for_ticket(str(entry.get("target_surface", ""))),
                "evidence": _evidence_for_ticket(str(entry.get("target_surface", ""))),
                "tasks": list(entry.get("plan", [])),
                "exit_condition": str(entry.get("exit_condition", "")),
                "status": "pending",
            }
        )

    # Bound the queue deterministically (preserve shortlist order).
    items = items[: int(max_items)]

    return {
        "schema_version": 3,
        "source": {"path": source_path, "sha256": source_sha256},
        "items": items,
    }


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Generate a bounded CRFT validation queue from a claims-extract JSON.")
    parser.add_argument(
        "--claims",
        required=True,
        help="Repo-relative path to claims extract JSON (recommended under formal/quarantine/claims).",
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Repo-relative output JSON path (recommended under formal/quarantine/validation).",
    )
    parser.add_argument(
        "--max-items",
        type=int,
        default=3,
        help="Maximum number of validation items to emit (default: 3).",
    )

    args = parser.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    claims_path = repo_root / args.claims
    if not claims_path.exists():
        raise SystemExit(f"Claims JSON not found: {args.claims}")

    payload = _read_json(claims_path)

    def rel(p: Path) -> str:
        try:
            return p.resolve().relative_to(repo_root.resolve()).as_posix()
        except Exception:
            return p.as_posix()

    out_payload = build_queue_payload(
        claims_payload=payload,
        source_path=rel(claims_path),
        source_sha256=_sha256_path(claims_path),
        max_items=args.max_items,
    )

    # Ensure deterministic formatting.
    out_text = json.dumps(out_payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    # Self-hash is useful for debugging/review but must not introduce nondeterminism.
    out_payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    out_text = json.dumps(out_payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    out_path = repo_root / args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(out_text, encoding="utf-8")

    print(str(Path(args.out).as_posix()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
