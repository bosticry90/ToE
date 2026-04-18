from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
BASELINE_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "recompute_baseline_snapshot_20260418_v0.json"
AUTHORITY_PROMOTION_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json"
PACKET_CHAIN_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json"

SURFACE_SPECS: dict[str, dict[str, str]] = {
    "qm_seam_coherence": {
        "schema_id": "QM_SEAM_COHERENCE_UNDER_REVISED_BLOCKER",
        "path": "formal/output/recompute/qm_seam_coherence_under_revised_blocker.json",
    },
    "ledger_artifact_transport": {
        "schema_id": "LEDGER_ARTIFACT_TRANSPORT_UNDER_REVISED_BLOCKER",
        "path": "formal/output/recompute/ledger_artifact_transport_under_revised_blocker.json",
    },
    "blocker_authority_transport": {
        "schema_id": "BLOCKER_AUTHORITY_TRANSPORT_SURFACE",
        "path": "formal/output/recompute/blocker_authority_transport_surface.json",
    },
}


def utc_now(value: str | None = None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def resolve_root(root: Path | None = None) -> Path:
    return REPO_ROOT if root is None else Path(root)


def surface_path(surface_id: str, *, root: Path | None = None) -> Path:
    try:
        rel_path = SURFACE_SPECS[surface_id]["path"]
    except KeyError as exc:
        raise KeyError(f"Unknown recompute surface: {surface_id}") from exc
    return resolve_root(root) / rel_path


def ensure_surface_document(surface_id: str, *, root: Path | None = None) -> dict[str, Any]:
    path = surface_path(surface_id, root=root)
    if path.exists():
        payload = read_json(path)
        payload.setdefault("triggers", [])
        return payload
    payload = {
        "schema_id": SURFACE_SPECS[surface_id]["schema_id"],
        "triggers": [],
    }
    write_json(path, payload)
    return payload


def clone_recompute_surfaces(*, destination_root: Path, source_root: Path | None = None) -> list[str]:
    source_base = resolve_root(source_root)
    destination_base = resolve_root(destination_root)
    copied_paths: list[str] = []
    for surface_id in SURFACE_SPECS:
        source_path = surface_path(surface_id, root=source_base)
        destination_path = surface_path(surface_id, root=destination_base)
        payload = read_json(source_path) if source_path.exists() else ensure_surface_document(surface_id, root=source_base)
        write_json(destination_path, payload)
        copied_paths.append(str(destination_path.relative_to(destination_base)).replace("\\", "/"))
    return copied_paths


def latest_trigger(
    document: dict[str, Any],
    *,
    status: str | None = None,
    trigger_id: str | None = None,
) -> dict[str, Any] | None:
    for trigger in reversed(list(document.get("triggers", []))):
        if trigger_id and trigger.get("trigger_id") != trigger_id:
            continue
        if status and trigger.get("status") != status:
            continue
        return trigger
    return None


def deterministic_fraction(*parts: str) -> float:
    seed = "::".join(parts).encode("utf-8")
    digest = hashlib.sha256(seed).hexdigest()
    numerator = int(digest[:12], 16)
    denominator = float(16 ** 12 - 1)
    return numerator / denominator if denominator else 0.0


def quantize(value: float, digits: int = 6) -> float:
    return round(float(value), digits)


def mark_trigger_completed(trigger: dict[str, Any], *, completed_at_utc: str, note: str) -> None:
    trigger["status"] = "COMPLETED"
    trigger["completed_at_utc"] = completed_at_utc
    trigger["completion_note"] = note


def refresh_surface_metadata(
    document: dict[str, Any],
    *,
    surface_id: str,
    trigger_id: str,
    captured_at_utc: str,
) -> None:
    document["schema_id"] = SURFACE_SPECS[surface_id]["schema_id"]
    document["last_completed_trigger_id"] = trigger_id
    document["captured_at_utc"] = captured_at_utc
    document["status"] = "ACTIVE_NONLIVE_NONCLAIM"
