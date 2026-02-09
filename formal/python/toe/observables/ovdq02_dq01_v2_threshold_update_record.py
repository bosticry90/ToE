"""OV-DQ-02: DQ-01_v2 threshold-update policy lock (computed).

Purpose
- Lock a narrowly-scoped, auditable policy evolution statement:
  DQ-01_v2 uses q_threshold=1.05 (vs 0.90 in DQ-01_v1) for the OV-01g family
  selection rule.
- Cite the pinned diagnostic evidence (OV-DQ-01 policy sensitivity artifact) and
  record the observed impact set in the currently evaluated suite.

Scope / limits
- Bookkeeping / narrative only; no physics claim.
- Does not mutate any canonical selection; it documents a proposed / parallel
  policy definition.

Design constraints
- Deterministic (no RNG, no network).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovdq01_policy_sensitivity_record import default_artifact_path


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _row_at(grid: list[dict[str, Any]], t: float) -> dict[str, Any]:
    for r in list(grid):
        if abs(float(r["q_threshold"]) - float(t)) <= 1e-12:
            return dict(r)
    raise ValueError(f"Missing row at q_threshold={t}")


@dataclass(frozen=True)
class OVDQ02DQ01v2ThresholdUpdateRecord:
    schema: str
    date: str

    from_policy: str
    to_policy: str
    q_threshold_from: float
    q_threshold_to: float

    delta: dict[str, Any]

    evidence_artifact_relpath: str
    evidence_artifact_fingerprint: str

    impact_set: tuple[str, ...]
    per_observable: dict[str, Any]

    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "from_policy": str(self.from_policy),
            "to_policy": str(self.to_policy),
            "q_threshold_from": float(self.q_threshold_from),
            "q_threshold_to": float(self.q_threshold_to),
            "delta": dict(self.delta),
            "evidence_artifact_relpath": str(self.evidence_artifact_relpath),
            "evidence_artifact_fingerprint": str(self.evidence_artifact_fingerprint),
            "impact_set": list(self.impact_set),
            "per_observable": dict(self.per_observable),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovdq02_dq01_v2_threshold_update_record(
    *,
    date: str = "2026-01-23",
    q_threshold_from: float = 0.90,
    q_threshold_to: float = 1.05,
) -> OVDQ02DQ01v2ThresholdUpdateRecord:
    repo_root = _find_repo_root(Path(__file__))

    artifact_path = default_artifact_path()
    artifact = _load_json(artifact_path)

    if str(artifact.get("schema")) != "OV-DQ-01_policy_sensitivity/v2":
        raise ValueError("Expected OV-DQ-01 policy sensitivity schema v2")

    obs_keys = {
        "OV-01g": "ov01g",
        "OV-02x": "ov02x",
        "OV-03x": "ov03x",
        "OV-04x": "ov04x",
    }

    per_obs: dict[str, Any] = {}
    impact: list[str] = []

    for obs_id, key in obs_keys.items():
        section = dict(artifact[key])
        grid = list(section["grid"])

        r_from = _row_at(grid, float(q_threshold_from))
        r_to = _row_at(grid, float(q_threshold_to))

        # Normalize the comparable "robustness_failed" signal across types.
        if obs_id == "OV-02x":
            failed_from = bool(r_from["robustness_failed"])
            failed_to = bool(r_to["robustness_failed"])
            prefer_from = bool(r_from["baseline_prefer_curved"])
            prefer_to = bool(r_to["baseline_prefer_curved"])
        else:
            failed_from = bool(r_from["robustness_failed"])
            failed_to = bool(r_to["robustness_failed"])
            prefer_from = bool(r_from["would_prefer_curved"])
            prefer_to = bool(r_to["would_prefer_curved"])

        changed = (failed_from != failed_to) or (prefer_from != prefer_to)
        if changed:
            impact.append(obs_id)

        per_obs[obs_id] = {
            "row_q_threshold_from": float(q_threshold_from),
            "row_q_threshold_to": float(q_threshold_to),
            "row_from": r_from,
            "row_to": r_to,
            "changed": bool(changed),
        }

    impact_set = tuple(sorted(set(impact)))

    delta = {
        "changed_fields": ["q_threshold"],
        "q_threshold_from": float(q_threshold_from),
        "q_threshold_to": float(q_threshold_to),
        "note": "Threshold-only delta at the OV-01g family-selection gate layer; curved-fit adequacy policy is unchanged in this proposal.",
    }

    narrative = (
        "DQ-01_v2 threshold update (diagnostic evidence-based; no physics claim):\n"
        f"- Delta: q_threshold {float(q_threshold_from):.12g} -> {float(q_threshold_to):.12g} only (selection gate clause).\n"
        f"- Evidence: {artifact_path.as_posix()} (fingerprint={str(artifact.get('fingerprint'))}).\n"
        f"- Observed impact set in evaluated suite: {list(impact_set)}.\n"
        "- Scope statement: within OV-01g/OV-02x/OV-03x/OV-04x as evaluated, only OV-03x changes; others are unchanged."
    )

    rel = artifact_path.resolve().relative_to(repo_root.resolve()).as_posix()

    return OVDQ02DQ01v2ThresholdUpdateRecord(
        schema="OV-DQ-02_dq01_v2_threshold_update/v1",
        date=str(date),
        from_policy="DQ-01_v1",
        to_policy="DQ-01_v2",
        q_threshold_from=float(q_threshold_from),
        q_threshold_to=float(q_threshold_to),
        delta=delta,
        evidence_artifact_relpath=str(rel),
        evidence_artifact_fingerprint=str(artifact.get("fingerprint")),
        impact_set=impact_set,
        per_observable=per_obs,
        narrative=narrative,
    )


def render_ovdq02_lock_markdown(record: OVDQ02DQ01v2ThresholdUpdateRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-DQ-02 — DQ-01_v2 threshold update (computed policy lock)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- Documents a proposed / parallel policy definition; does not mutate canonical selection\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovdq02_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "policies" / "DQ-01_v2_threshold_update.md"

    out.parent.mkdir(parents=True, exist_ok=True)
    rec = ovdq02_dq01_v2_threshold_update_record()
    out.write_text(render_ovdq02_lock_markdown(rec), encoding="utf-8")
    return out
