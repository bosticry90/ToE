"""OV-SEL-02: selection-status narrative under DQ-01_v1 vs DQ-01_v2 (computed).

Purpose
- Provide a locked, policy-interpretable narrative comparing selection status
  under DQ-01_v1 (q_threshold=0.90) vs DQ-01_v2 (q_threshold=1.05), using the
  pinned diagnostic sensitivity artifact.

Scope / limits
- Bookkeeping / narrative only; no physics claim.
- Evaluated set is limited to {OV-01g, OV-02x, OV-03x, OV-04x} as represented
  in the policy sensitivity artifact.

Design constraints
- Deterministic (no RNG, no network).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Literal

from formal.python.toe.observables.ovdq01_policy_sensitivity_record import default_artifact_path


SelectionStatus = Literal["decisive_curved", "undecided"]


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


def _selection_status_from_would_prefer(*, would_prefer_curved: bool, robustness_failed: bool) -> SelectionStatus:
    decisive = bool(would_prefer_curved and (not robustness_failed))
    return "decisive_curved" if decisive else "undecided"


@dataclass(frozen=True)
class OVSEL02SelectionStatusRecord:
    schema: str
    status_date: str

    q_threshold_v1: float
    q_threshold_v2: float

    evidence_artifact_relpath: str
    evidence_artifact_fingerprint: str

    v1: dict[str, Any]
    v2: dict[str, Any]

    delta: dict[str, Any]
    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "q_threshold_v1": float(self.q_threshold_v1),
            "q_threshold_v2": float(self.q_threshold_v2),
            "evidence_artifact_relpath": str(self.evidence_artifact_relpath),
            "evidence_artifact_fingerprint": str(self.evidence_artifact_fingerprint),
            "v1": dict(self.v1),
            "v2": dict(self.v2),
            "delta": dict(self.delta),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsel02_selection_status_record(
    *,
    status_date: str = "2026-01-23",
    q_threshold_v1: float = 0.90,
    q_threshold_v2: float = 1.05,
) -> OVSEL02SelectionStatusRecord:
    repo_root = _find_repo_root(Path(__file__))

    artifact_path = default_artifact_path()
    artifact = _load_json(artifact_path)

    if str(artifact.get("schema")) != "OV-DQ-01_policy_sensitivity/v2":
        raise ValueError("Expected OV-DQ-01 policy sensitivity schema v2")

    def _extract(obs_id: str) -> dict[str, Any]:
        key = {
            "OV-01g": "ov01g",
            "OV-02x": "ov02x",
            "OV-03x": "ov03x",
            "OV-04x": "ov04x",
        }[obs_id]
        section = dict(artifact[key])
        grid = list(section["grid"])

        r1 = _row_at(grid, float(q_threshold_v1))
        r2 = _row_at(grid, float(q_threshold_v2))

        if obs_id == "OV-02x":
            s1 = _selection_status_from_would_prefer(
                would_prefer_curved=bool(r1["baseline_prefer_curved"]),
                robustness_failed=bool(r1["robustness_failed"]),
            )
            s2 = _selection_status_from_would_prefer(
                would_prefer_curved=bool(r2["baseline_prefer_curved"]),
                robustness_failed=bool(r2["robustness_failed"]),
            )
        else:
            s1 = _selection_status_from_would_prefer(
                would_prefer_curved=bool(r1["would_prefer_curved"]),
                robustness_failed=bool(r1["robustness_failed"]),
            )
            s2 = _selection_status_from_would_prefer(
                would_prefer_curved=bool(r2["would_prefer_curved"]),
                robustness_failed=bool(r2["robustness_failed"]),
            )

        return {
            "observable_id": str(obs_id),
            "row_v1": r1,
            "row_v2": r2,
            "selection_status_v1": s1,
            "selection_status_v2": s2,
            "changed": bool(s1 != s2),
        }

    per = {obs: _extract(obs) for obs in ("OV-01g", "OV-02x", "OV-03x", "OV-04x")}

    changed = [k for (k, v) in per.items() if bool(v["changed"])]

    v1_summary = {k: v["selection_status_v1"] for (k, v) in per.items()}
    v2_summary = {k: v["selection_status_v2"] for (k, v) in per.items()}

    delta = {
        "changed_observables": list(changed),
        "v1": dict(v1_summary),
        "v2": dict(v2_summary),
    }

    narrative = (
        "Selection status comparison (robustness-only; no physics claim):\n"
        f"- DQ-01_v1 uses q_threshold={float(q_threshold_v1):.12g}.\n"
        f"- DQ-01_v2 uses q_threshold={float(q_threshold_v2):.12g}.\n"
        f"- Evidence: {artifact_path.as_posix()} (fingerprint={str(artifact.get('fingerprint'))}).\n"
        f"- Under v1: {v1_summary}.\n"
        f"- Under v2: {v2_summary}.\n"
        f"- Delta: changed_observables={list(changed)} (expected: ['OV-03x']).\n"
        "No continuity claim; no averaging across regimes; β not inferred / β-null posture."
    )

    rel = artifact_path.resolve().relative_to(repo_root.resolve()).as_posix()

    return OVSEL02SelectionStatusRecord(
        schema="OV-SEL-02_selection_status_policy_compare/v1",
        status_date=str(status_date),
        q_threshold_v1=float(q_threshold_v1),
        q_threshold_v2=float(q_threshold_v2),
        evidence_artifact_relpath=str(rel),
        evidence_artifact_fingerprint=str(artifact.get("fingerprint")),
        v1={"per_observable": per, "summary": v1_summary},
        v2={"per_observable": per, "summary": v2_summary},
        delta=delta,
        narrative=narrative,
    )


def render_ovsel02_lock_markdown(record: OVSEL02SelectionStatusRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-02 — Selection status under DQ-01_v1 vs DQ-01_v2 (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- Evaluated set limited to OV-01g/OV-02x/OV-03x/OV-04x as represented in OV-DQ-01 policy sensitivity\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsel02_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SEL-02_selection_status_policy_compare.md"

    out.parent.mkdir(parents=True, exist_ok=True)
    rec = ovsel02_selection_status_record()
    out.write_text(render_ovsel02_lock_markdown(rec), encoding="utf-8")
    return out
