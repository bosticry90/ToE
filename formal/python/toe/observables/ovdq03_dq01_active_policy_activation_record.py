"""OV-DQ-03: DQ-01 active policy activation record (computed).

Purpose
- Pin the project decision of which DQ-01 variant is the *active* selection policy.
- Keep DQ-01_v1 intact as a conservative baseline.

This is the missing piece after OV-DQ-02 (which defined the v2 threshold change):
OV-DQ-03 records the activation stance and cites the pinned evidence/guardrails.

Scope / limits
- Bookkeeping / policy posture only; no physics claim.
- Activation is limited to the OV-03x/OV-04x decision layer and the overlap-only
  comparison layer (OV-XD-04 / OV-BR-02 downstream), not to benchmark handling.

Design constraints
- Deterministic (no RNG, no network).
- Does not depend on OV-SEL-01 (to avoid circular dependence).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovsel02_selection_status_record import ovsel02_selection_status_record


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


@dataclass(frozen=True)
class OVDQ03DQ01ActivePolicyActivationRecord:
    schema: str
    date: str

    effective_status_date: str

    active_policy_id: str
    baseline_policy_id: str

    q_threshold_active: float
    q_threshold_baseline: float

    scope: dict[str, Any]

    evidence: dict[str, Any]
    guardrails: dict[str, Any]

    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "effective_status_date": str(self.effective_status_date),
            "active_policy_id": str(self.active_policy_id),
            "baseline_policy_id": str(self.baseline_policy_id),
            "q_threshold_active": float(self.q_threshold_active),
            "q_threshold_baseline": float(self.q_threshold_baseline),
            "scope": dict(self.scope),
            "evidence": dict(self.evidence),
            "guardrails": dict(self.guardrails),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def dq01_active_policy() -> dict[str, Any]:
    """Single-source declaration of the active DQ-01 policy posture.

    Option B (recommended): DQ-01_v2 is active; DQ-01_v1 remains baseline.
    """

    return {
        "active_policy_id": "DQ-01_v2",
        "baseline_policy_id": "DQ-01_v1",
        "q_threshold_active": 1.05,
        "q_threshold_baseline": 0.90,
        "effective_status_date": "2026-01-23",
    }


def ovdq03_dq01_active_policy_activation_record(
    *,
    date: str = "2026-01-24",
) -> OVDQ03DQ01ActivePolicyActivationRecord:
    repo_root = _find_repo_root(Path(__file__))

    posture = dq01_active_policy()

    sel02 = ovsel02_selection_status_record(
        status_date=str(posture["effective_status_date"]),
        q_threshold_v1=float(posture["q_threshold_baseline"]),
        q_threshold_v2=float(posture["q_threshold_active"]),
    )

    changed = list(sel02.delta.get("changed_observables", []))
    expected_changed = ["OV-03x"]

    scope = {
        "layer": "selection_decision_layer",
        "applies_to": ["OV-03x", "OV-04x", "OV-XD-04", "OV-BR-02"],
        "benchmarks_in_scope": False,
        "notes": "DQ-01 policy affects decisiveness gating only; does not introduce continuity/averaging or benchmark participation.",
    }

    evidence = {
        "ov_sel_02_lock": "formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
        "ov_sel_02_record_fingerprint": sel02.fingerprint(),
        "evidence_artifact_relpath": sel02.evidence_artifact_relpath,
        "evidence_artifact_fingerprint": sel02.evidence_artifact_fingerprint,
    }

    guardrails = {
        "expected_changed_observables": expected_changed,
        "observed_changed_observables": list(changed),
        "changed_set_ok": bool(changed == expected_changed),
        "benchmark_non_participation_guardrails": [
            "OV-SEL-BM-02",
            "OV-SEL-BM-03",
            "OV-SEL-BM-04",
        ],
    }

    narrative = (
        "DQ-01 active policy activation (bookkeeping-only; no physics claim):\n"
        f"- Active policy: {posture['active_policy_id']} (q_threshold={float(posture['q_threshold_active']):.12g}).\n"
        f"- Baseline policy remains pinned: {posture['baseline_policy_id']} (q_threshold={float(posture['q_threshold_baseline']):.12g}).\n"
        f"- Effective status date for selection narratives: {posture['effective_status_date']}.\n"
        f"- Evidence: OV-SEL-02 fingerprint={sel02.fingerprint()} and policy sensitivity artifact fingerprint={sel02.evidence_artifact_fingerprint}.\n"
        f"- Guardrail: changed_observables={list(changed)} (expected {expected_changed})."
    )

    return OVDQ03DQ01ActivePolicyActivationRecord(
        schema="OV-DQ-03_dq01_active_policy_activation/v1",
        date=str(date),
        effective_status_date=str(posture["effective_status_date"]),
        active_policy_id=str(posture["active_policy_id"]),
        baseline_policy_id=str(posture["baseline_policy_id"]),
        q_threshold_active=float(posture["q_threshold_active"]),
        q_threshold_baseline=float(posture["q_threshold_baseline"]),
        scope=scope,
        evidence=evidence,
        guardrails=guardrails,
        narrative=narrative,
    )


def render_ovdq03_lock_markdown(record: OVDQ03DQ01ActivePolicyActivationRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-DQ-03 — DQ-01 active policy activation (computed policy lock)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / policy posture only; no physics claim\n"
        "- Activates a selection-policy label; keeps DQ-01_v1 pinned as baseline\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovdq03_lock(*, lock_path: Path | None = None, date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "policies" / "DQ-01_active_policy_activation.md"

    out.parent.mkdir(parents=True, exist_ok=True)
    rec = ovdq03_dq01_active_policy_activation_record(date=str(date))
    out.write_text(render_ovdq03_lock_markdown(rec), encoding="utf-8")
    return out
