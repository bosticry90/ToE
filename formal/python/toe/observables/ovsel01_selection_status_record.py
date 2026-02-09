"""OV-SEL-01: locked selection-status narrative (computed from locks).

Purpose
- Provide a single, policy-interpretable, locked narrative of current selection
    outcomes under the *active* DQ-01 policy for:
  - OV-04x (DS-02 low-k)
  - OV-03x (B1 second dataset)
  - The overlap-only comparison (OV-XD-04) within the overlap band (OV-XD-03)

Scope / limits
- Bookkeeping / narrative only; no physics claim.
- No continuity claim; no averaging across regimes.
- β not inferred / β-null posture.
- Computed from existing locks; does not change any policy threshold.

Design constraints
- Deterministic (no RNG, no network).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Literal

from formal.python.toe.observables.ov01_fit_family_robustness import (
    OV01FitFamilyRobustnessReport,
    ov01_fit_family_robustness_failure_reasons,
)
from formal.python.toe.observables.ovdq03_dq01_active_policy_activation_record import dq01_active_policy


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


def _extract_json_block(md_text: str) -> dict[str, Any]:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise ValueError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_fingerprint_line(md_text: str, *, label: str) -> str:
    m = re.search(rf"{re.escape(label)}:\s*`([0-9a-f]{{64}})`", md_text)
    if m is None:
        raise ValueError(f"Missing fingerprint line: {label!r}")
    return m.group(1)


def _report_from_lock_payload(payload: dict[str, Any]) -> OV01FitFamilyRobustnessReport:
    return OV01FitFamilyRobustnessReport(
        config_tag=str(payload["config_tag"]),
        adequacy_policy=str(payload.get("adequacy_policy", "unknown")),
        fn_fingerprint=str(payload["fn_fingerprint"]),
        linear_report_fingerprint=str(payload["linear_report_fingerprint"]),
        curved_report_fingerprint=str(payload["curved_report_fingerprint"]),
        r_max_linear=float(payload["r_max_linear"]),
        r_rms_linear=float(payload["r_rms_linear"]),
        r_max_curved=float(payload["r_max_curved"]),
        r_rms_curved=float(payload["r_rms_curved"]),
        q_ratio=float(payload["q_ratio"]),
        q_threshold=float(payload["q_threshold"]),
        curved_adequacy_passes=bool(payload["curved_adequacy_passes"]),
        prefer_curved=bool(payload["prefer_curved"]),
        robustness_failed=bool(payload["robustness_failed"]),
    )


def _selection_status(*, prefer_curved: bool, robustness_failed: bool) -> SelectionStatus:
    decisive = bool(prefer_curved and (not robustness_failed))
    return "decisive_curved" if decisive else "undecided"


def _load_robustness_lock(*, repo_root: Path, lock_rel_path: str, observable_id: str) -> dict[str, Any]:
    p = repo_root / Path(lock_rel_path)
    text = p.read_text(encoding="utf-8")

    payload = _extract_json_block(text)
    report_fp = _extract_fingerprint_line(text, label="Report fingerprint")

    rep = _report_from_lock_payload(payload)
    reasons = ov01_fit_family_robustness_failure_reasons(rep)

    return {
        "observable_id": str(observable_id),
        "lock_path": str(lock_rel_path).replace("\\", "/"),
        "report_fingerprint": str(report_fp),
        "lock_payload_fingerprint": _sha256_json(payload),
        "adequacy_policy": str(payload.get("adequacy_policy", "unknown")),
        "curved_adequacy_passes": bool(payload.get("curved_adequacy_passes")),
        "prefer_curved": bool(payload.get("prefer_curved")),
        "robustness_failed": bool(payload.get("robustness_failed")),
        "q_ratio": float(payload.get("q_ratio")),
        "q_threshold": float(payload.get("q_threshold")),
        "r_max_linear": float(payload.get("r_max_linear")),
        "r_max_curved": float(payload.get("r_max_curved")),
        "failure_reasons": list(reasons),
        "selection_status": _selection_status(
            prefer_curved=bool(payload.get("prefer_curved")),
            robustness_failed=bool(payload.get("robustness_failed")),
        ),
    }


def _load_json_lock(*, repo_root: Path, lock_rel_path: str, fingerprint_label: str) -> tuple[dict[str, Any], str]:
    p = repo_root / Path(lock_rel_path)
    text = p.read_text(encoding="utf-8")
    payload = _extract_json_block(text)
    fp = _extract_fingerprint_line(text, label=fingerprint_label)
    return payload, fp


@dataclass(frozen=True)
class OVSEL01SelectionStatusRecord:
    schema: str
    status_date: str

    ov04x: dict[str, Any]
    ov03x: dict[str, Any]

    ovxd03_overlap_band: dict[str, Any]
    ovxd04_overlap_only_comparison: dict[str, Any]

    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "ov04x": dict(self.ov04x),
            "ov03x": dict(self.ov03x),
            "ovxd03_overlap_band": dict(self.ovxd03_overlap_band),
            "ovxd04_overlap_only_comparison": dict(self.ovxd04_overlap_only_comparison),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsel01_selection_status_record(*, status_date: str = "2026-01-23") -> OVSEL01SelectionStatusRecord:
    repo_root = _find_repo_root(Path(__file__))

    posture = dq01_active_policy()
    active_policy_id = str(posture["active_policy_id"])

    if active_policy_id == "DQ-01_v2":
        ov04x_lock = "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk_DQ-01_v2.md"
        ov03x_lock = "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset_DQ-01_v2.md"
        xd04_lock = "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison_DQ-01_v2.md"
    elif active_policy_id == "DQ-01_v1":
        ov04x_lock = "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md"
        ov03x_lock = "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md"
        xd04_lock = "formal/markdown/locks/observables/OV-XD-04_overlap_only_preference_comparison.md"
    else:
        raise ValueError(f"Unsupported active_policy_id={active_policy_id!r} (expected DQ-01_v1 or DQ-01_v2)")

    ov04x = _load_robustness_lock(
        repo_root=repo_root,
        lock_rel_path=str(ov04x_lock),
        observable_id="OV-04x",
    )
    ov03x = _load_robustness_lock(
        repo_root=repo_root,
        lock_rel_path=str(ov03x_lock),
        observable_id="OV-03x",
    )

    xd03_payload, xd03_fp = _load_json_lock(
        repo_root=repo_root,
        lock_rel_path="formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
        fingerprint_label="Record fingerprint",
    )

    overlap = dict(xd03_payload.get("overlap", {}))
    ovxd03_overlap_band = {
        "lock_path": "formal/markdown/locks/observables/OV-XD-03_cross_dataset_overlap_band_record.md",
        "record_fingerprint": str(xd03_fp),
        "schema": str(xd03_payload.get("schema", "unknown")),
        "overlap": {
            "k_min": float(overlap.get("k_min")),
            "k_max": float(overlap.get("k_max")),
            "non_empty": bool(overlap.get("non_empty")),
        },
    }

    xd04_payload, xd04_fp = _load_json_lock(
        repo_root=repo_root,
        lock_rel_path=str(xd04_lock),
        fingerprint_label="Record fingerprint",
    )

    ovxd04_overlap_only = {
        "lock_path": str(xd04_lock),
        "record_fingerprint": str(xd04_fp),
        "schema": str(xd04_payload.get("schema", "unknown")),
        "overlap_band": list(xd04_payload.get("overlap_band", [])),
        "decisiveness": str(xd04_payload.get("decisiveness", "unknown")),
        "agreement": bool(xd04_payload.get("agreement")),
    }

    narrative = (
        f"Selection status under active DQ-01 policy={active_policy_id} (robustness-only; no physics claim):\n"
        f"- Baseline policy remains pinned: {str(posture['baseline_policy_id'])} (q_threshold={float(posture['q_threshold_baseline']):.6g}).\n"
        f"- OV-04x (DS-02 low-k): selection_status={ov04x['selection_status']} "
        f"(prefer_curved={bool(ov04x['prefer_curved'])}, robustness_failed={bool(ov04x['robustness_failed'])}, "
        f"q_ratio={float(ov04x['q_ratio']):.6g} <= q_threshold={float(ov04x['q_threshold']):.6g}).\n"
        f"- OV-03x (B1): selection_status={ov03x['selection_status']} "
        f"(curved_adequacy_passes={bool(ov03x['curved_adequacy_passes'])}, "
        f"q_ratio={float(ov03x['q_ratio']):.6g} > q_threshold={float(ov03x['q_threshold']):.6g}; "
        f"failure_reasons={ov03x['failure_reasons']}).\n"
        f"- Overlap band (OV-XD-03): non_empty={bool(ovxd03_overlap_band['overlap']['non_empty'])}, "
        f"k=[{float(ovxd03_overlap_band['overlap']['k_min']):.6g}, {float(ovxd03_overlap_band['overlap']['k_max']):.6g}].\n"
        f"- Overlap-only comparison (OV-XD-04): decisiveness={ovxd04_overlap_only['decisiveness']}, "
        f"agreement={bool(ovxd04_overlap_only['agreement'])}.\n"
        "No continuity claim; no averaging across regimes; β not inferred / β-null posture."
    )

    return OVSEL01SelectionStatusRecord(
        schema="OV-SEL-01_selection_status/v1",
        status_date=str(status_date),
        ov04x=ov04x,
        ov03x=ov03x,
        ovxd03_overlap_band=ovxd03_overlap_band,
        ovxd04_overlap_only_comparison=ovxd04_overlap_only,
        narrative=narrative,
    )


def render_ovsel01_lock_markdown(record: OVSEL01SelectionStatusRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-01 — Selection status narrative (active DQ-01 policy; computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- No continuity claim; no averaging across regimes\n"
        "- β not inferred / β-null posture\n"
        "- Computed from locks; does not change policy thresholds\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsel01_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-23") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SEL-01_selection_status.md"

    rec = ovsel01_selection_status_record(status_date=str(status_date))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsel01_lock_markdown(rec), encoding="utf-8")
    return out
