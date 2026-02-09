"""OV-BR-02: regime bridge record for OV-04x (low-k DS-02) ↔ OV-03x (high-k B1).

Purpose
- Declare two k-bands anchored by OV-04x (low-k, DS-02) and OV-03x (high-k, B1),
  and record only band geometry plus regime-separated robustness-only preference
  outcomes.
- Use OV-XD-03 as the authoritative overlap-band bookkeeping source.

Scope / limits
- split into sub-bands
- evaluated separately
- overlap-only comparability
- no averaging across regimes
- no continuity claim
- β not inferred / β-null posture

Design constraints
- Deterministic (no RNG).
- No fitting. No model selection. No statistics.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ov01_fit_family_robustness import (
    OV01FitFamilyRobustnessReport,
    ov01_fit_family_robustness_failure_reasons,
)
from formal.python.toe.observables.ovxd03_overlap_band_record import ovxd03_overlap_band_record


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


def _extract_report_fingerprint(md_text: str) -> str:
    m = re.search(r"Report fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing report fingerprint line")
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


def _load_preference_from_lock(*, repo_root: Path, lock_rel_path: str, observable_id: str) -> dict[str, Any]:
    path = repo_root / Path(lock_rel_path)
    text = path.read_text(encoding="utf-8")
    payload = _extract_json_block(text)
    report_fp = _extract_report_fingerprint(text)

    rep = _report_from_lock_payload(payload)
    failure_reasons = ov01_fit_family_robustness_failure_reasons(rep)

    return {
        "observable_id": str(observable_id),
        "adequacy_policy": str(payload.get("adequacy_policy", "unknown")),
        "prefer_curved": bool(payload["prefer_curved"]),
        "robustness_failed": bool(payload["robustness_failed"]),
        "curved_adequacy_passes": bool(payload.get("curved_adequacy_passes")),
        "q_ratio": float(payload.get("q_ratio")) if payload.get("q_ratio") is not None else None,
        "q_threshold": float(payload.get("q_threshold")) if payload.get("q_threshold") is not None else None,
        "failure_reasons": list(failure_reasons),
        "report_fingerprint": str(report_fp),
        "lock_payload_fingerprint": _sha256_json(payload),
        "lock_path": str(lock_rel_path).replace("\\", "/"),
    }


def _robustness_lock_paths_for_policy(*, adequacy_policy: str, q_threshold: float) -> tuple[str, str]:
    ap = str(adequacy_policy)
    qt = float(q_threshold)

    # Canonical baseline (DQ-01_v1 selection): q_threshold=0.90.
    if ap == "DQ-01_v1" and abs(qt - 0.90) <= 1e-12:
        return (
            "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
            "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
        )

    # Parallel threshold-only variant: DQ-01_v2 label (q_threshold=1.05).
    # Back-compat: allow the older selector pair (DQ-01_v1, 1.05).
    if (ap in {"DQ-01_v2", "DQ-01_v1"}) and abs(qt - 1.05) <= 1e-12:
        return (
            "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk_DQ-01_v2.md",
            "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset_DQ-01_v2.md",
        )

    raise ValueError(
        "Unsupported policy for OV-BR-02 (expected DQ-01_v1 with q_threshold 0.90, or DQ-01_v2 with q_threshold 1.05)"
    )


def _compute_gap(*, low_band: tuple[float, float], high_band: tuple[float, float]) -> tuple[tuple[float, float] | None, float | None]:
    low_min, low_max = float(low_band[0]), float(low_band[1])
    high_min, high_max = float(high_band[0]), float(high_band[1])
    # If they overlap, no gap.
    if min(low_max, high_max) >= max(low_min, high_min):
        return None, None
    # Disjoint: gap is [kmax_low, kmin_high] in ascending order.
    a = min(low_max, high_max)
    b = max(low_min, high_min)
    gap = (float(a), float(b))
    return gap, float(gap[1] - gap[0])


@dataclass(frozen=True)
class OVBR02RegimeBridgeRecord:
    schema: str

    low_band: tuple[float, float]
    high_band: tuple[float, float]

    overlap: tuple[float, float] | None
    gap: tuple[float, float] | None
    gap_width: float | None

    low_preference: dict[str, Any]
    high_preference: dict[str, Any]

    comparability_statement: str
    provenance: dict[str, Any]
    notes: str

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "low_band": [float(self.low_band[0]), float(self.low_band[1])],
            "high_band": [float(self.high_band[0]), float(self.high_band[1])],
            "overlap": None if self.overlap is None else [float(self.overlap[0]), float(self.overlap[1])],
            "gap": None if self.gap is None else [float(self.gap[0]), float(self.gap[1])],
            "gap_width": None if self.gap_width is None else float(self.gap_width),
            "low_preference": dict(self.low_preference),
            "high_preference": dict(self.high_preference),
            "comparability_statement": str(self.comparability_statement),
            "provenance": self.provenance,
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable())


def ovbr02_regime_bridge_record(
    *,
    adequacy_policy: str = "DQ-01_v1",
    q_threshold: float = 0.90,
) -> OVBR02RegimeBridgeRecord:
    repo_root = _find_repo_root(Path(__file__))

    xd03 = ovxd03_overlap_band_record()
    bands = xd03.bands

    if "OV-04x" not in bands:
        raise RuntimeError("OV-BR-02 requires OV-04x to be included in OV-XD-03 bands")
    if "OV-03x" not in bands:
        raise RuntimeError("OV-BR-02 requires OV-03x to be included in OV-XD-03 bands")

    low_band = (float(bands["OV-04x"].k_min), float(bands["OV-04x"].k_max))
    high_band = (float(bands["OV-03x"].k_min), float(bands["OV-03x"].k_max))

    # Authoritative overlap from OV-XD-03 intersection bookkeeping.
    overlap = None
    if bool(xd03.overlap.non_empty):
        overlap = (float(xd03.overlap.k_min), float(xd03.overlap.k_max))

    gap, gap_width = _compute_gap(low_band=low_band, high_band=high_band)

    low_lock, high_lock = _robustness_lock_paths_for_policy(adequacy_policy=str(adequacy_policy), q_threshold=float(q_threshold))

    low_pref = _load_preference_from_lock(repo_root=repo_root, lock_rel_path=low_lock, observable_id="OV-04x")
    high_pref = _load_preference_from_lock(repo_root=repo_root, lock_rel_path=high_lock, observable_id="OV-03x")

    if overlap is not None:
        comparability_statement = (
            "Overlap exists; comparison is meaningful only within the OV-XD-03 overlap band. "
            "This record does not assert continuity; it records regime-separated results and band geometry only. "
            "No averaging across regimes."
        )
    else:
        comparability_statement = (
            "No overlap (per OV-XD-03); comparison is not valid; per-dataset evaluation only. "
            "This record does not assert continuity; it records regime-separated results and band geometry only. "
            "No averaging across regimes."
        )

    provenance: dict[str, Any] = {
        "bands": {
            "source": "OV-XD-03",
            "ovxd03_schema": xd03.schema,
            "ovxd03_fingerprint": xd03.fingerprint(),
        },
        "preferences": {
            "low": {
                "source": "lock",
                "lock_path": low_lock,
            },
            "high": {
                "source": "lock",
                "lock_path": high_lock,
            },
        },
        "policy": {
            "curved_fit_adequacy_policy": str(adequacy_policy),
            "q_threshold": float(q_threshold),
        },
    }

    return OVBR02RegimeBridgeRecord(
        schema="OV-BR-02/v1",
        low_band=low_band,
        high_band=high_band,
        overlap=overlap,
        gap=gap,
        gap_width=gap_width,
        low_preference=low_pref,
        high_preference=high_pref,
        comparability_statement=comparability_statement,
        provenance=provenance,
        notes=(
            "Bookkeeping only; split into sub-bands; evaluated separately; overlap-only comparability; "
            "no averaging across regimes; no continuity claim; β not inferred / β-null posture."
        ),
    )


def render_ovbr02_lock_markdown(record: OVBR02RegimeBridgeRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    scope_fence = (
        "This record does not assert continuity; it records regime-separated results and their k-band overlap/gap only. "
        "No averaging."
    )

    return (
        "# OV-BR-02 — Regime bridge record (OV-04x ↔ OV-03x) (computed)\n\n"
        f"{scope_fence}\n\n"
        "Scope / limits\n"
        "- split into sub-bands\n"
        "- evaluated separately\n"
        "- overlap-only comparability\n"
        "- no averaging across regimes\n"
        "- no continuity claim\n"
        "- β not inferred / β-null posture\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr02_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    rec = ovbr02_regime_bridge_record()

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-BR-02_regime_bridge_record.md"
        )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr02_lock_markdown(rec), encoding="utf-8")
    return out


def write_ovbr02_lock_for_policy(
    *,
    lock_path: Path | None,
    adequacy_policy: str,
    q_threshold: float,
) -> Path:
    repo_root = _find_repo_root(Path(__file__))

    is_canonical = (str(adequacy_policy) == "DQ-01_v1") and (abs(float(q_threshold) - 0.90) <= 1e-12)
    if lock_path is None and (not is_canonical):
        raise ValueError("Non-canonical OV-BR-02 lock requires explicit lock_path")

    rec = ovbr02_regime_bridge_record(
        adequacy_policy=str(adequacy_policy),
        q_threshold=float(q_threshold),
    )

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-BR-02_regime_bridge_record.md"
        )

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr02_lock_markdown(rec), encoding="utf-8")
    return out
