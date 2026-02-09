"""OV-XD-04: overlap-only preferred-fit-family comparison (OV-04x vs OV-03x).

Purpose
- Record, deterministically, whether the robustness-only preferred fit-family
  outcomes agree between OV-04x (DS-02 low-k slot) and OV-03x (B1 dataset)
  within the OV-XD-03 overlap band.

Scope / limits
- Overlap-only bookkeeping record.
- No continuity claim.
- No averaging across regimes.
- β not inferred / β-null posture.

Design constraints
- Deterministic (no RNG).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Literal

from formal.python.toe.observables.ovxd03_overlap_band_record import ovxd03_overlap_band_record


OVPreferredFamily = Literal["curved", "undecided"]


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


def _preferred_family(*, prefer_curved: bool, robustness_failed: bool) -> OVPreferredFamily:
    # Align with OV-01 family selection policy: selection is decisive only when
    # prefer_curved is true and robustness_failed is false.
    prefer = bool(prefer_curved and (not robustness_failed))
    return "curved" if prefer else "undecided"


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
        "Unsupported policy for OV-XD-04 (expected DQ-01_v1 with q_threshold 0.90, or DQ-01_v2 with q_threshold 1.05)"
    )


def _load_preference_from_lock(*, repo_root: Path, lock_rel_path: str, observable_id: str) -> dict[str, Any]:
    path = repo_root / Path(lock_rel_path)
    text = path.read_text(encoding="utf-8")
    payload = _extract_json_block(text)
    report_fp = _extract_report_fingerprint(text)

    return {
        "observable_id": str(observable_id),
        "adequacy_policy": str(payload.get("adequacy_policy", "unknown")),
        "prefer_curved": bool(payload["prefer_curved"]),
        "robustness_failed": bool(payload["robustness_failed"]),
        "report_fingerprint": str(report_fp),
        "lock_payload_fingerprint": _sha256_json(payload),
        "lock_path": str(lock_rel_path).replace("\\", "/"),
    }


@dataclass(frozen=True)
class OVXD04OverlapOnlyPreferenceComparisonRecord:
    schema: str

    overlap_band: tuple[float, float]

    low_observable_id: str
    high_observable_id: str

    low_preference: dict[str, Any]
    high_preference: dict[str, Any]

    low_preferred_family: OVPreferredFamily
    high_preferred_family: OVPreferredFamily

    agreement: bool
    decisiveness: str

    provenance: dict[str, Any]
    notes: str

    def to_jsonable(self) -> dict[str, Any]:
        k0, k1 = self.overlap_band
        return {
            "schema": str(self.schema),
            "overlap_band": [float(k0), float(k1)],
            "low_observable_id": str(self.low_observable_id),
            "high_observable_id": str(self.high_observable_id),
            "low_preference": dict(self.low_preference),
            "high_preference": dict(self.high_preference),
            "low_preferred_family": str(self.low_preferred_family),
            "high_preferred_family": str(self.high_preferred_family),
            "agreement": bool(self.agreement),
            "decisiveness": str(self.decisiveness),
            "provenance": self.provenance,
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable())


def ovxd04_overlap_only_preference_comparison_record(
    *,
    adequacy_policy: str = "DQ-01_v1",
    q_threshold: float = 0.90,
) -> OVXD04OverlapOnlyPreferenceComparisonRecord:
    repo_root = _find_repo_root(Path(__file__))

    xd03 = ovxd03_overlap_band_record()
    overlap = xd03.overlap
    overlap_band = (float(overlap.k_min), float(overlap.k_max))

    low_lock, high_lock = _robustness_lock_paths_for_policy(adequacy_policy=str(adequacy_policy), q_threshold=float(q_threshold))

    low = _load_preference_from_lock(repo_root=repo_root, lock_rel_path=low_lock, observable_id="OV-04x")
    high = _load_preference_from_lock(repo_root=repo_root, lock_rel_path=high_lock, observable_id="OV-03x")

    fam_low = _preferred_family(prefer_curved=bool(low["prefer_curved"]), robustness_failed=bool(low["robustness_failed"]))
    fam_high = _preferred_family(
        prefer_curved=bool(high["prefer_curved"]), robustness_failed=bool(high["robustness_failed"])
    )

    agreement = bool(fam_low == fam_high)

    decisive_low = bool(fam_low != "undecided")
    decisive_high = bool(fam_high != "undecided")
    if decisive_low and decisive_high:
        decisiveness = "both-decisive"
    elif decisive_low or decisive_high:
        decisiveness = "one-decisive"
    else:
        decisiveness = "neither-decisive"

    provenance: dict[str, Any] = {
        "overlap_band": {
            "source": "OV-XD-03",
            "ovxd03_schema": xd03.schema,
            "ovxd03_fingerprint": xd03.fingerprint(),
        },
        "preferences": {
            "low": {"source": "lock", "observable_id": "OV-04x", "lock_path": low_lock},
            "high": {"source": "lock", "observable_id": "OV-03x", "lock_path": high_lock},
        },
        "policy": {
            "curved_fit_adequacy_policy": str(adequacy_policy),
            "q_threshold": float(q_threshold),
        },
    }

    return OVXD04OverlapOnlyPreferenceComparisonRecord(
        schema="OV-XD-04/v1",
        overlap_band=overlap_band,
        low_observable_id="OV-04x",
        high_observable_id="OV-03x",
        low_preference=low,
        high_preference=high,
        low_preferred_family=fam_low,
        high_preferred_family=fam_high,
        agreement=agreement,
        decisiveness=decisiveness,
        provenance=provenance,
        notes=(
            "Overlap-only bookkeeping record: compares robustness-only preferred-fit-family outcomes only within the "
            "OV-XD-03 overlap band; no continuity claim; no averaging across regimes; β not inferred / β-null posture."
        ),
    )


def render_ovxd04_lock_markdown(record: OVXD04OverlapOnlyPreferenceComparisonRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-XD-04 — Overlap-only preferred-fit-family comparison (OV-04x vs OV-03x)\n\n"
        "Scope / limits\n"
        "- Overlap-only bookkeeping record\n"
        "- No continuity claim\n"
        "- No averaging across regimes\n"
        "- β not inferred / β-null posture\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovxd04_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    rec = ovxd04_overlap_only_preference_comparison_record()

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-XD-04_overlap_only_preference_comparison.md"
        )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovxd04_lock_markdown(rec), encoding="utf-8")
    return out


def write_ovxd04_lock_for_policy(
    *,
    lock_path: Path | None,
    adequacy_policy: str,
    q_threshold: float,
) -> Path:
    repo_root = _find_repo_root(Path(__file__))

    is_canonical = (str(adequacy_policy) == "DQ-01_v1") and (abs(float(q_threshold) - 0.90) <= 1e-12)
    if lock_path is None and (not is_canonical):
        raise ValueError("Non-canonical OV-XD-04 lock requires explicit lock_path")

    rec = ovxd04_overlap_only_preference_comparison_record(
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
            / "OV-XD-04_overlap_only_preference_comparison.md"
        )

    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovxd04_lock_markdown(rec), encoding="utf-8")
    return out
