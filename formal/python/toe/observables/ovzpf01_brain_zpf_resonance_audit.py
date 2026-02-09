"""OV-ZPF-01: Brain–ZPF resonance audit scaffold (spectral overlap bookkeeping).

This module provides a conservative, deterministic *audit scaffold* for assessing
simple frequency-band overlap between:
- candidate neural oscillation bands (e.g., beta/gamma), and
- candidate "mode" bands from a hypothesized coupling source (labeled "ZPF" here).

Policy / limits
- This is not an empirical anchor.
- By default it uses synthetic/demo inputs.
- It does not assert physical coupling, causation, or feasibility; it records
  overlap geometry and a few clearly-labeled heuristic summaries.

The intent is to provide a disciplined *front-door* quantitative harness so that
any future ZPF-related legacy claims can be staged into explicit tests and
artifact bookkeeping, without promoting epistemic status.
"""

from __future__ import annotations

from dataclasses import asdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any


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
class FrequencyBand:
    name: str
    f_low_hz: float
    f_high_hz: float

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name.strip():
            raise ValueError("band name must be a non-empty string")
        if not (self.f_low_hz >= 0.0 and self.f_high_hz >= 0.0):
            raise ValueError("band frequencies must be non-negative")
        if not (self.f_high_hz > self.f_low_hz):
            raise ValueError("band must satisfy f_high_hz > f_low_hz")

    @property
    def width_hz(self) -> float:
        return float(self.f_high_hz - self.f_low_hz)

    @property
    def center_hz(self) -> float:
        return 0.5 * float(self.f_low_hz + self.f_high_hz)


@dataclass(frozen=True)
class BandOverlap:
    a: str
    b: str
    overlap_low_hz: float
    overlap_high_hz: float
    overlap_width_hz: float
    frac_of_a: float
    frac_of_b: float
    jaccard: float


def band_overlap(a: FrequencyBand, b: FrequencyBand) -> BandOverlap:
    low = max(float(a.f_low_hz), float(b.f_low_hz))
    high = min(float(a.f_high_hz), float(b.f_high_hz))
    width = max(0.0, high - low)

    frac_a = width / a.width_hz if a.width_hz > 0 else 0.0
    frac_b = width / b.width_hz if b.width_hz > 0 else 0.0

    denom = a.width_hz + b.width_hz - width
    jacc = width / denom if denom > 0 else 0.0

    return BandOverlap(
        a=str(a.name),
        b=str(b.name),
        overlap_low_hz=float(low if width > 0 else 0.0),
        overlap_high_hz=float(high if width > 0 else 0.0),
        overlap_width_hz=float(width),
        frac_of_a=float(frac_a),
        frac_of_b=float(frac_b),
        jaccard=float(jacc),
    )


def thermal_frequency_scale_hz(*, T_K: float) -> float:
    """Return the thermal frequency scale f_T = k_B T / h.

    This is a *bookkeeping* helper. It does not model noise spectra; it provides
    a reference scale often used to distinguish quantum vs classical regimes.
    """

    if T_K <= 0:
        raise ValueError("T_K must be > 0")

    k_B = 1.380649e-23  # J/K
    h = 6.62607015e-34  # J*s
    return float(k_B * float(T_K) / h)


@dataclass(frozen=True)
class OVZPF01BrainZPFResonanceReport:
    schema: str
    config_tag: str
    temperature_K: float
    thermal_frequency_scale_hz: float
    eeg_bands: list[FrequencyBand]
    zpf_mode_bands: list[FrequencyBand]
    min_mode_overlap_fraction: float
    overlaps: list[BandOverlap]
    mode_best_matches: dict[str, str | None]
    mode_has_any_overlap: dict[str, bool]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        d = asdict(self)
        return d

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovzpf01_brain_zpf_resonance_audit(
    *,
    eeg_bands: list[FrequencyBand],
    zpf_mode_bands: list[FrequencyBand],
    temperature_K: float = 295.0,
    min_mode_overlap_fraction: float = 0.05,
    config_tag: str = "OV-ZPF-01_brain_zpf_resonance_v1",
) -> OVZPF01BrainZPFResonanceReport:
    """Compute overlap bookkeeping between EEG-like bands and candidate mode bands."""

    if min_mode_overlap_fraction < 0.0 or min_mode_overlap_fraction > 1.0:
        raise ValueError("min_mode_overlap_fraction must be in [0, 1]")

    if len(eeg_bands) == 0:
        raise ValueError("eeg_bands must be non-empty")
    if len(zpf_mode_bands) == 0:
        raise ValueError("zpf_mode_bands must be non-empty")

    f_T = thermal_frequency_scale_hz(T_K=float(temperature_K))

    overlaps: list[BandOverlap] = []
    # Compute all pair overlaps deterministically.
    for m in sorted(zpf_mode_bands, key=lambda x: (x.name.lower(), x.f_low_hz, x.f_high_hz)):
        for e in sorted(eeg_bands, key=lambda x: (x.name.lower(), x.f_low_hz, x.f_high_hz)):
            overlaps.append(band_overlap(m, e))

    # Pick a "best match" per mode by maximum overlap fraction of the mode.
    mode_best: dict[str, str | None] = {}
    mode_any: dict[str, bool] = {}

    for m in zpf_mode_bands:
        rel = [o for o in overlaps if o.a == m.name]
        rel_sorted = sorted(rel, key=lambda o: (-(o.frac_of_a), -(o.jaccard), o.b.lower()))
        best = rel_sorted[0] if rel_sorted else None
        if best is None or best.frac_of_a <= 0:
            mode_best[m.name] = None
            mode_any[m.name] = False
            continue

        mode_best[m.name] = best.b
        mode_any[m.name] = bool(best.frac_of_a >= float(min_mode_overlap_fraction))

    return OVZPF01BrainZPFResonanceReport(
        schema="OV-ZPF-01/brain_zpf_resonance_report/v1",
        config_tag=str(config_tag),
        temperature_K=float(temperature_K),
        thermal_frequency_scale_hz=float(f_T),
        eeg_bands=list(eeg_bands),
        zpf_mode_bands=list(zpf_mode_bands),
        min_mode_overlap_fraction=float(min_mode_overlap_fraction),
        overlaps=list(overlaps),
        mode_best_matches=dict(mode_best),
        mode_has_any_overlap=dict(mode_any),
    )


def default_demo_inputs() -> tuple[list[FrequencyBand], list[FrequencyBand]]:
    """Return canonical demo inputs.

    These are not asserted to be physically meaningful; they are chosen so that
    the overlap logic is non-trivial and testable.
    """

    eeg = [
        FrequencyBand(name="beta", f_low_hz=13.0, f_high_hz=30.0),
        FrequencyBand(name="gamma", f_low_hz=30.0, f_high_hz=80.0),
    ]

    # Narrow "candidate mode" bands centered near canonical beta/gamma subranges.
    modes = [
        FrequencyBand(name="zpf_mode_beta_candidate", f_low_hz=18.0, f_high_hz=22.0),
        FrequencyBand(name="zpf_mode_gamma_candidate", f_low_hz=38.0, f_high_hz=42.0),
    ]

    return eeg, modes


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-ZPF-01" / "brain_zpf_resonance.json"


def write_ovzpf01_brain_zpf_resonance_artifact(
    *,
    path: Path | None = None,
    temperature_K: float = 295.0,
    min_mode_overlap_fraction: float = 0.05,
) -> Path:
    eeg, modes = default_demo_inputs()
    rep = ovzpf01_brain_zpf_resonance_audit(
        eeg_bands=eeg,
        zpf_mode_bands=modes,
        temperature_K=float(temperature_K),
        min_mode_overlap_fraction=float(min_mode_overlap_fraction),
    )

    payload = {
        "schema": "OV-ZPF-01/brain_zpf_resonance_artifact/v1",
        "notes": (
            "Synthetic overlap demo only; not external evidence, not an anchoring claim, "
            "and not a physical feasibility determination."
        ),
        "inputs": {
            "temperature_K": float(temperature_K),
            "min_mode_overlap_fraction": float(min_mode_overlap_fraction),
            "eeg_bands": [asdict(b) for b in eeg],
            "zpf_mode_bands": [asdict(b) for b in modes],
        },
        "report": rep.to_jsonable(),
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
