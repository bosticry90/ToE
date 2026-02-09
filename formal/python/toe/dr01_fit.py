"""DR-01 fit artifacts (public surface).

This module defines the canonical *fit object* type consumed by bridges such as BR-01.

Notes
-----
- DR-01 is a dispersion-structure criterion. This file provides a minimal, typed
  artifact used to pass dispersion-fit parameters through the bridge layer.
- Keep this stable: downstream code should depend on this object rather than
  re-introducing ad-hoc surrogate tuples.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from typing import Iterable, Literal


@dataclass(frozen=True)
class DR01Fit1D:
    """Minimal 1D DR-01 dispersion-fit artifact.

    Interpreted as an effective dispersion of the form:
        ω(k) = u*k + c_s*|k|

    This is a *fit artifact* (parameters + a stable identifier), not a full solver.
    """

    u: float
    c_s: float

    # Human-friendly identifier used in tests/locks.
    tag: str = "synthetic"

    # Minimal provenance payload (no filesystem reads required).
    source_kind: Literal["csv", "manual", "synthetic", "unknown"] = "unknown"
    source_ref: str | None = None

    # Hash of underlying data used to fit (content-based).
    # Preferred semantics: sha256 hash of a canonical (k, ω) sample.
    data_fingerprint: str | None = None
    sample_kw: tuple[tuple[float, float], ...] | None = None

    # Fit implementation tag (for provenance; does not change scientific surface).
    fit_method_tag: str = "unspecified"

    @staticmethod
    def _canonical_sample_bytes(sample_kw: Iterable[tuple[float, float]]) -> bytes:
      # Canonical encoding:
      # - sort by k, then ω
      # - format floats with a stable representation
      # - one pair per line
      items = [(float(k), float(w)) for (k, w) in sample_kw]
      items.sort(key=lambda t: (t[0], t[1]))
      lines = [f"{k:.17g},{w:.17g}" for (k, w) in items]
      return ("\n".join(lines) + "\n").encode("utf-8")

    @classmethod
    def data_fingerprint_from_sample(cls, sample_kw: Iterable[tuple[float, float]]) -> str:
      payload = cls._canonical_sample_bytes(sample_kw)
      return hashlib.sha256(payload).hexdigest()

    def __post_init__(self) -> None:
      if self.sample_kw is not None and self.data_fingerprint is None:
        object.__setattr__(self, "data_fingerprint", self.data_fingerprint_from_sample(self.sample_kw))

    def omega(self, k: float) -> float:
        return float(self.u * k + self.c_s * abs(k))

    def fingerprint(self) -> str:
        # Stable, deterministic string for guardrail assertions.
      dfp = self.data_fingerprint if self.data_fingerprint is not None else "none"
      src = self.source_ref if self.source_ref is not None else "none"
      return (
        f"{self.tag}"
        f"|u={float(self.u):.16g}"
        f"|c_s={float(self.c_s):.16g}"
        f"|source_kind={self.source_kind}"
        f"|source_ref={src}"
        f"|fit_method={self.fit_method_tag}"
        f"|data_fingerprint={dfp}"
      )
