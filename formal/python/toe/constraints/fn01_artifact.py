"""FN-01 artifacts (public surface).

This module defines the canonical, provenance-stamped *artifact* type used to
reference an FN-01 deformation candidate without importing candidate code.

Notes
-----
- This is intentionally a small, stable surface.
- It does not evaluate the deformation; it only carries an identifier, params,
  provenance, and a deterministic fingerprint.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Iterable, Literal


SourceKind = Literal["manual", "csv", "synthetic", "unknown"]


def _canonicalize_params(params: dict[str, float] | Iterable[tuple[str, float]]) -> tuple[tuple[str, float], ...]:
    items = list(params.items()) if isinstance(params, dict) else list(params)
    normalized: list[tuple[str, float]] = [(str(k), float(v)) for (k, v) in items]
    normalized.sort(key=lambda kv: kv[0])

    keys = [k for (k, _v) in normalized]
    if len(keys) != len(set(keys)):
        raise ValueError("params keys must be unique")

    return tuple(normalized)


def _sha256_json(payload: object) -> str:
    # Canonical encoding: sorted keys, compact separators, ASCII-only output.
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class FN01Artifact1D:
    """Provenance-stamped FN-01 artifact.

    This represents a specific FN-01 candidate choice plus parameterization.

    Fields
    ------
    candidate_tag:
        Named candidate token (e.g. "P_cubic").
    term_kind:
        Human-readable classification of the term (e.g. "nonlinear_pressure_polynomial").
    params:
        Canonical (sorted) parameter pairs.
    source_kind/source_ref/model_tag:
        Minimal provenance payload.
    """

    candidate_tag: str
    term_kind: str
    params: tuple[tuple[str, float], ...]

    source_kind: SourceKind
    source_ref: str | None
    model_tag: str = "unspecified"

    @classmethod
    def from_params(
        cls,
        *,
        candidate_tag: str,
        term_kind: str,
        params: dict[str, float] | Iterable[tuple[str, float]],
        source_kind: SourceKind,
        source_ref: str | None,
        model_tag: str = "unspecified",
    ) -> "FN01Artifact1D":
        return cls(
            candidate_tag=str(candidate_tag),
            term_kind=str(term_kind),
            params=_canonicalize_params(params),
            source_kind=source_kind,
            source_ref=source_ref,
            model_tag=str(model_tag),
        )

    def params_dict(self) -> dict[str, float]:
        return {k: float(v) for (k, v) in self.params}

    def fingerprint(self) -> str:
        src = self.source_ref if self.source_ref is not None else "none"
        payload = {
            "candidate_tag": self.candidate_tag,
            "term_kind": self.term_kind,
            "params": [[k, float(v)] for (k, v) in self.params],
            "source_kind": self.source_kind,
            "source_ref": src,
            "model_tag": self.model_tag,
        }
        return _sha256_json(payload)


def fn01_make_P_cubic_artifact(
    *,
    g: float = 0.3,
    source_kind: SourceKind = "manual",
    source_ref: str | None = "FN-01k promotion: P_cubic artifact (2026-01-17)",
    model_tag: str = "P_cubic",
    term_kind: str = "nonlinear_pressure_polynomial",
) -> FN01Artifact1D:
    """Canonical constructor for the promoted FN-01 survivor P_cubic.

    This is a front-door constructor that does not import any test-only
    candidate modules.
    """

    return FN01Artifact1D.from_params(
        candidate_tag="P_cubic",
        term_kind=term_kind,
        params={"g": float(g)},
        source_kind=source_kind,
        source_ref=source_ref,
        model_tag=model_tag,
    )


def fn01_make_P_cubic_structural_fail_artifact(
    *,
    g: float = 0.3,
    source_kind: SourceKind = "manual",
    source_ref: str | None = "FN-01k structural-fail probe artifact (2026-01-27)",
    model_tag: str = "P_cubic_structural_fail",
    term_kind: str = "nonlinear_pressure_polynomial",
) -> FN01Artifact1D:
    """Companion FN artifact constructor intended to fail structural predicates.

    This exists only to demonstrate/lock discriminative pruning behavior for the
    BR→FN stage without adding any numeric interpretation.
    """

    return FN01Artifact1D.from_params(
        candidate_tag="P_cubic_structural_fail",
        term_kind=term_kind,
        params={"g": float(g)},
        source_kind=source_kind,
        source_ref=source_ref,
        model_tag=model_tag,
    )
