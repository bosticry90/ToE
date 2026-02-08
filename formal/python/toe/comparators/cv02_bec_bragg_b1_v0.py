from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.comparators.cv01_bec_bragg_v0 import (
    cv01_compare_curved_fit,
    cv01_compare_linear_fit,
)
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D


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


def _default_artifact_dir(repo_root: Path) -> Path:
    return repo_root / "formal" / "external_evidence" / "bec_bragg_b1_second_dataset_TBD"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _as_sample_kw(raw_sample_kw: list[list[float]]) -> tuple[tuple[float, float], ...]:
    return tuple((float(k), float(w)) for (k, w) in raw_sample_kw)


def _load_dr01_linear(path: Path) -> DR01Fit1D:
    payload = _load_json(path)
    return DR01Fit1D(
        u=float(payload["u"]),
        c_s=float(payload["c_s"]),
        tag=str(payload.get("tag", "dr01_linear_artifact")),
        source_kind=str(payload.get("source_kind", "unknown")),
        source_ref=str(payload.get("source_ref", "unknown")),
        fit_method_tag=str(payload.get("fit_method_tag", "unspecified")),
        sample_kw=_as_sample_kw(payload["sample_kw"]),
        data_fingerprint=str(payload.get("data_fingerprint", "")),
    )


def _load_dr01_curved(path: Path) -> DR01FitCurved1D:
    payload = _load_json(path)
    return DR01FitCurved1D(
        u=float(payload["u"]),
        c0=float(payload["c0"]),
        beta=float(payload["beta"]),
        tag=str(payload.get("tag", "dr01_curved_artifact")),
        source_kind=str(payload.get("source_kind", "unknown")),
        source_ref=str(payload.get("source_ref", "unknown")),
        fit_method_tag=str(payload.get("fit_method_tag", "unspecified")),
        sample_kw=_as_sample_kw(payload["sample_kw"]),
        data_fingerprint=str(payload.get("data_fingerprint", "")),
    )


def cv02_compare_linear_fit(
    dr01_fit: DR01Fit1D,
    *,
    tol_metric_identity: float = 1e-12,
    tol_unit_gxx: float = 1e-12,
    tol_declared_speed: float = 1e-12,
) -> dict[str, Any]:
    return cv01_compare_linear_fit(
        dr01_fit,
        tol_metric_identity=float(tol_metric_identity),
        tol_unit_gxx=float(tol_unit_gxx),
        tol_declared_speed=float(tol_declared_speed),
    )


def cv02_compare_curved_fit(
    dr01_fit_curved: DR01FitCurved1D,
    *,
    tol_metric_identity: float = 1e-12,
    tol_unit_gxx: float = 1e-12,
    tol_declared_speed: float = 1e-12,
) -> dict[str, Any]:
    return cv01_compare_curved_fit(
        dr01_fit_curved,
        tol_metric_identity=float(tol_metric_identity),
        tol_unit_gxx=float(tol_unit_gxx),
        tol_declared_speed=float(tol_declared_speed),
    )


@dataclass(frozen=True)
class CV02BecBraggB1V0Record:
    schema: str
    date: str
    observable_id: str
    domain_id: str
    comparator_role: str
    status: dict[str, Any]
    inputs: dict[str, Any]
    rows: list[dict[str, Any]]
    summary: dict[str, Any]
    scope_limits: list[str]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "domain_id": str(self.domain_id),
            "comparator_role": str(self.comparator_role),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "rows": list(self.rows),
            "summary": dict(self.summary),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def cv02_bec_bragg_b1_v0_record(
    *,
    date: str = "2026-02-08",
    artifact_dir: Path | None = None,
    tol_metric_identity: float = 1e-12,
    tol_unit_gxx: float = 1e-12,
    tol_declared_speed: float = 1e-12,
) -> CV02BecBraggB1V0Record:
    repo_root = _find_repo_root(Path(__file__))
    data_dir = (artifact_dir or _default_artifact_dir(repo_root)).resolve()

    linear_path = data_dir / "dr01_fit_artifact.json"
    curved_path = data_dir / "dr01_fit_artifact_curved.json"

    missing = [str(p) for p in [linear_path, curved_path] if not p.exists()]
    if missing:
        return CV02BecBraggB1V0Record(
            schema="OV-CV-02_bec_bragg_b1_comparator/v1",
            date=str(date),
            observable_id="OV-CV-02",
            domain_id="DRBR-DOMAIN-02",
            comparator_role="integrity_only",
            status={
                "blocked": True,
                "reasons": ["missing_domain_artifacts"],
            },
            inputs={
                "artifact_dir": str(data_dir),
                "missing_artifacts": list(missing),
            },
            rows=[],
            summary={
                "counts": {"pass": 0, "fail": 0},
                "artifacts": {"pass": [], "fail": []},
            },
            scope_limits=["blocked_by_missing_inputs", "front_door_only"],
        )

    fit_linear = _load_dr01_linear(linear_path)
    fit_curved = _load_dr01_curved(curved_path)

    row_linear = cv02_compare_linear_fit(
        fit_linear,
        tol_metric_identity=tol_metric_identity,
        tol_unit_gxx=tol_unit_gxx,
        tol_declared_speed=tol_declared_speed,
    )
    row_curved = cv02_compare_curved_fit(
        fit_curved,
        tol_metric_identity=tol_metric_identity,
        tol_unit_gxx=tol_unit_gxx,
        tol_declared_speed=tol_declared_speed,
    )

    rows = [row_linear, row_curved]
    pass_ids = [str(r["artifact_id"]) for r in rows if bool(r["passed"])]
    fail_ids = [str(r["artifact_id"]) for r in rows if not bool(r["passed"])]

    return CV02BecBraggB1V0Record(
        schema="OV-CV-02_bec_bragg_b1_comparator/v1",
        date=str(date),
        observable_id="OV-CV-02",
        domain_id="DRBR-DOMAIN-02",
        comparator_role="integrity_only",
        status={
            "blocked": False,
            "reasons": [],
            "tolerances": {
                "metric_identity": float(tol_metric_identity),
                "unit_gxx": float(tol_unit_gxx),
                "declared_speed_match": float(tol_declared_speed),
            },
        },
        inputs={
            "artifact_dir": str(data_dir),
            "linear_artifact_path": str(linear_path),
            "curved_artifact_path": str(curved_path),
            "linear_data_fingerprint": fit_linear.data_fingerprint,
            "curved_data_fingerprint": fit_curved.data_fingerprint,
        },
        rows=rows,
        summary={
            "counts": {"pass": len(pass_ids), "fail": len(fail_ids)},
            "artifacts": {"pass": pass_ids, "fail": fail_ids},
        },
        scope_limits=[
            "front_door_only",
            "typed_artifacts_only",
            "deterministic_record_only",
            "integrity_only",
            "no_external_truth_claim",
        ],
    )


def render_cv02_lock_markdown(record: CV02BecBraggB1V0Record) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-CV-02 - BEC Bragg B1 Comparator v0 (front-door, deterministic)\n\n"
        "Scope / limits\n"
        "- Deterministic comparator record only\n"
        "- Typed DR-01 artifacts only (linear + curved)\n"
        "- Pass/fail rows carry explicit reason codes\n"
        "- No external truth claim\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )
