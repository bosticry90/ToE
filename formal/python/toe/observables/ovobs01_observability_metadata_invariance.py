"""OV-OBS-01: observability (representation) invariance audit.

Motivation
----------
Wavefunction/"state" unknowability is operationally enforced here as a simple rule:
*observable outputs must not depend on unobservable metadata*.

In this repository, a common risk is accidental coupling to provenance fields
(e.g., tags, source_ref strings) that should not affect computed quantities.

This module defines a small audit that checks that OV-01 observable outputs are
invariant under metadata-only perturbations of inputs.

Notes
-----
- This is a behavioral (Python) audit only.
- It does not create or enable any gate.
- It does not claim physical completeness; it is a hygiene/guardrail check.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from dataclasses import asdict

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.observables.ov01_observable import OV01ObservableReport, ov01_observable_residual_from
from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact


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


def _load_dr01_fit_from_json(path: Path) -> DR01Fit1D:
    d = json.loads(path.read_text(encoding="utf-8"))

    sample_kw = None
    if d.get("sample_kw") is not None:
        sample_kw = tuple((float(k), float(w)) for (k, w) in d["sample_kw"])

    return DR01Fit1D(
        u=float(d["u"]),
        c_s=float(d["c_s"]),
        tag=str(d.get("tag", path.name)),
        source_kind=str(d.get("source_kind", "unknown")),
        source_ref=d.get("source_ref", None),
        fit_method_tag=str(d.get("fit_method_tag", "unspecified")),
        data_fingerprint=d.get("data_fingerprint", None),
        sample_kw=sample_kw,
    )


@dataclass(frozen=True)
class OVOBS01ObservabilityMetadataInvarianceReport:
    schema: str
    config_tag: str

    fn_fingerprint_a: str
    fn_fingerprint_b: str
    dr_fingerprint_a: str
    dr_fingerprint_b: str

    report_a_fingerprint: str
    report_b_fingerprint: str

    obs_value_a: float
    obs_value_b: float
    residual_a: float
    residual_b: float

    ok_obs_value_equal: bool
    ok_residual_equal: bool

    def to_jsonable_without_fingerprint(self) -> dict[str, object]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, object]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def _clone_fn_with_new_metadata(fn: FN01Artifact1D) -> FN01Artifact1D:
    # params must remain identical; only metadata changes.
    return FN01Artifact1D.from_params(
        candidate_tag=fn.candidate_tag,
        term_kind=fn.term_kind,
        params=fn.params_dict(),
        source_kind=fn.source_kind,
        source_ref=("OV-OBS-01 metadata perturbation"),
        model_tag=(fn.model_tag + "/OV-OBS-01"),
    )


def _clone_dr_with_new_metadata(dr: DR01Fit1D) -> DR01Fit1D:
    return DR01Fit1D(
        u=float(dr.u),
        c_s=float(dr.c_s),
        tag=str(dr.tag) + "/OV-OBS-01",
        source_kind=str(dr.source_kind),
        source_ref=("OV-OBS-01 metadata perturbation"),
        fit_method_tag=str(dr.fit_method_tag),
        data_fingerprint=dr.data_fingerprint,
        sample_kw=dr.sample_kw,
    )


def ovobs01_metadata_invariance_audit(
    *,
    fn_artifact: FN01Artifact1D,
    dr_fit_artifact: DR01Fit1D,
    config_tag: str = "OV-OBS-01_metadata_invariance_v1",
) -> OVOBS01ObservabilityMetadataInvarianceReport:
    """Check OV-01 outputs are invariant to metadata-only input perturbations."""

    fn2 = _clone_fn_with_new_metadata(fn_artifact)
    dr2 = _clone_dr_with_new_metadata(dr_fit_artifact)

    r1: OV01ObservableReport = ov01_observable_residual_from(fn_artifact, dr_fit_artifact)
    r2: OV01ObservableReport = ov01_observable_residual_from(fn2, dr2)

    ok_obs = float(r1.obs_value) == float(r2.obs_value)
    ok_res = float(r1.residual) == float(r2.residual)

    return OVOBS01ObservabilityMetadataInvarianceReport(
        schema="OV-OBS-01/metadata_invariance_report/v1",
        config_tag=str(config_tag),
        fn_fingerprint_a=fn_artifact.fingerprint(),
        fn_fingerprint_b=fn2.fingerprint(),
        dr_fingerprint_a=dr_fit_artifact.fingerprint(),
        dr_fingerprint_b=dr2.fingerprint(),
        report_a_fingerprint=r1.fingerprint(),
        report_b_fingerprint=r2.fingerprint(),
        obs_value_a=float(r1.obs_value),
        obs_value_b=float(r2.obs_value),
        residual_a=float(r1.residual),
        residual_b=float(r2.residual),
        ok_obs_value_equal=bool(ok_obs),
        ok_residual_equal=bool(ok_res),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-OBS-01" / "metadata_invariance.json"


def write_ovobs01_metadata_invariance_artifact(*, path: Path | None = None) -> Path:
    """Write a canonical OV-OBS-01 diagnostic artifact.

    Uses the frozen DR-01 fit artifact and the promoted FN-01 P_cubic constructor.
    """

    repo_root = _find_repo_root(Path(__file__))
    dr_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_bragg_steinhauer_2001"
        / "dr01_fit_artifact.json"
    )
    dr = _load_dr01_fit_from_json(dr_path)
    fn = fn01_make_P_cubic_artifact(g=0.4)

    rec = ovobs01_metadata_invariance_audit(fn_artifact=fn, dr_fit_artifact=dr)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8")
    return out
