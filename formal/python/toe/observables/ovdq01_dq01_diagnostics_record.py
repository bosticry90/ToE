"""OV-DQ-01: deterministic DQ-01_v1 audit/diagnostic record.

Purpose
- Make DQ-01_v1 auditability first-class without changing the selection policy.
- Record (deterministically) the curved-fit adequacy metrics/reason codes per
  window for the external datasets currently in use (OV-04x DS-02 and OV-03x B1).
- Record the robustness gate summary fields (q_ratio, thresholds, etc.) and the
  policy-defined failure reasons.

Scope / limits
- Diagnostic/bookkeeping record only; no physics claim.
- No continuity claim; no averaging across regimes.
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
from typing import Any

from formal.python.toe.dr01_fit_adequacy import dr01_check_curved_fit_adequacy
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import (
    OV01FitFamilyRobustnessReport,
    ov01_fit_family_robustness_failure_reasons,
)


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
    m = re.search(r"(?:Report|Record) fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing fingerprint line")
    return m.group(1)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_dr01_fit_curved_from_json(path: Path) -> DR01FitCurved1D:
    d = _load_json(path)

    sample_kw = None
    if d.get("sample_kw") is not None:
        sample_kw = tuple((float(k), float(w)) for (k, w) in d["sample_kw"])

    fq = None
    if d.get("fit_quality") is not None:
        q = d["fit_quality"]
        fq = DR01FitQualityCurved1D(
            n_points=int(q["n_points"]),
            rmse_omega_over_k_m_per_s=float(q["rmse_omega_over_k_m_per_s"]),
            c0_stderr_m_per_s=float(q["c0_stderr_m_per_s"]),
            beta_stderr_s_per_m2=float(q["beta_stderr_s_per_m2"]),
            r2_y_space=float(q["r2_y_space"]),
        )

    return DR01FitCurved1D(
        u=float(d["u"]),
        c0=float(d["c0"]),
        beta=float(d["beta"]),
        tag=str(d.get("tag", path.name)),
        source_kind=str(d.get("source_kind", "unknown")),
        source_ref=d.get("source_ref", None),
        data_fingerprint=d.get("data_fingerprint", None),
        sample_kw=sample_kw,
        fit_method_tag=str(d.get("fit_method_tag", "unspecified")),
        fit_quality=fq,
        fit_quality_fingerprint=d.get("fit_quality_fingerprint", None),
    )


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


def _load_robustness_report_from_lock(*, repo_root: Path, lock_rel_path: str) -> tuple[OV01FitFamilyRobustnessReport, str]:
    path = repo_root / Path(lock_rel_path)
    text = path.read_text(encoding="utf-8")
    payload = _extract_json_block(text)
    fp = _extract_report_fingerprint(text)
    return _report_from_lock_payload(payload), str(fp)


def _dq01_window_diagnostics(*, repo_root: Path, curved_paths: list[Path], policy: str) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for p in curved_paths:
        fit = _load_dr01_fit_curved_from_json(p)
        adequacy = dr01_check_curved_fit_adequacy(fit, policy=str(policy))
        out.append(
            {
                "path": p.as_posix(),
                "tag": str(getattr(fit, "tag", "")),
                "data_fingerprint": fit.data_fingerprint,
                "fit_quality": None
                if fit.fit_quality is None
                else {
                    "n_points": int(fit.fit_quality.n_points),
                    "rmse_omega_over_k_m_per_s": float(fit.fit_quality.rmse_omega_over_k_m_per_s),
                    "c0_stderr_m_per_s": float(fit.fit_quality.c0_stderr_m_per_s),
                    "beta_stderr_s_per_m2": float(fit.fit_quality.beta_stderr_s_per_m2),
                    "r2_y_space": float(fit.fit_quality.r2_y_space),
                },
                "dq01": {
                    "passes": bool(adequacy.passes),
                    "reason_codes": list(adequacy.reason_codes),
                    "metrics": {k: float(v) for (k, v) in sorted(adequacy.metrics.items())},
                    "input_fingerprint": str(adequacy.input_fingerprint),
                    "fingerprint": adequacy.fingerprint(),
                },
            }
        )
    return out


def _adequacy_summary(*, curved_windows: list[dict[str, Any]]) -> dict[str, Any]:
    # DQ-01_v1 aggregation semantics as used by OV-01g/OV-03x/OV-04x:
    # all curved windows must pass for curved_adequacy_passes=True.
    passes = [bool(w["dq01"]["passes"]) for w in curved_windows]
    tags = [str(w.get("tag", "")) for w in curved_windows]
    fail_tags = [t for (t, ok) in zip(tags, passes, strict=True) if not ok]
    return {
        "adequacy_aggregation": "all_windows",
        "n_windows": int(len(curved_windows)),
        "n_pass": int(sum(1 for ok in passes if ok)),
        "n_fail": int(sum(1 for ok in passes if not ok)),
        "fail_tags": fail_tags,
    }


@dataclass(frozen=True)
class OVDQ01DQ01DiagnosticsRecord:
    schema: str
    adequacy_policy: str

    ov04x: dict[str, Any]
    ov03x: dict[str, Any]

    notes: str
    provenance: dict[str, Any]

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "adequacy_policy": str(self.adequacy_policy),
            "ov04x": self.ov04x,
            "ov03x": self.ov03x,
            "notes": str(self.notes),
            "provenance": self.provenance,
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable())


def ovdq01_dq01_diagnostics_record(*, adequacy_policy: str = "DQ-01_v1") -> OVDQ01DQ01DiagnosticsRecord:
    repo_root = _find_repo_root(Path(__file__))
    pol = str(adequacy_policy)

    # Load robustness reports from canonical locks (authoritative for summary values).
    rep04, fp04 = _load_robustness_report_from_lock(
        repo_root=repo_root,
        lock_rel_path="formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
    )
    rep03, fp03 = _load_robustness_report_from_lock(
        repo_root=repo_root,
        lock_rel_path="formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
    )

    # Per-window curved adequacy details from frozen artifacts.
    ds02_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_ds02_lowk_dataset_TBD"
    b1_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_b1_second_dataset_TBD"

    ds02_curved = [
        ds02_dir / "dr01_fit_artifact_curved.json",
        ds02_dir / "dr03_fit_artifact_curved.json",
        ds02_dir / "dr04d_fit_artifact_curved.json",
        ds02_dir / "dr05_fit_artifact_curved.json",
    ]
    b1_curved = [
        b1_dir / "dr01_fit_artifact_curved.json",
        b1_dir / "dr03_fit_artifact_curved.json",
        b1_dir / "dr04d_fit_artifact_curved.json",
        b1_dir / "dr05_fit_artifact_curved.json",
    ]

    ov04x = {
        "observable_id": "OV-04x",
        "robustness_report_fingerprint": fp04,
        "prefer_curved": bool(rep04.prefer_curved),
        "robustness_failed": bool(rep04.robustness_failed),
        "curved_adequacy_passes": bool(rep04.curved_adequacy_passes),
        "q_ratio": float(rep04.q_ratio),
        "q_threshold": float(rep04.q_threshold),
        "r_max_linear": float(rep04.r_max_linear),
        "r_max_curved": float(rep04.r_max_curved),
        "failure_reasons": list(ov01_fit_family_robustness_failure_reasons(rep04)),
    }

    ov04x["curved_windows"] = _dq01_window_diagnostics(repo_root=repo_root, curved_paths=ds02_curved, policy=pol)
    ov04x["curved_adequacy_summary"] = _adequacy_summary(curved_windows=list(ov04x["curved_windows"]))

    ov03x = {
        "observable_id": "OV-03x",
        "robustness_report_fingerprint": fp03,
        "prefer_curved": bool(rep03.prefer_curved),
        "robustness_failed": bool(rep03.robustness_failed),
        "curved_adequacy_passes": bool(rep03.curved_adequacy_passes),
        "q_ratio": float(rep03.q_ratio),
        "q_threshold": float(rep03.q_threshold),
        "r_max_linear": float(rep03.r_max_linear),
        "r_max_curved": float(rep03.r_max_curved),
        "failure_reasons": list(ov01_fit_family_robustness_failure_reasons(rep03)),
    }

    ov03x["curved_windows"] = _dq01_window_diagnostics(repo_root=repo_root, curved_paths=b1_curved, policy=pol)
    ov03x["curved_adequacy_summary"] = _adequacy_summary(curved_windows=list(ov03x["curved_windows"]))

    provenance: dict[str, Any] = {
        "robustness_locks": {
            "ov04x": "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
            "ov03x": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
        },
        "curved_artifacts": {
            "ov04x": [p.as_posix() for p in ds02_curved],
            "ov03x": [p.as_posix() for p in b1_curved],
        },
    }

    return OVDQ01DQ01DiagnosticsRecord(
        schema="OV-DQ-01/v1",
        adequacy_policy=pol,
        ov04x=ov04x,
        ov03x=ov03x,
        notes=(
            "Deterministic diagnostic record for DQ-01 curved-fit adequacy and OV robustness summaries. "
            "Bookkeeping only; no physics claim; no continuity claim; β not inferred / β-null posture."
        ),
        provenance=provenance,
    )


def render_ovdq01_lock_markdown(record: OVDQ01DQ01DiagnosticsRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-DQ-01 — DQ-01_v1 diagnostic record (computed)\n\n"
        "Scope / limits\n"
        "- Diagnostic/bookkeeping record only; no physics claim\n"
        "- No continuity claim; no averaging across regimes\n"
        "- β not inferred / β-null posture\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovdq01_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    rec = ovdq01_dq01_diagnostics_record()

    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-DQ-01_dq01_diagnostics_record.md"
        )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovdq01_lock_markdown(rec), encoding="utf-8")
    return out
