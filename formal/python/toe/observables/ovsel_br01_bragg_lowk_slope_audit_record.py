"""OV-SEL-BR-01: Bragg low-k slope audit / selection invariants (computed lock).

Purpose
- Provide a single, explicit governance/audit record for the Bragg lane that:
  - asserts OV-BR-03N digitization lock==computed and frozen artifacts exist
  - asserts OV-BR-04A/04B low-k slope locks==computed
  - pins the low-k window rule (rule id + parameters) used by the derived records
  - records why digitization is render-based (axis text is rasterized)

Scope / limits
- Bookkeeping / narrative only; no physics claim.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovbr03n_bragg_dispersion_k_omega_digitized import (
    ovbr03n_digitized_dispersion_record,
)
from formal.python.toe.observables.ovbr04a_bragg_lowk_slope_conditionA_record import (
    ovbr04a_bragg_lowk_slope_conditionA_record,
)
from formal.python.toe.observables.ovbr04b_bragg_lowk_slope_conditionB_record import (
    ovbr04b_bragg_lowk_slope_conditionB_record,
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


def _extract_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing record fingerprint line")
    return m.group(1)


def _check_lock_matches(*, repo_root: Path, lock_rel_path: str, computed_payload: dict[str, Any]) -> dict[str, Any]:
    p = repo_root / Path(lock_rel_path)
    text = p.read_text(encoding="utf-8")
    locked = _extract_json_block(text)
    fp = _extract_fingerprint(text)
    ok = bool(locked == computed_payload)
    return {
        "lock_path": str(lock_rel_path).replace("\\", "/"),
        "lock_fingerprint": str(fp),
        "ok": bool(ok),
    }


def _check_path_exists(*, repo_root: Path, rel_path: str) -> dict[str, Any]:
    p = repo_root / Path(rel_path)
    return {"path": str(rel_path).replace("\\", "/"), "exists": bool(p.exists())}


def _check_equals(*, label: str, expected: object, actual: object) -> dict[str, Any]:
    ok = expected == actual
    return {"label": str(label), "expected": expected, "actual": actual, "ok": bool(ok)}


@dataclass(frozen=True)
class OVSELBR01BraggLowKSlopeAuditRecord:
    schema: str
    status_date: str

    checks: dict[str, Any]
    narrative: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "checks": dict(self.checks),
            "narrative": str(self.narrative),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovsel_br01_bragg_lowk_slope_audit_record(*, status_date: str = "2026-01-25") -> OVSELBR01BraggLowKSlopeAuditRecord:
    repo_root = _find_repo_root(Path(__file__))

    br03n = ovbr03n_digitized_dispersion_record(date=str(status_date))
    br04a = ovbr04a_bragg_lowk_slope_conditionA_record(date=str(status_date))
    br04b = ovbr04b_bragg_lowk_slope_conditionB_record(date=str(status_date))

    meta_relpath = (
        "formal/external_evidence/bec_bragg_shammass_2012/ovbr03n_digitization/k_omega_digitization.metadata.json"
    )

    checks: dict[str, Any] = {
        "OV-BR-03N": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md",
            computed_payload=br03n.to_jsonable(),
        ),
        "OV-BR-04A": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
            computed_payload=br04a.to_jsonable(),
        ),
        "OV-BR-04B": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md",
            computed_payload=br04b.to_jsonable(),
        ),
        "OV-BR-03N condition_A CSV exists": _check_path_exists(
            repo_root=repo_root, rel_path=str(br03n.dataset["condition_A"]["csv_relpath"])
        ),
        "OV-BR-03N condition_B CSV exists": _check_path_exists(
            repo_root=repo_root, rel_path=str(br03n.dataset["condition_B"]["csv_relpath"])
        ),
        "OV-BR-03N source PDF exists": _check_path_exists(
            repo_root=repo_root, rel_path=str(br03n.source["pdf_relpath"])
        ),
        "OV-BR-03N source PNG exists": _check_path_exists(
            repo_root=repo_root, rel_path=str(br03n.source["png_relpath"])
        ),
        "OV-BR-03N metadata exists": _check_path_exists(
            repo_root=repo_root, rel_path=str(meta_relpath)
        ),
        "lowk_window_v1 params (A)": _check_equals(
            label="selection_parameters",
            expected={
                "k_um_inv_max": 1.0,
                "omega_over_2pi_kHz_min": 0.1,
                "omega_over_2pi_kHz_max": 1.3,
            },
            actual=br04a.selection.get("parameters"),
        ),
        "lowk_window_v1 params (B)": _check_equals(
            label="selection_parameters",
            expected={
                "k_um_inv_max": 1.0,
                "omega_over_2pi_kHz_min": 0.1,
                "omega_over_2pi_kHz_max": 1.3,
            },
            actual=br04b.selection.get("parameters"),
        ),
    }

    all_ok = all(bool(v.get("ok", True)) for v in checks.values() if isinstance(v, dict)) and all(
        bool(v.get("exists", True)) for v in checks.values() if isinstance(v, dict)
    )

    narrative = (
        "Bragg low-k slope audit (bookkeeping-only; no physics claim):\n"
        f"0) External anchor: {br03n.source['pdf_relpath']} (sha256={br03n.source['pdf_sha256']}).\n"
        "1) OV-BR-03N digitization is render-based (axis text is rasterized), so provenance is pinned to a deterministic PNG render.\n"
        "2) OV-BR-04A/04B derive low-k slopes using lowk_window_v1 (k<=1.0, 0.1<=omega<=1.3) and pinned OLS slope rules.\n"
        "3) Governance posture: lock==computed for OV-BR-03N and OV-BR-04A/04B; frozen artifacts must exist; selection parameters are pinned.\n"
        f"\nSelf-checks all_ok={bool(all_ok)}."
    )

    return OVSELBR01BraggLowKSlopeAuditRecord(
        schema="OV-SEL-BR-01_bragg_lowk_slope_audit/v1",
        status_date=str(status_date),
        checks=checks,
        narrative=narrative,
    )


def render_ovsel_br01_lock_markdown(record: OVSELBR01BraggLowKSlopeAuditRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-BR-01 — Bragg low-k slope audit (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- Pins selection rule + asserts lock==computed for Bragg digitization and derived slope records\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsel_br01_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-25") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-SEL-BR-01_bragg_lowk_slope_audit.md"
        )

    rec = ovsel_br01_bragg_lowk_slope_audit_record(status_date=str(status_date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsel_br01_lock_markdown(rec), encoding="utf-8")
    return out
