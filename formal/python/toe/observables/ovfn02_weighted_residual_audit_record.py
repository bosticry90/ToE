"""OV-FN-02: weighted residual audit (consumes selected weight policy).

Purpose
- Consume the FN-01 cross-fit metric residual lock and the selected FN weight
  policy (OV-FN-WT-02), then record a deterministic, declared-weight score.
- This record exists to propagate eliminations into a downstream reported choice.

Scope / limits
- Bookkeeping / audit only; no physics claim.
- Numeric use is limited to applying a declared scalar weight to a locked scalar.
- May be BLOCKED by admissibility manifest (CT01/SYM01/CAUS01).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from formal.python.toe.constraints.admissibility_manifest import check_required_gates


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


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


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing record fingerprint line")
    return m.group(1)


def _extract_fn01_r_metric(md_text: str) -> float | None:
    m = re.search(r"^\s*-\s*R_metric\s*=\s*([0-9eE+\-\.]+)\s*$", md_text, flags=re.MULTILINE)
    if m is None:
        return None
    try:
        return float(m.group(1))
    except ValueError:
        return None


def _format_float_stable(x: float | None) -> str | None:
    if x is None:
        return None
    try:
        return format(float(x), ".12g")
    except Exception:  # noqa: BLE001
        return None


def _fn_residual_semantic_digest(*, r_metric: float | None) -> str | None:
    """Stable semantic digest for the FN residual.

    Intentionally binds only to the semantic scalar(s) we explicitly consume.
    """

    if r_metric is None:
        return None
    payload = {
        "source": "FN-01_cross_fit_metric_residual_DR02_DR03",
        "r_metric": _format_float_stable(r_metric),
    }
    return _sha256_json(payload)


@dataclass(frozen=True)
class OVFN02WeightedResidualAuditRecord:
    schema: str
    date: str

    observable_id: str
    status: dict[str, Any]

    inputs: dict[str, Any]
    audit: dict[str, Any]

    scope_limits: list[str]

    def fingerprint_payload(self) -> dict[str, Any]:
        """Stable payload for fingerprinting.

        Critical rule: the fingerprint must not depend on upstream lock paths or
        upstream lock fingerprints (those may include paths). It binds only to:
        - FN residual semantic digest (reduced)
        - selected policy id + policy parameters (w_fn, max_score, br_candidate_id)
        - computed weighted score + threshold outcome
        - admissibility manifest sha/version (not path)
        """

        status = dict(self.status)
        adm = dict(status.get("admissibility_manifest") or {})
        adm.pop("path", None)
        status["admissibility_manifest"] = adm

        reasons = status.get("reasons")
        reasons_sorted = sorted([str(x) for x in reasons]) if isinstance(reasons, list) else []

        required = status.get("required_gates")
        required_sorted = sorted([str(x) for x in required]) if isinstance(required, list) else []

        audit = dict(self.audit)
        r_metric_f: float | None
        try:
            r_metric_f = float(audit.get("r_metric")) if audit.get("r_metric") is not None else None
        except Exception:  # noqa: BLE001
            r_metric_f = None

        r_metric_s = _format_float_stable(r_metric_f)
        w_fn_s = _format_float_stable(audit.get("w_fn"))
        max_score_s = _format_float_stable(audit.get("max_score"))
        weighted_score_s = _format_float_stable(audit.get("weighted_score"))
        br_candidate_id = audit.get("br_candidate_id")

        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "blocked": bool(status.get("blocked")),
            "required_gates": required_sorted,
            "reasons": reasons_sorted,
            "admissibility_manifest": {
                "sha256": adm.get("sha256"),
                "version": adm.get("version"),
            },
            "fn_residual": {
                "r_metric": r_metric_s,
                "semantic_digest": _fn_residual_semantic_digest(r_metric=r_metric_f),
            },
            "selected_policy": {
                "selected_policy_id": audit.get("selected_policy_id"),
                "w_fn": w_fn_s,
                "max_score": max_score_s,
                "br_candidate_id": br_candidate_id,
            },
            "audit": {
                "weighted_score": weighted_score_s,
                "within_threshold": audit.get("within_threshold"),
            },
            "scope_limits": list(self.scope_limits),
        }

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "date": str(self.date),
            "observable_id": str(self.observable_id),
            "status": dict(self.status),
            "inputs": dict(self.inputs),
            "audit": dict(self.audit),
            "scope_limits": list(self.scope_limits),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.fingerprint_payload())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovfn02_weighted_residual_audit_record(
    *,
    date: str = "2026-01-25",
    residual_lock_path: Path | None = None,
    selection_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> OVFN02WeightedResidualAuditRecord:
    repo_root = _find_repo_root(Path(__file__))

    default_residual = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "functionals"
        / "FN-01_cross_fit_metric_residual_DR02_DR03.md"
    )
    residual_path = (residual_lock_path or default_residual).resolve()

    default_sel = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-FN-WT-02_selected_weight_policy.md"
    )
    sel_path = (selection_lock_path or default_sel).resolve()

    if not residual_path.exists():
        status: dict[str, Any] = {
            "blocked": True,
            "reasons": ["missing_input_lock_FN-01_cross_fit_metric_residual_DR02_DR03"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {"path": None, "version": None, "skipped": True},
        }
        return OVFN02WeightedResidualAuditRecord(
            schema="OV-FN-02_weighted_residual_audit/v1",
            date=str(date),
            observable_id="OV-FN-02",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": False,
                }
            },
            audit={
                "selected_policy_id": None,
                "computed_under_blocked_admissibility": True,
                "reason_codes": ["missing_input_lock"],
            },
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    if not sel_path.exists():
        status = {
            "blocked": True,
            "reasons": ["missing_input_lock_OV-FN-WT-02"],
            "required_gates": ["CT01", "SYM01", "CAUS01"],
            "admissibility_manifest": {"path": None, "version": None, "skipped": True},
        }
        return OVFN02WeightedResidualAuditRecord(
            schema="OV-FN-02_weighted_residual_audit/v1",
            date=str(date),
            observable_id="OV-FN-02",
            status=status,
            inputs={
                "FN-01_cross_fit_metric_residual_DR02_DR03": {
                    "expected_path": str(default_residual),
                    "path": str(residual_path),
                    "present": True,
                },
                "OV-FN-WT-02": {
                    "expected_path": str(default_sel),
                    "path": str(sel_path),
                    "present": False,
                },
            },
            audit={
                "selected_policy_id": None,
                "computed_under_blocked_admissibility": True,
                "reason_codes": ["missing_input_lock"],
            },
            scope_limits=["blocked_by_missing_input_lock", "blocked_by_default"],
        )

    required_gates = ["CT01", "SYM01", "CAUS01"]
    gate_check = check_required_gates(
        repo_root=repo_root,
        required_gate_ids=required_gates,
        manifest_path=admissibility_manifest_path,
    )

    status: dict[str, Any] = {
        "blocked": bool(gate_check.blocked),
        "reasons": list(gate_check.reasons),
        "required_gates": list(required_gates),
        "admissibility_manifest": {
            "path": str(gate_check.manifest_path),
            "version": gate_check.manifest_version,
            "sha256": gate_check.manifest_sha256,
        },
    }

    residual_text = residual_path.read_text(encoding="utf-8")
    residual_sha = _sha256_text(residual_text)
    r_metric = _extract_fn01_r_metric(residual_text)

    sel_text = sel_path.read_text(encoding="utf-8")
    sel_locked = _extract_json_block(sel_text)
    sel_fp = _extract_record_fingerprint(sel_text)

    if bool((sel_locked.get("status") or {}).get("blocked")):
        status["blocked"] = True
        status["reasons"].append("input_OV-FN-WT-02_is_blocked")

    selection = dict(sel_locked.get("selection") or {})
    selected_policy_id = selection.get("selected_policy_id")
    selected_row = selection.get("selected_row")

    reason_codes: list[str] = []

    if r_metric is None:
        status["blocked"] = True
        status["reasons"].append("fn01_residual_lock_missing_R_metric")
        reason_codes.append("missing_R_metric")

    if not isinstance(selected_policy_id, str) or not selected_policy_id:
        status["blocked"] = True
        status["reasons"].append("missing_selected_policy_id")
        reason_codes.append("missing_selected_policy")


    w_fn: float | None = None
    max_score: float | None = None
    br_candidate_id: str | None = None
    if isinstance(selected_row, dict):
        try:
            w_fn = float(selected_row.get("w_fn"))
            max_score = float(selected_row.get("max_score"))
            br_candidate_id = selected_row.get("br_candidate_id")
        except Exception:  # noqa: BLE001
            w_fn = None
            max_score = None
            br_candidate_id = None

    if w_fn is None or max_score is None:
        status["blocked"] = True
        status["reasons"].append("selected_row_missing_weight_fields")
        reason_codes.append("missing_selected_row_fields")

    weighted_score: float | None = None
    within_threshold: bool | None = None
    if r_metric is not None and w_fn is not None and max_score is not None:
        weighted_score = float(r_metric) * float(w_fn)
        within_threshold = bool(weighted_score <= float(max_score) + 0.0)
        reason_codes.append("weighted_score_computed")

    computed_under_blocked_admissibility = bool(status.get("blocked"))
    if computed_under_blocked_admissibility and "computed_under_blocked_admissibility" not in reason_codes:
        reason_codes.append("computed_under_blocked_admissibility")

    inputs = {
        "FN-01_cross_fit_metric_residual_DR02_DR03": {
            "path": str(residual_path),
            "present": True,
            "sha256": str(residual_sha),
            "r_metric": float(r_metric) if r_metric is not None else None,
        },
        "OV-FN-WT-02": {
            "path": str(sel_path),
            "schema": str(sel_locked.get("schema")),
            "locked_fingerprint": str(sel_fp),
            "record_fingerprint": str(sel_locked.get("fingerprint")),
            "present": True,
        },
    }

    audit = {
        "selected_policy_id": str(selected_policy_id) if isinstance(selected_policy_id, str) else None,
        "br_candidate_id": br_candidate_id,
        "w_fn": float(w_fn) if w_fn is not None else None,
        "max_score": float(max_score) if max_score is not None else None,
        "r_metric": float(r_metric) if r_metric is not None else None,
        "weighted_score": float(weighted_score) if weighted_score is not None else None,
        "within_threshold": bool(within_threshold) if within_threshold is not None else None,
        "computed_under_blocked_admissibility": bool(computed_under_blocked_admissibility),
        "reason_codes": reason_codes,
    }

    return OVFN02WeightedResidualAuditRecord(
        schema="OV-FN-02_weighted_residual_audit/v1",
        date=str(date),
        observable_id="OV-FN-02",
        status=status,
        inputs=inputs,
        audit=audit,
        scope_limits=[
            "audit_only",
            "declared_weight_application_only",
            "lock_derived",
            "no_new_claims",
        ],
    )


def render_ovfn02_lock_markdown(record: OVFN02WeightedResidualAuditRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-FN-02 - Weighted residual audit (computed)\n\n"
        "Scope / limits\n"
        "- Audit-only bookkeeping; no physics claim\n"
        "- Applies declared weights to a locked scalar residual\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovfn02_lock(
    *,
    lock_path: Path | None = None,
    date: str = "2026-01-25",
    residual_lock_path: Path | None = None,
    selection_lock_path: Path | None = None,
    admissibility_manifest_path: Path | None = None,
) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-FN-02_weighted_residual_audit.md"
        )

    rec = ovfn02_weighted_residual_audit_record(
        date=str(date),
        residual_lock_path=residual_lock_path,
        selection_lock_path=selection_lock_path,
        admissibility_manifest_path=admissibility_manifest_path,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovfn02_lock_markdown(rec), encoding="utf-8")
    return out
