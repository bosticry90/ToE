"""OV-SEL-SND-04: density dependence lane audit (computed lock).

Purpose
- Audit that adding SND-DIG-01 + OV-SND-03N (density digitization) and OV-SND-03
  (density-scaled derived observable) does not trigger unintended policy/regime/
  selection consequences.

Design
- Deterministic.
- Checks:
  - SND-DIG-01 policy lock is lock==computed.
  - OV-SND-01, OV-SND-01N, OV-SND-02 locks remain lock==computed.
  - OV-SND-03N lock is lock==computed; its artifacts exist.
  - OV-SND-03 lock is lock==computed.
  - Canonical governance locks remain lock==computed (OV-SEL-01/02, OV-DQ-03).
  - Negative checks: governance/selection locks do not reference OV-SND-03 or OV-SND-03N.

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

from formal.python.toe.observables.ovdq03_dq01_active_policy_activation_record import (
    ovdq03_dq01_active_policy_activation_record,
)
from formal.python.toe.observables.ovsel01_selection_status_record import ovsel01_selection_status_record
from formal.python.toe.observables.ovsel02_selection_status_record import ovsel02_selection_status_record
from formal.python.toe.observables.snddig01_minimal_density_digitization_record import (
    snddig01_minimal_density_digitization_record,
)
from formal.python.toe.observables.ovsnd01_sound_propagation_distance_time_digitized import (
    ovsnd01_digitized_propagation_dataset_record,
)
from formal.python.toe.observables.ovsnd01_sound_speed_scaling_record import ovsnd01_sound_speed_scaling_record
from formal.python.toe.observables.ovsnd02_sound_speed_from_propagation_record import (
    ovsnd02_sound_speed_from_propagation_record,
)
from formal.python.toe.observables.ovsnd03n_central_density_digitized import (
    ovsnd03n_central_density_digitized_record,
)
from formal.python.toe.observables.ovsnd03_sound_speed_density_scaling_record import (
    ovsnd03_sound_speed_density_scaling_record,
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


def _check_no_token(*, repo_root: Path, lock_rel_path: str, token: str) -> dict[str, Any]:
    p = repo_root / Path(lock_rel_path)
    text = p.read_text(encoding="utf-8")
    ok = token not in text
    return {"lock_path": str(lock_rel_path).replace("\\", "/"), "token": token, "ok": bool(ok)}


@dataclass(frozen=True)
class OVSELSND04DensityDependenceAuditRecord:
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


def ovsel_snd04_density_dependence_audit_record(
    *,
    status_date: str = "2026-01-24",
) -> OVSELSND04DensityDependenceAuditRecord:
    repo_root = _find_repo_root(Path(__file__))

    policy = snddig01_minimal_density_digitization_record(date=str(status_date))

    snd01 = ovsnd01_sound_speed_scaling_record(date=str(status_date))
    snd01n = ovsnd01_digitized_propagation_dataset_record(date=str(status_date))
    snd02 = ovsnd02_sound_speed_from_propagation_record(date=str(status_date))
    snd03n = ovsnd03n_central_density_digitized_record(date=str(status_date))
    snd03 = ovsnd03_sound_speed_density_scaling_record(date=str(status_date))

    sel01 = ovsel01_selection_status_record(status_date="2026-01-23")
    sel02 = ovsel02_selection_status_record(status_date="2026-01-23")
    dq03 = ovdq03_dq01_active_policy_activation_record(date="2026-01-24")

    checks: dict[str, Any] = {
        "SND-DIG-01": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/policies/SND-DIG-01_minimal_density_digitization.md",
            computed_payload=policy.to_jsonable(),
        ),
        "OV-SND-01": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SND-01_sound_speed_scaling_anchor.md",
            computed_payload=snd01.to_jsonable(),
        ),
        "OV-SND-01N": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SND-01_sound_propagation_distance_time_digitized.md",
            computed_payload=snd01n.to_jsonable(),
        ),
        "OV-SND-02": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
            computed_payload=snd02.to_jsonable(),
        ),
        "OV-SND-03N": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SND-03_central_density_digitized.md",
            computed_payload=snd03n.to_jsonable(),
        ),
        "OV-SND-03": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SND-03_sound_speed_density_scaling.md",
            computed_payload=snd03.to_jsonable(),
        ),
        "OV-SND-03N CSV exists": _check_path_exists(repo_root=repo_root, rel_path=snd03n.dataset["csv_relpath"]),
        "OV-SND-03N metadata exists": _check_path_exists(
            repo_root=repo_root, rel_path=snd03n.dataset["metadata_relpath"]
        ),
        "OV-SEL-01": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
            computed_payload=sel01.to_jsonable(),
        ),
        "OV-SEL-02": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-02_selection_status_policy_compare.md",
            computed_payload=sel02.to_jsonable(),
        ),
        "OV-DQ-03": _check_lock_matches(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/policies/DQ-01_active_policy_activation.md",
            computed_payload=dq03.to_jsonable(),
        ),
        "No OV-SND-03 token in OV-SEL-01": _check_no_token(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
            token="OV-SND-03",
        ),
        "No OV-SND-03N token in OV-SEL-01": _check_no_token(
            repo_root=repo_root,
            lock_rel_path="formal/markdown/locks/observables/OV-SEL-01_selection_status.md",
            token="OV-SND-03N",
        ),
        "No OV-SND-03 token in OV-XD-04": _check_no_token(
            repo_root=repo_root,
            lock_rel_path=str(sel01.ovxd04_overlap_only_comparison["lock_path"]),
            token="OV-SND-03",
        ),
        "No OV-SND-03N token in OV-XD-04": _check_no_token(
            repo_root=repo_root,
            lock_rel_path=str(sel01.ovxd04_overlap_only_comparison["lock_path"]),
            token="OV-SND-03N",
        ),
    }

    all_ok = all(bool(v.get("ok", True)) for v in checks.values() if isinstance(v, dict)) and all(
        bool(v.get("exists", True)) for v in checks.values() if isinstance(v, dict)
    )

    narrative = (
        "Density dependence audit (bookkeeping-only; no physics claim):\n"
        "1) What changed? Added SND-DIG-01 policy, OV-SND-03N (digitized central density), and OV-SND-03 (density-scaled derived quantities).\n"
        "2) What did not change? Selection/regime/policy locks are unchanged; new sound-lane density artifacts are non-decisive by design.\n"
        "3) Forbidden behaviors: no continuity inference; no regime averaging; no selection participation.\n"
        "4) Limitation: single-condition density anchor only; constancy across densities not tested here."
        f"\n\nSelf-checks (lock==computed + file existence + negative token checks) all_ok={bool(all_ok)}."
    )

    return OVSELSND04DensityDependenceAuditRecord(
        schema="OV-SEL-SND-04_density_dependence_audit/v1",
        status_date=str(status_date),
        checks=checks,
        narrative=narrative,
    )


def render_ovsel_snd04_lock_markdown(record: OVSELSND04DensityDependenceAuditRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-SEL-SND-04 — Density dependence audit (computed)\n\n"
        "Scope / limits\n"
        "- Bookkeeping / narrative only; no physics claim\n"
        "- New density artifacts are non-decisive by design; no selection/regime effects\n\n"
        "Narrative (operational)\n\n"
        f"{record.narrative}\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovsel_snd04_lock(*, lock_path: Path | None = None, status_date: str = "2026-01-24") -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-SEL-SND-04_density_dependence_audit.md"

    rec = ovsel_snd04_density_dependence_audit_record(status_date=str(status_date))

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovsel_snd04_lock_markdown(rec), encoding="utf-8")
    return out
