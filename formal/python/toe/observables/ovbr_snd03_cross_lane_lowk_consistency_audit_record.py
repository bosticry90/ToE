"""OV-BR-SND-03: cross-lane low-k consistency audit (computed lock).

Purpose
- Ingest already-locked, derived outputs from the Sound lane and Bragg lane and
  emit a conservative comparability audit.

Inputs (locked outputs only)
- Sound:
  - OV-SND-02 (single) derived sound speed
  - OV-SND-02B (seriesB) derived sound speed
- Bragg:
  - OV-BR-04A low-k slope (condition_A)
  - OV-BR-04B low-k slope (condition_B)

Design constraints
- Must run even if no Bragg↔Sound mapping exists.
- If mapping is absent, that is a *valid audit conclusion* (not a blocker):
  comparability.status="absent" and blocked=False.

Scope / limits
- Bookkeeping/audit only; no physics claim.
- No unit conversion beyond what is explicitly pinned by the input records.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.constraints.admissibility_manifest import check_required_gates
from formal.python.toe.observables.ovbr02_regime_bridge_record import ovbr02_regime_bridge_record
from formal.python.toe.observables.ovbr03n_bragg_dispersion_k_omega_digitized import ovbr03n_digitized_dispersion_record
from formal.python.toe.observables.ovbr04a_bragg_lowk_slope_conditionA_record import (
    ovbr04a_bragg_lowk_slope_conditionA_record,
)
from formal.python.toe.observables.ovbr04b_bragg_lowk_slope_conditionB_record import (
    ovbr04b_bragg_lowk_slope_conditionB_record,
)
from formal.python.toe.observables.ovsnd02_sound_speed_from_propagation_record import (
    ovsnd02_sound_speed_from_propagation_record,
)
from formal.python.toe.observables.ovsnd02b_sound_speed_from_propagation_seriesb_record import (
    ovsnd02b_sound_speed_from_propagation_record,
)


RC_NO_MAPPING_TUPLE = "NO_MAPPING_TUPLE"
RC_MAPPING_HYPOTHESIS_ONLY = "MAPPING_HYPOTHESIS_ONLY"
RC_REGIME_BRIDGE_INSUFFICIENT = "REGIME_BRIDGE_INSUFFICIENT"
RC_UNIT_CONVERSION_UNSPECIFIED = "UNIT_CONVERSION_UNSPECIFIED"
RC_GATES_DISABLED = "GATES_DISABLED"

RC_CONVERSION_CHAIN_PINNED = "CONVERSION_CHAIN_PINNED"
RC_CRITERION_DEFINED = "CRITERION_DEFINED"
RC_WITHIN_TOL = "WITHIN_TOL"
RC_OUTSIDE_TOL = "OUTSIDE_TOL"
RC_PRIMARY_PAIR_NOT_COMPUTABLE = "PRIMARY_PAIR_NOT_COMPUTABLE"
RC_PRIMARY_PAIR_WITHIN_TOL = "PRIMARY_PAIR_WITHIN_TOL"
RC_PRIMARY_PAIR_OUTSIDE_TOL = "PRIMARY_PAIR_OUTSIDE_TOL"
RC_UNIT_METADATA_MISSING = "UNIT_METADATA_MISSING"
RC_NO_JUSTIFIED_PAIRING = "NO_JUSTIFIED_PAIRING"
RC_PAIRING_MAPPING_FILE_MISSING = "PAIRING_MAPPING_FILE_MISSING"
RC_PAIRING_MAPPING_INVALID = "PAIRING_MAPPING_INVALID"


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


def _try_load_json(repo_root: Path, relpath: str) -> tuple[bool, dict[str, Any] | None, str | None]:
    path = repo_root / relpath
    if not path.exists():
        return False, None, None
    try:
        return True, json.loads(path.read_text(encoding="utf-8")), None
    except Exception as e:  # noqa: BLE001
        return True, None, f"failed_to_parse_json:{type(e).__name__}"


@dataclass(frozen=True)
class OVBR_SND03CrossLaneLowKConsistencyAuditRecord:
    schema: str
    status_date: str

    observable_id: str

    sound_date: str
    bragg_date: str

    status: dict[str, Any]
    comparability: dict[str, Any]
    rows: list[dict[str, Any]]

    source_locators: dict[str, Any]
    notes: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "status_date": str(self.status_date),
            "observable_id": str(self.observable_id),
            "sound_date": str(self.sound_date),
            "bragg_date": str(self.bragg_date),
            "status": dict(self.status),
            "comparability": dict(self.comparability),
            "rows": list(self.rows),
            "source_locators": dict(self.source_locators),
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovbr_snd03_cross_lane_lowk_consistency_audit_record(
    *,
    status_date: str = "2026-01-25",
    sound_date: str = "2026-01-24",
    bragg_date: str = "2026-01-25",
) -> OVBR_SND03CrossLaneLowKConsistencyAuditRecord:
    repo_root = _find_repo_root(Path(__file__))

    required_gates = ["CT01", "SYM01", "CAUS01"]
    gate_check = check_required_gates(repo_root=repo_root, required_gate_ids=required_gates)

    # If admissibility gates are disabled (default posture), fail closed immediately.
    # This ensures mapping tuples cannot influence results under a blocked posture.
    if bool(gate_check.blocked):
        status = {
            "blocked": True,
            "blockers": ["admissibility_manifest_blocked"],
            "inputs": {
                "required_gates": list(required_gates),
                "admissibility_manifest": {
                    "path": str(gate_check.manifest_path),
                    "version": gate_check.manifest_version,
                },
            },
        }
        comparability = {
            "status": "blocked",
            "reasons": [RC_GATES_DISABLED],
        }
        notes = "Blocked by admissibility manifest; audit not computed."
        return OVBR_SND03CrossLaneLowKConsistencyAuditRecord(
            schema="OV-BR-SND-03_cross_lane_lowk_consistency_audit/v4",
            status_date=str(status_date),
            observable_id="OV-BR-SND-03",
            sound_date=str(sound_date),
            bragg_date=str(bragg_date),
            status=status,
            comparability=comparability,
            rows=[],
            source_locators={},
            notes=notes,
        )

    # Locked input records.
    snd02 = ovsnd02_sound_speed_from_propagation_record(date=str(sound_date))
    snd02b = ovsnd02b_sound_speed_from_propagation_record(date=str(sound_date))

    br03n = ovbr03n_digitized_dispersion_record(date=str(bragg_date))
    br04a = ovbr04a_bragg_lowk_slope_conditionA_record(date=str(bragg_date))
    br04b = ovbr04b_bragg_lowk_slope_conditionB_record(date=str(bragg_date))

    # Robustness: fail closed if BR-04A is blocked or missing results.primary
    br04a_blocked = False
    br04a_missing_primary = False
    br04a_status = getattr(br04a, "status", {})
    if isinstance(br04a_status, dict):
        br04a_blocked = br04a_status.get("blocked", False)
    if not (hasattr(br04a, "results") and isinstance(br04a.results, dict) and "primary" in br04a.results):
        br04a_missing_primary = True
    if br04a_blocked or br04a_missing_primary:
        status = {
            "blocked": True,
            "blockers": (["br04a_blocked"] if br04a_blocked else []) + (["br04a_missing_primary"] if br04a_missing_primary else []),
            "inputs": {
                "br04a_blocked": br04a_blocked,
                "br04a_missing_primary": br04a_missing_primary,
            },
        }
        comparability = {
            "status": "blocked",
            "reasons": (["br04a_blocked"] if br04a_blocked else []) + (["br04a_missing_primary"] if br04a_missing_primary else []),
        }
        notes = "Blocked: BR-04A is blocked or missing results.primary. Audit not computed."
        return OVBR_SND03CrossLaneLowKConsistencyAuditRecord(
            schema="OV-BR-SND-03_cross_lane_lowk_consistency_audit/v4",
            status_date=str(status_date),
            observable_id="OV-BR-SND-03",
            sound_date=str(sound_date),
            bragg_date=str(bragg_date),
            status=status,
            comparability=comparability,
            rows=[],
            source_locators={},
            notes=notes,
        )

    # Optional: OV-BR-02 regime-bridge bookkeeping (not required for comparability).
    br02 = ovbr02_regime_bridge_record()

    blockers: list[str] = []
    if gate_check.blocked:
        blockers.append("admissibility_manifest_blocked")

    # Sound seriesB can be BLOCKED; treat as a blocker for that input only.
    snd02b_blocked = bool(getattr(snd02b, "status", {}).get("blocked", False))
    if snd02b_blocked:
        blockers.append("sound_seriesB_blocked")

    if blockers and gate_check.blocked:
        status = {
            "blocked": True,
            "blockers": list(blockers) + list(gate_check.reasons),
            "inputs": {
                "required_gates": list(required_gates),
                "admissibility_manifest": {
                    "path": str(gate_check.manifest_path),
                    "version": gate_check.manifest_version,
                },
                "sound_seriesB_blocked": bool(snd02b_blocked),
            },
        }
        comparability = {
            "status": "blocked",
            "reasons": [RC_GATES_DISABLED],
        }
        source_locators = {
            "sound": {
                "snd02_lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
                "snd02b_lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
            },
            "bragg": {
                "br04a_lock_path": "formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
                "br04b_lock_path": "formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md",
                "br03n_lock_path": "formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md",
            },
            "regime": {
                "br02_lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
            },
        }
        notes = "Blocked by admissibility manifest; audit not computed."
        return OVBR_SND03CrossLaneLowKConsistencyAuditRecord(
            schema="OV-BR-SND-03_cross_lane_lowk_consistency_audit/v4",
            status_date=str(status_date),
            observable_id="OV-BR-SND-03",
            sound_date=str(sound_date),
            bragg_date=str(bragg_date),
            status=status,
            comparability=comparability,
            rows=[],
            source_locators=source_locators,
            notes=notes,
        )

    # Mapping tuples are optional inputs; Bragg↔Sound comparability requires an explicit
    # cross-lane pairing mapping (or an explicit same-source assertion).
    density_mapping_rel = "formal/external_evidence/bec_sound_density_secondary_TBD/ovbr_snd02_density_mapping/mapping_tuples.json"
    density_mapping_exists, density_mapping_obj, density_mapping_err = _try_load_json(repo_root, density_mapping_rel)

    pairing_mapping_rel = "formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json"
    pairing_mapping_exists, pairing_mapping_obj, pairing_mapping_err = _try_load_json(repo_root, pairing_mapping_rel)

    mapping_tuples: list[dict[str, Any]] = []
    if pairing_mapping_exists and pairing_mapping_obj is not None:
        t = pairing_mapping_obj.get("mapping_tuples")
        if isinstance(t, list) and all(isinstance(x, dict) for x in t):
            mapping_tuples = [dict(x) for x in t]

    def _mapping_tuple_for(*, bragg_key: str, sound_key: str) -> dict[str, Any] | None:
        for t in mapping_tuples:
            if str(t.get("bragg_key")) == str(bragg_key) and str(t.get("sound_key")) == str(sound_key):
                return t
        return None

    bragg_sound_mapping_present = bool(mapping_tuples)
    bragg_sound_mapping_count = int(len(mapping_tuples))

    # --- Pinned conversion + criterion (deterministic) ---
    # Bragg lane: OV-BR-04A/B export a velocity candidate c_mm_per_s derived from
    # the low-k slope with the pinned identity: 1 (kHz)/(um^-1) = 1 (mm/s).
    # We convert mm/s -> m/s with factor 1e-3.
    BRAGG_MM_PER_S_TO_M_PER_S = 1.0e-3

    # Comparability criterion (pinned): relative error within tolerance.
    # This is governance bookkeeping only; it is not a physics claim.
    REL_TOL = 0.15
    EPS = 1.0e-12

    conversion_chain = {
        "rule_id": "unit_chain_v1",
        "bragg": {
            "input": {
                "quantity": "low_k_slope_of_omega_over_2pi_vs_k",
                "x_units": "um^-1",
                "y_units": "kHz",
                "slope_units": "(kHz)/(um^-1)",
            },
            "velocity_candidate": {
                "quantity": "c",
                "units": "mm/s",
                "identity": "1 (kHz)/(um^-1) = 1 (mm/s)",
                "exported_key": "c_mm_per_s",
            },
            "to_m_per_s": {
                "factor": float(BRAGG_MM_PER_S_TO_M_PER_S),
                "identity": "1 (mm/s) = 1e-3 (m/s)",
            },
            "assumptions": [
                "uses_unit_identities_pinned_in_OV-BR-04A/B",
                "no_additional_physical_equivalence_claim",
            ],
        },
        "sound": {
            "input": {
                "quantity": "sound_speed",
                "units": "m/s",
                "exported_key": "c_m_per_s",
            },
            "assumptions": [
                "derived_from_frozen_distance_time_points_only",
            ],
        },
    }

    criterion = {
        "criterion_id": "lowk_velocity_ratio_v1",
        "metric": "rel_err = abs(v_bragg_m_per_s - v_sound_m_per_s) / max(abs(v_sound_m_per_s), eps)",
        "tolerance": float(REL_TOL),
        "eps": float(EPS),
        "prerequisites": [
            "unit_labels_pinned_in_upstream_records",
            "explicit_cross_lane_pairing_present",
        ],
        "rationale": "Pinned conservative tolerance for numeric comparability after explicit unit conversion; no systematic-error model.",
    }

    def _relative_err(v_a: float, v_b: float) -> float:
        denom = max(abs(float(v_b)), float(EPS))
        return float(abs(float(v_a) - float(v_b)) / denom)

    def _units_ok() -> tuple[bool, list[str]]:
        reasons: list[str] = []

        snd_units = getattr(snd02, "units", None)
        if not isinstance(snd_units, dict):
            reasons.append("snd02_missing_units")
        else:
            if str(snd_units.get("time")) != "ms":
                reasons.append("snd02_units_time_not_ms")
            if str(snd_units.get("distance")) != "um":
                reasons.append("snd02_units_distance_not_um")
            if str(snd_units.get("c")) != "m_per_s":
                reasons.append("snd02_units_c_not_m_per_s")

        br_units = getattr(br04a, "units", None)
        if not isinstance(br_units, dict):
            reasons.append("br04a_missing_units")
        else:
            if str(br_units.get("k")) != "um_inv":
                reasons.append("br04a_units_k_not_um_inv")
            if str(br_units.get("omega_over_2pi")) != "kHz":
                reasons.append("br04a_units_omega_over_2pi_not_kHz")
            if str(br_units.get("slope")) != "kHz_per_um_inv":
                reasons.append("br04a_units_slope_not_kHz_per_um_inv")
            if str(br_units.get("velocity_candidate")) != "mm_per_s":
                reasons.append("br04a_units_velocity_candidate_not_mm_per_s")

        return (len(reasons) == 0), reasons

    def _sound_value_for(key: str) -> tuple[float | None, float | None, dict[str, Any]]:
        if key == "snd02_single":
            v = float(snd02.results["primary"]["c_m_per_s"])  # type: ignore[index]
            se = float(snd02.results["primary"]["se_m_per_s"])  # type: ignore[index]
            loc = {
                "lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
                "schema": str(snd02.schema),
                "fingerprint": str(snd02.fingerprint()),
            }
            return v, se, loc

        if key == "snd02b_seriesB":
            if snd02b.results is None:
                loc = {
                    "lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
                    "schema": str(snd02b.schema),
                    "fingerprint": str(snd02b.fingerprint()),
                    "blocked": True,
                    "blockers": list(getattr(snd02b, "status", {}).get("blockers", [])),
                }
                return None, None, loc

            v = float(snd02b.results["primary"]["c_m_per_s"])  # type: ignore[index]
            se = float(snd02b.results["primary"]["se_m_per_s"])  # type: ignore[index]
            loc = {
                "lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
                "schema": str(snd02b.schema),
                "fingerprint": str(snd02b.fingerprint()),
            }
            return v, se, loc

        raise ValueError(f"unknown sound_key: {key}")

    def _bragg_value_for(key: str) -> tuple[float, float, dict[str, Any]]:
        if key == "br04a_conditionA":
            # Prefer the already-pinned velocity candidate in mm/s.
            v = float(br04a.results["primary"]["c_mm_per_s"])  # type: ignore[index]
            se = float(br04a.results["primary"]["se_mm_per_s"])  # type: ignore[index]
            loc = {
                "lock_path": "formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
                "schema": str(br04a.schema),
                "fingerprint": str(br04a.fingerprint()),
                "source": {
                    "pdf_relpath": str(br03n.source["pdf_relpath"]),
                    "pdf_sha256": str(br03n.source["pdf_sha256"]),
                    "png_relpath": str(br03n.source["png_relpath"]),
                    "png_sha256": str(br03n.source["png_sha256"]),
                    "figure": "Fig. 2",
                    "page_render": "page6_z4.png",
                },
            }
            return v, se, loc

        if key == "br04b_conditionB":
            v = float(br04b.results["primary"]["c_mm_per_s"])  # type: ignore[index]
            se = float(br04b.results["primary"]["se_mm_per_s"])  # type: ignore[index]
            loc = {
                "lock_path": "formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md",
                "schema": str(br04b.schema),
                "fingerprint": str(br04b.fingerprint()),
                "source": {
                    "pdf_relpath": str(br03n.source["pdf_relpath"]),
                    "pdf_sha256": str(br03n.source["pdf_sha256"]),
                    "png_relpath": str(br03n.source["png_relpath"]),
                    "png_sha256": str(br03n.source["png_sha256"]),
                    "figure": "Fig. 2",
                    "page_render": "page6_z4.png",
                },
            }
            return v, se, loc

        raise ValueError(f"unknown bragg_key: {key}")

    units_ok, unit_fail_reasons = _units_ok()

    rows: list[dict[str, Any]] = []
    for bragg_key in ["br04a_conditionA", "br04b_conditionB"]:
        br_v, br_se, br_loc = _bragg_value_for(bragg_key)
        for sound_key in ["snd02_single", "snd02b_seriesB"]:
            snd_v, snd_se, snd_loc = _sound_value_for(sound_key)

            # Convert Bragg velocity candidate mm/s -> m/s.
            v_bragg_m_per_s = float(br_v) * float(BRAGG_MM_PER_S_TO_M_PER_S)
            se_bragg_m_per_s = float(br_se) * float(BRAGG_MM_PER_S_TO_M_PER_S)

            row_reason_codes: list[str] = [RC_CONVERSION_CHAIN_PINNED, RC_CRITERION_DEFINED]
            if not units_ok:
                row_reason_codes.append(RC_UNIT_METADATA_MISSING)
            if snd_v is None or snd_se is None:
                row_reason_codes.append("SOUND_INPUT_BLOCKED")

            mt = _mapping_tuple_for(bragg_key=str(bragg_key), sound_key=str(sound_key))
            paired = bool(mt is not None)
            pair_type = "none" if mt is None else str(mt.get("pair_type") or "unknown")
            mapping_tuple_id = None if mt is None else mt.get("mapping_tuple_id")

            rel_err = None
            abs_diff = None
            z = None
            passed = None
            status = "not_compared"

            if not paired:
                row_reason_codes.append(RC_NO_MAPPING_TUPLE)
                row_reason_codes.append(RC_NO_JUSTIFIED_PAIRING)
            elif not units_ok:
                row_reason_codes.append(RC_UNIT_METADATA_MISSING)
            elif snd_v is None or snd_se is None:
                # Cannot compute metric if sound input is blocked.
                status = "not_compared"
            else:
                abs_diff = float(abs(v_bragg_m_per_s - float(snd_v)))
                rel_err = _relative_err(v_bragg_m_per_s, float(snd_v))
                combined = float((se_bragg_m_per_s**2 + float(snd_se) ** 2) ** 0.5)
                z = None if not (combined > 0.0) else float(abs_diff / combined)
                passed = bool(rel_err <= float(REL_TOL))
                status = "pass" if passed else "fail"
                row_reason_codes.append(RC_WITHIN_TOL if passed else RC_OUTSIDE_TOL)

            row = {
                "bragg_key": str(bragg_key),
                "sound_key": str(sound_key),
                "pair_id": f"{bragg_key}__{sound_key}",
                "pair_type": str(pair_type),
                "mapping_tuple_id": mapping_tuple_id,
                "values": {
                    "bragg_velocity_candidate_units": "mm_per_s",
                    "sound_c_units": "m_per_s",
                    "bragg_value": float(br_v),
                    "bragg_se": float(br_se),
                    "sound_value": None if snd_v is None else float(snd_v),
                    "sound_se": None if snd_se is None else float(snd_se),
                },
                "conversion_chain": dict(conversion_chain),
                "criterion": dict(criterion),
                "derived": {
                    "bragg_velocity_candidate_m_per_s": float(v_bragg_m_per_s),
                    "bragg_velocity_candidate_se_m_per_s": float(se_bragg_m_per_s),
                    "sound_velocity_m_per_s": None if snd_v is None else float(snd_v),
                    "sound_velocity_se_m_per_s": None if snd_se is None else float(snd_se),
                    "abs_diff_m_per_s": abs_diff,
                    "rel_err": rel_err,
                    "z_score": z,
                    "pass": passed,
                },
                "comparability": {
                    "status": str(status),
                    "reason_codes": list(row_reason_codes),
                    "notes": "Comparison is only computed when an explicit cross-lane pairing exists; otherwise prerequisites are reported only.",
                },
                "source_locators": {
                    "bragg": dict(br_loc),
                    "sound": dict(snd_loc),
                    "regime": {
                        "lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
                        "schema": str(br02.schema),
                        "fingerprint": str(br02.fingerprint()),
                    },
                },
            }
            rows.append(row)

    # Overall decision: established iff at least one explicitly paired row is computed and passes.
    comparability_reasons: list[str] = [RC_CONVERSION_CHAIN_PINNED, RC_CRITERION_DEFINED]
    if not units_ok:
        comparability_reasons.append(RC_UNIT_METADATA_MISSING)
        comparability_reasons.extend([f"unit:{r}" for r in unit_fail_reasons])

    if not pairing_mapping_exists:
        comparability_reasons.append(RC_PAIRING_MAPPING_FILE_MISSING)
    elif pairing_mapping_obj is None:
        comparability_reasons.append(RC_PAIRING_MAPPING_INVALID)

    any_paired = any(str(r.get("pair_type")) != "none" for r in rows)
    any_pass = any(bool(r.get("derived", {}).get("pass")) is True for r in rows)

    if not any_paired:
        comparability_status = "absent"
        comparability_reasons.append(RC_NO_MAPPING_TUPLE)
        comparability_reasons.append(RC_NO_JUSTIFIED_PAIRING)
    else:
        comparability_status = "established" if any_pass else "absent"
        comparability_reasons.append(RC_WITHIN_TOL if any_pass else RC_OUTSIDE_TOL)

    status = {
        "blocked": False,
        "blockers": [],
        "inputs": {
            "required_gates": list(required_gates),
            "admissibility_manifest": {
                "path": str(gate_check.manifest_path),
                "version": gate_check.manifest_version,
            },
            "sound_seriesB_blocked": bool(snd02b_blocked),
            "mapping_tuples": {
                "ovbr_snd02_density_mapping": {
                    "exists": bool(density_mapping_exists),
                    "relpath": str(density_mapping_rel),
                    "parse_error": density_mapping_err,
                    "schema": None if density_mapping_obj is None else str(density_mapping_obj.get("schema")),
                },
                "ovbr_snd03_bragg_sound_pairing": {
                    "exists": bool(pairing_mapping_exists),
                    "relpath": str(pairing_mapping_rel),
                    "parse_error": pairing_mapping_err,
                    "schema": None if pairing_mapping_obj is None else str(pairing_mapping_obj.get("schema")),
                    "bragg_sound_mapping_present": bool(bragg_sound_mapping_present),
                    "bragg_sound_tuple_count": int(bragg_sound_mapping_count),
                },
            },
        },
    }

    # Mapping absence is not a blocker; keep blocked=False per spec.
    comparability = {
        "status": str(comparability_status),
        "reasons": list(comparability_reasons),
        "conversion_chain": dict(conversion_chain),
        "criterion": dict(criterion),
    }

    source_locators = {
        "sound": {
            "snd02_lock_path": "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md",
            "snd02b_lock_path": "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
        },
        "bragg": {
            "br04a_lock_path": "formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md",
            "br04b_lock_path": "formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md",
            "br03n_lock_path": "formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md",
        },
        "regime": {
            "br02_lock_path": "formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md",
        },
    }

    notes = (
        "This audit does not assert physical comparability. It reports locked derived outputs and explicitly "
        "pins a unit conversion chain + numeric criterion. Cross-lane comparison is only computed when an "
        "explicit Bragg↔Sound pairing exists."
    )

    return OVBR_SND03CrossLaneLowKConsistencyAuditRecord(
        schema="OV-BR-SND-03_cross_lane_lowk_consistency_audit/v4",
        status_date=str(status_date),
        observable_id="OV-BR-SND-03",
        sound_date=str(sound_date),
        bragg_date=str(bragg_date),
        status=status,
        comparability=comparability,
        rows=rows,
        source_locators=source_locators,
        notes=notes,
    )


def render_ovbr_snd03_lock_markdown(record: OVBR_SND03CrossLaneLowKConsistencyAuditRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-SND-03 — Cross-lane low-k consistency audit (computed)\n\n"
        "Scope / limits\n"
        "- Audit only; no physics claim\n"
        "- Must remain valid even when no Bragg↔Sound mapping exists\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr_snd03_lock(
    *,
    lock_path: Path | None = None,
    status_date: str = "2026-01-25",
    sound_date: str = "2026-01-24",
    bragg_date: str = "2026-01-25",
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
            / "OV-BR-SND-03_cross_lane_lowk_consistency_audit.md"
        )

    rec = ovbr_snd03_cross_lane_lowk_consistency_audit_record(
        status_date=str(status_date),
        sound_date=str(sound_date),
        bragg_date=str(bragg_date),
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr_snd03_lock_markdown(rec), encoding="utf-8")
    return out
