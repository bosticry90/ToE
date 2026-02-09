from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Iterable


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


_JSON_BLOCK_RE = re.compile(r"```json\s*(\{.*?\})\s*```", flags=re.DOTALL)


def _extract_json_block(md_text: str) -> dict[str, Any]:
    m = _JSON_BLOCK_RE.search(md_text)
    if m is None:
        raise ValueError("Missing JSON record block")
    return json.loads(m.group(1))


def _get_nested(d: dict[str, Any], path: str) -> Any:
    cur: Any = d
    for part in path.split("."):
        if not isinstance(cur, dict) or part not in cur:
            raise KeyError(path)
        cur = cur[part]
    return cur


@dataclass(frozen=True)
class ScalarEstimate:
    key: str | None
    label: str
    value: float
    se: float | None
    units: str
    fingerprint: str | None
    source_lock: str


@dataclass(frozen=True)
class PairingDecision:
    bragg_condition_key: str
    sound_lock: str
    reasons: tuple[str, ...]


def _norm_relpath(p: str) -> str:
    return p.replace("\\\\", "/").lstrip("./")


def _extract_comparability_gate(ovbr_snd01: dict[str, Any]) -> tuple[bool, list[str], str | None]:
    """Return (gate_ok, current_blockers, status) for OV-BR-SND-01."""
    comp = ovbr_snd01.get("comparability")
    if not isinstance(comp, dict):
        return (False, ["missing_comparability"], None)

    comparable_in_principle = comp.get("comparable_in_principle") is True
    blockers: list[str] = []
    blockers_raw = comp.get("current_blockers")
    if isinstance(blockers_raw, list):
        blockers = [x for x in blockers_raw if isinstance(x, str)]

    status = comp.get("status") if isinstance(comp.get("status"), str) else None
    gate_ok = comparable_in_principle and not blockers
    return (gate_ok, blockers, status)


def _extract_density_mapping_gate(ovbr_snd02: dict[str, Any]) -> tuple[bool, str | None, int | None]:
    """Return (gate_ok, mapping.status, mapping_tuples_count) for OV-BR-SND-02."""
    mapping = ovbr_snd02.get("mapping")
    if not isinstance(mapping, dict):
        return (False, None, None)

    mapping_status = mapping.get("status") if isinstance(mapping.get("status"), str) else None
    tuples_raw = mapping.get("mapping_tuples")
    tuple_count = len(tuples_raw) if isinstance(tuples_raw, list) else None

    gate_ok = mapping_status == "unblocked"
    return (gate_ok, mapping_status, tuple_count)


def _load_bragg_sound_pairing_map(
    *,
    repo_root: Path,
    audit: dict[str, Any] | None,
    override_mapping_relpath: str | None,
) -> tuple[dict[str, set[str]], str | None, int | None]:
    """Return (condition_key -> set(sound_lock_relpath), mapping_relpath, tuple_count)."""
    mapping_relpath: str | None = None
    if override_mapping_relpath is not None:
        mapping_relpath = override_mapping_relpath
    elif audit is not None:
        try:
            rel = _get_nested(audit, "status.inputs.mapping_tuples.ovbr_snd03_bragg_sound_pairing.relpath")
            if isinstance(rel, str) and rel.strip():
                mapping_relpath = rel.strip()
        except KeyError:
            mapping_relpath = None

    if not mapping_relpath:
        return ({}, None, None)

    p = repo_root / mapping_relpath
    if not p.exists():
        return ({}, mapping_relpath, 0)

    try:
        obj = json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return ({}, mapping_relpath, 0)

    tuples_raw = obj.get("mapping_tuples") if isinstance(obj, dict) else None
    if not isinstance(tuples_raw, list):
        return ({}, mapping_relpath, 0)

    out: dict[str, set[str]] = {}
    for t in tuples_raw:
        if not isinstance(t, dict):
            continue
        ck = t.get("bragg_condition_key")
        sl = t.get("sound_lock_path") or t.get("sound_lock_relpath")
        if not isinstance(ck, str) or not isinstance(sl, str):
            continue
        ck = ck.strip()
        sl = _norm_relpath(sl.strip())
        if not ck or not sl:
            continue
        out.setdefault(ck, set()).add(sl)

    return (out, mapping_relpath, len(tuples_raw))


def _format_float(x: float | None, *, digits: int = 6) -> str:
    if x is None:
        return "null"
    if not math.isfinite(x):
        return str(x)
    return f"{x:.{digits}g}"


def _markdown_table(headers: list[str], rows: list[list[str]]) -> str:
    out: list[str] = []
    out.append("| " + " | ".join(headers) + " |")
    out.append("| " + " | ".join(["---"] * len(headers)) + " |")
    for r in rows:
        out.append("| " + " | ".join(r) + " |")
    return "\n".join(out)


def _compute_rel_err(a: float, b: float, eps: float = 1e-12) -> float:
    return abs(a - b) / max(abs(b), eps)


def _compute_zscore(a: float, sa: float | None, b: float, sb: float | None) -> float | None:
    if sa is None or sb is None:
        return None
    denom = math.sqrt(sa * sa + sb * sb)
    if denom <= 0:
        return None
    return (a - b) / denom


def _extract_bragg_conditions(bragg05: dict[str, Any], *, lock_path: str) -> list[ScalarEstimate]:
    status = dict(bragg05.get("status") or {})
    if status.get("blocked") is True:
        raise RuntimeError(f"Bragg summary is blocked: {status.get('reasons')}")

    fp = bragg05.get("fingerprint") if isinstance(bragg05.get("fingerprint"), str) else None

    rows = bragg05.get("rows")
    if not isinstance(rows, list) or not rows:
        raise RuntimeError("Bragg summary missing non-empty rows")

    out: list[ScalarEstimate] = []
    for r in rows:
        if not isinstance(r, dict):
            continue
        ck = r.get("condition_key")
        c = r.get("c_mm_per_s")
        se = r.get("se_mm_per_s")
        if not isinstance(ck, str) or not isinstance(c, (int, float)):
            continue
        out.append(
            ScalarEstimate(
                key=ck,
                label=f"Bragg {ck}",
                value=float(c) * 1e-3,
                se=float(se) * 1e-3 if isinstance(se, (int, float)) else None,
                units="m/s",
                fingerprint=fp,
                source_lock=lock_path,
            )
        )

    if not out:
        raise RuntimeError("Bragg summary had no parseable c_mm_per_s rows")

    return out


def _extract_sound_speed(sound02: dict[str, Any], *, label: str, lock_path: str) -> ScalarEstimate:
    fp = sound02.get("fingerprint") if isinstance(sound02.get("fingerprint"), str) else None
    c = _get_nested(sound02, "results.primary.c_m_per_s")
    se = None
    try:
        se_raw = _get_nested(sound02, "results.primary.se_m_per_s")
        if isinstance(se_raw, (int, float)):
            se = float(se_raw)
    except KeyError:
        se = None

    if not isinstance(c, (int, float)):
        raise RuntimeError(f"Sound record missing results.primary.c_m_per_s ({lock_path})")

    return ScalarEstimate(
        key=None,
        label=label,
        value=float(c),
        se=se,
        units="m/s",
        fingerprint=fp,
        source_lock=lock_path,
    )


def _read_lock_json(repo_root: Path, relpath: str) -> dict[str, Any]:
    p = repo_root / relpath
    if not p.exists():
        raise FileNotFoundError(f"Missing lock file: {relpath}")
    return _extract_json_block(p.read_text(encoding="utf-8"))


def build_report(
    *,
    repo_root: Path,
    bragg_lock: str,
    sound_locks: list[tuple[str, str]],
    cross_lane_audit_lock: str | None,
    comparability_lock: str | None,
    density_mapping_lock: str | None,
    bragg_sound_pairing_mapping_relpath: str | None,
    mode: str,
    include_suppressed: bool,
) -> str:
    bragg05 = _read_lock_json(repo_root, bragg_lock)
    bragg = _extract_bragg_conditions(bragg05, lock_path=bragg_lock)

    sound: list[ScalarEstimate] = []
    for label, rel in sound_locks:
        obj = _read_lock_json(repo_root, rel)
        sound.append(_extract_sound_speed(obj, label=label, lock_path=rel))

    tol = None
    comparability_status = None
    comparability_reasons: list[str] | None = None
    audit: dict[str, Any] | None = None
    if cross_lane_audit_lock is not None:
        audit = _read_lock_json(repo_root, cross_lane_audit_lock)
        try:
            tol_raw = _get_nested(audit, "comparability.criterion.tolerance")
            if isinstance(tol_raw, (int, float)):
                tol = float(tol_raw)
        except KeyError:
            tol = None
        try:
            comparability_status_raw = _get_nested(audit, "comparability.status")
            if isinstance(comparability_status_raw, str):
                comparability_status = comparability_status_raw
        except KeyError:
            comparability_status = None
        try:
            reasons_raw = _get_nested(audit, "comparability.reasons")
            if isinstance(reasons_raw, list) and all(isinstance(x, str) for x in reasons_raw):
                comparability_reasons = list(reasons_raw)
        except KeyError:
            comparability_reasons = None

    ovbr_snd01_ok: bool | None = None
    ovbr_snd01_blockers: list[str] | None = None
    ovbr_snd01_status: str | None = None
    if comparability_lock is not None:
        ovbr_snd01 = _read_lock_json(repo_root, comparability_lock)
        ovbr_snd01_ok, ovbr_snd01_blockers, ovbr_snd01_status = _extract_comparability_gate(ovbr_snd01)

    ovbr_snd02_ok: bool | None = None
    ovbr_snd02_status: str | None = None
    ovbr_snd02_tuple_count: int | None = None
    if density_mapping_lock is not None:
        ovbr_snd02 = _read_lock_json(repo_root, density_mapping_lock)
        ovbr_snd02_ok, ovbr_snd02_status, ovbr_snd02_tuple_count = _extract_density_mapping_gate(ovbr_snd02)

    pairing_map, pairing_relpath, pairing_tuple_count = _load_bragg_sound_pairing_map(
        repo_root=repo_root,
        audit=audit,
        override_mapping_relpath=bragg_sound_pairing_mapping_relpath,
    )

    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    src_rows: list[list[str]] = []
    for s in bragg + sound:
        src_rows.append(
            [
                s.label,
                s.source_lock,
                s.fingerprint or "(none)",
                f"{_format_float(s.value)} {s.units}",
                _format_float(s.se),
            ]
        )

    if mode not in {"justified_only", "numeric_only"}:
        raise ValueError(f"Unsupported mode: {mode!r}")

    cmp_rows: list[list[str]] = []
    suppressed: list[PairingDecision] = []
    justified_count = 0
    suppressed_count = 0

    for b in bragg:
        bkey = b.key or ""
        for s in sound:
            if mode == "numeric_only":
                rel_err = _compute_rel_err(b.value, s.value)
                z = _compute_zscore(b.value, b.se, s.value, s.se)
                pass_str = "(no threshold)"
                if tol is not None:
                    pass_str = "PASS" if rel_err <= tol else "FAIL"
                cmp_rows.append(
                    [
                        b.label,
                        s.label,
                        _format_float(b.value),
                        _format_float(b.se),
                        _format_float(s.value),
                        _format_float(s.se),
                        _format_float(abs(b.value - s.value)),
                        _format_float(rel_err),
                        _format_float(z),
                        pass_str,
                    ]
                )
                continue

            # justified_only: apply gates fail-closed.
            reasons: list[str] = []
            if cross_lane_audit_lock is None:
                reasons.append("NO_AUDIT_LOCK")
            if comparability_status != "present":
                reasons.append("AUDIT_COMPARABILITY_NOT_PRESENT")
            if comparability_lock is None:
                reasons.append("NO_OVBR_SND01_LOCK")
            elif ovbr_snd01_ok is not True:
                reasons.append("OVBR_SND01_BLOCKED")
            if density_mapping_lock is None:
                reasons.append("NO_OVBR_SND02_LOCK")
            elif ovbr_snd02_ok is not True:
                reasons.append("OVBR_SND02_MAPPING_NOT_UNBLOCKED")
            if not bkey:
                reasons.append("BRAGG_MISSING_CONDITION_KEY")

            allowed_sound_locks = pairing_map.get(bkey) if bkey else None
            if not allowed_sound_locks:
                reasons.append("NO_BRAGG_SOUND_MAPPING_TUPLE")
            else:
                sound_lock_norm = _norm_relpath(s.source_lock)
                if sound_lock_norm not in allowed_sound_locks:
                    reasons.append("BRAGG_SOUND_TUPLE_DOES_NOT_MATCH_SOUND_LOCK")

            if reasons:
                suppressed.append(
                    PairingDecision(
                        bragg_condition_key=bkey or "(missing)",
                        sound_lock=_norm_relpath(s.source_lock),
                        reasons=tuple(reasons),
                    )
                )
                suppressed_count += 1
                continue

            rel_err = _compute_rel_err(b.value, s.value)
            z = _compute_zscore(b.value, b.se, s.value, s.se)
            pass_str = "(no threshold)"
            if tol is not None:
                pass_str = "PASS" if rel_err <= tol else "FAIL"
            cmp_rows.append(
                [
                    b.label,
                    s.label,
                    _format_float(b.value),
                    _format_float(b.se),
                    _format_float(s.value),
                    _format_float(s.se),
                    _format_float(abs(b.value - s.value)),
                    _format_float(rel_err),
                    _format_float(z),
                    pass_str,
                ]
            )
            justified_count += 1

    lines: list[str] = []
    lines.append(f"# Cross-anchor comparison: Bragg low-k slope vs sound propagation")
    lines.append("")
    lines.append(f"Generated: {now}")
    lines.append("")
    if mode == "numeric_only":
        lines.append("MODE=NUMERIC_ONLY")
        lines.append(f"TOTAL={len(bragg) * len(sound)}")
    else:
        lines.append("MODE=JUSTIFIED_ONLY")
        lines.append(f"JUSTIFIED={justified_count} SUPPRESSED={suppressed_count} TOTAL={len(bragg) * len(sound)}")
    lines.append("")
    lines.append("Scope / limits")
    lines.append("- Bookkeeping-only: this report does not assert physical comparability.")
    lines.append("- Uses locked derived values and a pinned unit conversion: Bragg $c_{\\mathrm{mm/s}}$ → $c_{\\mathrm{m/s}}$ via $1\\,\\mathrm{mm/s}=10^{-3}\\,\\mathrm{m/s}$.")
    lines.append("- Any cross-lane pairing justification (comparability + mapping tuples) must come from OV-BR-SND-01/02 and explicit Bragg↔Sound pairing tuples; this report does not invent one.")
    lines.append("")

    if cross_lane_audit_lock is not None:
        lines.append("Cross-lane audit context")
        lines.append(f"- Audit lock: `{cross_lane_audit_lock}`")
        if comparability_status is not None:
            lines.append(f"- comparability.status: `{comparability_status}`")
        if tol is not None:
            lines.append(f"- criterion tolerance (relative error): {tol}")
        if comparability_reasons:
            lines.append(f"- comparability.reasons: {', '.join(comparability_reasons)}")
        lines.append("")

    lines.append("Gating inputs")
    if comparability_lock is not None:
        lines.append(f"- OV-BR-SND-01 lock: `{comparability_lock}`")
        if ovbr_snd01_status is not None:
            lines.append(f"  - OV-BR-SND-01 comparability.status: `{ovbr_snd01_status}`")
        if ovbr_snd01_blockers:
            lines.append(f"  - OV-BR-SND-01 current_blockers: {', '.join(ovbr_snd01_blockers)}")
        if ovbr_snd01_ok is not None:
            lines.append(f"  - OV-BR-SND-01 gate_ok: `{ovbr_snd01_ok}`")
    if density_mapping_lock is not None:
        lines.append(f"- OV-BR-SND-02 lock: `{density_mapping_lock}`")
        if ovbr_snd02_status is not None:
            lines.append(f"  - OV-BR-SND-02 mapping.status: `{ovbr_snd02_status}`")
        if ovbr_snd02_tuple_count is not None:
            lines.append(f"  - OV-BR-SND-02 mapping_tuples_count: {ovbr_snd02_tuple_count}")
        if ovbr_snd02_ok is not None:
            lines.append(f"  - OV-BR-SND-02 gate_ok: `{ovbr_snd02_ok}`")
    if pairing_relpath is not None:
        lines.append(f"- Bragg↔Sound pairing tuples: `{pairing_relpath}`")
        if pairing_tuple_count is not None:
            lines.append(f"  - mapping_tuples_count: {pairing_tuple_count}")
    lines.append("")

    lines.append("## Inputs (locks + fingerprints)")
    lines.append(_markdown_table(["Quantity", "Lock", "Fingerprint", "Value", "SE"], src_rows))
    lines.append("")

    if mode == "numeric_only":
        lines.append("## Numeric comparisons (numeric-only; not a justified pairing)")
    else:
        lines.append("## Justified comparisons only")
        if not cmp_rows:
            lines.append("No justified comparisons were produced under the current gates.")
            lines.append("")

    if cmp_rows:
        lines.append(
            _markdown_table(
                [
                    "Bragg",
                    "Sound",
                    "Bragg (m/s)",
                    "SE_b",
                    "Sound (m/s)",
                    "SE_s",
                    "|Δ| (m/s)",
                    "rel_err",
                    "z",
                    "tol check",
                ],
                cmp_rows,
            )
        )
        lines.append("")

    if mode == "justified_only" and include_suppressed and suppressed:
        lines.append("## Unjustified numeric checks (suppressed by default)")
        sup_rows: list[list[str]] = []
        for d in suppressed:
            sup_rows.append(
                [
                    d.bragg_condition_key,
                    d.sound_lock,
                    "SUPPRESSED",
                    ";".join(d.reasons),
                ]
            )
        lines.append(_markdown_table(["Bragg condition_key", "Sound lock", "Status", "Reasons"], sup_rows))
        lines.append("")

    lines.append("Interpretation notes")
    if mode == "justified_only":
        lines.append("- In `MODE=JUSTIFIED_ONLY`, comparisons are suppressed unless explicitly justified by comparability + mapping evidence.")
    else:
        lines.append("- In `MODE=NUMERIC_ONLY`, rows are bookkeeping-only and do not assert a justified physical pairing.")
    lines.append("- A FAIL on `tol check` (if a tolerance is present) is not a physics contradiction by itself; it can reflect model/uncertainty gaps or an overly strict tolerance.")
    lines.append("- Use OV-BR-SND-01/02 and the explicit Bragg↔Sound pairing tuples to justify whether a given Bragg condition and sound dataset should be compared at all.")
    lines.append("")

    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="cross_anchor_bragg_vs_sound_report")
    parser.add_argument(
        "--out-dir",
        default=None,
        help="Output directory (default: formal/output)",
    )
    parser.add_argument(
        "--bragg-lock",
        default="formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md",
        help="Bragg summary lock path (repo-relative)",
    )
    parser.add_argument(
        "--sound-lock",
        action="append",
        default=[],
        metavar="LABEL=PATH",
        help="Sound lock spec(s), e.g. snd02=formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md (repeatable)",
    )
    parser.add_argument(
        "--cross-lane-audit-lock",
        default="formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit_OVERRIDE.md",
        help="Cross-lane audit lock path (repo-relative). Use empty string to disable.",
    )
    parser.add_argument(
        "--comparability-lock",
        default="formal/markdown/locks/observables/OV-BR-SND-01_sound_vs_bragg_lowk_comparability.md",
        help="OV-BR-SND-01 comparability lock path (repo-relative). Use empty string to disable.",
    )
    parser.add_argument(
        "--density-mapping-lock",
        default="formal/markdown/locks/observables/OV-BR-SND-02_cross_source_density_mapping.md",
        help="OV-BR-SND-02 density-mapping lock path (repo-relative). Use empty string to disable.",
    )
    parser.add_argument(
        "--bragg-sound-pairing-tuples",
        default=None,
        help="Override Bragg↔Sound pairing tuples JSON relpath (repo-relative). Default: use OV-BR-SND-03 status.inputs mapping relpath.",
    )
    parser.add_argument(
        "--mode",
        choices=["justified_only", "numeric_only"],
        default="justified_only",
        help="Default suppresses any comparison not explicitly justified by mapping tuples.",
    )
    parser.add_argument(
        "--include-suppressed",
        action="store_true",
        help="In justified_only mode, include a suppressed-items section (no numeric metrics computed for suppressed items).",
    )

    args = parser.parse_args(argv)

    repo_root = find_repo_root(Path(__file__))

    sound_specs: list[tuple[str, str]] = []
    if args.sound_lock:
        for spec in args.sound_lock:
            if "=" not in spec:
                raise SystemExit(f"Invalid --sound-lock: {spec!r} (expected LABEL=PATH)")
            label, rel = spec.split("=", 1)
            label = label.strip()
            rel = rel.strip()
            if not label or not rel:
                raise SystemExit(f"Invalid --sound-lock: {spec!r} (empty label or path)")
            sound_specs.append((label, rel))
    else:
        sound_specs = [
            ("Sound OV-SND-02", "formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md"),
            (
                "Sound OV-SND-02B",
                "formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md",
            ),
        ]

    audit_lock = str(args.cross_lane_audit_lock or "").strip() or None
    comparability_lock = str(args.comparability_lock or "").strip() or None
    density_mapping_lock = str(args.density_mapping_lock or "").strip() or None
    pairing_override = str(args.bragg_sound_pairing_tuples or "").strip() or None

    report = build_report(
        repo_root=repo_root,
        bragg_lock=args.bragg_lock,
        sound_locks=sound_specs,
        cross_lane_audit_lock=audit_lock,
        comparability_lock=comparability_lock,
        density_mapping_lock=density_mapping_lock,
        bragg_sound_pairing_mapping_relpath=pairing_override,
        mode=args.mode,
        include_suppressed=bool(args.include_suppressed),
    )

    out_dir = Path(args.out_dir).resolve() if args.out_dir else (repo_root / "formal" / "output")
    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    out_path = out_dir / f"cross_anchor_bragg_vs_sound_{stamp}.md"
    if out_path.exists():
        i = 1
        while True:
            candidate = out_dir / f"cross_anchor_bragg_vs_sound_{stamp}_{i}.md"
            if not candidate.exists():
                out_path = candidate
                break
            i += 1
    out_path.write_text(report, encoding="utf-8", newline="\n")

    print(str(out_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
