"""CLI wrapper for OV-03x fit-family robustness record (B1 second dataset).

This tool supports two modes:
- Default: reads the canonical OV-03x lock and prints a concise --report summary.
- Compute: recomputes the report from the frozen B1 artifacts; optionally writes the lock.

Usage
    python -m formal.python.tools.ov03x_fit_family_robustness_record --report
    python -m formal.python.tools.ov03x_fit_family_robustness_record --report --compute
    python -m formal.python.tools.ov03x_fit_family_robustness_record --report --compute --write-lock
"""

from __future__ import annotations

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import json
import re
from pathlib import Path

from formal.python.toe.observables.ov01_fit_family_robustness import (
    OV01FitFamilyRobustnessReport,
    ov01_fit_family_robustness_failure_reasons,
)
from formal.python.toe.observables.ov03x_fit_family_robustness_record import (
    ov03x_fit_family_robustness_report,
    write_ov03x_lock,
)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise RuntimeError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_report_fingerprint(md_text: str) -> str:
    m = re.search(r"Report fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise RuntimeError("Missing report fingerprint line")
    return m.group(1)


def _report_from_lock_payload(payload: dict) -> OV01FitFamilyRobustnessReport:
    return OV01FitFamilyRobustnessReport(
        config_tag=str(payload["config_tag"]),
        adequacy_policy=str(payload["adequacy_policy"]),
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


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print a human-readable report")
    p.add_argument(
        "--compute",
        action="store_true",
        help="Compute report from frozen artifacts instead of reading the lock",
    )
    p.add_argument(
        "--write-lock",
        action="store_true",
        help="Write/update the canonical markdown lock (requires --compute)",
    )
    p.add_argument(
        "--lock-path",
        default=None,
        help="Override lock output path when using --write-lock",
    )
    p.add_argument(
        "--adequacy-policy",
        default="DQ-01_v1",
        help="Adequacy policy string passed to the robustness gate when using --compute",
    )
    p.add_argument(
        "--q-threshold",
        default=0.90,
        type=float,
        help="q_threshold passed to the robustness gate when using --compute",
    )
    args = p.parse_args(argv)

    if not args.report:
        return 0

    repo_root = _find_repo_root(Path(__file__))
    canonical_lock_path = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-03x_fit_family_robustness_B1_dataset.md"
    )

    locked_fp: str | None = None
    if args.compute:
        rep = ov03x_fit_family_robustness_report(
            repo_root=repo_root,
            adequacy_policy=str(args.adequacy_policy),
            q_threshold=float(args.q_threshold),
            config_tag=f"OV-03x_fit_family_robustness_{str(args.adequacy_policy)}_q{float(args.q_threshold):.12g}",
        )
        if args.write_lock:
            out = write_ov03x_lock(
                lock_path=Path(args.lock_path) if args.lock_path is not None else None,
                adequacy_policy=str(args.adequacy_policy),
                q_threshold=float(args.q_threshold),
                config_tag=f"OV-03x_fit_family_robustness_{str(args.adequacy_policy)}_q{float(args.q_threshold):.12g}",
            )
            print(f"Wrote lock: {out}")
        print(
            "OV-03x report (B1 second dataset; computed from artifacts) "
            f"[adequacy_policy={str(args.adequacy_policy)}, q_threshold={float(args.q_threshold):.12g}]"
        )
    else:
        if args.write_lock:
            raise SystemExit("--write-lock requires --compute")
        text = canonical_lock_path.read_text(encoding="utf-8")
        payload = _extract_json_block(text)
        locked_fp = _extract_report_fingerprint(text)
        rep = _report_from_lock_payload(payload)
        print("OV-03x report (B1 second dataset; from lock)")
        print(f"  lock: {canonical_lock_path}")

    reasons = ov01_fit_family_robustness_failure_reasons(rep)
    print(f"  config_tag: {rep.config_tag}")
    print(f"  adequacy_policy: {rep.adequacy_policy}")
    print(f"  prefer_curved: {bool(rep.prefer_curved)}")
    print(f"  robustness_failed: {bool(rep.robustness_failed)}")
    print(f"  failure_reasons: {reasons if reasons else '[]'}")
    print(f"  curved_adequacy_passes: {bool(rep.curved_adequacy_passes)}")
    print(f"  q_ratio: {float(rep.q_ratio):.12g}  q_threshold: {float(rep.q_threshold):.12g}")
    if not (float(rep.r_max_linear) == 0.0):
        print(f"  q_ratio<=threshold: {bool(float(rep.q_ratio) <= float(rep.q_threshold))}")
    print(
        "  R_max linear/curved: "
        f"{float(rep.r_max_linear):.12g} / {float(rep.r_max_curved):.12g}"
    )
    if locked_fp is not None:
        print(f"  report_fingerprint (locked): {locked_fp}")
    else:
        print(f"  report_fingerprint: {rep.fingerprint()}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
