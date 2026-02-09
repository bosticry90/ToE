r"""CLI for OV-UCFF-02 framewise cross-variation audit scaffold.

Usage
    .\\py.ps1 -m formal.python.tools.ovucff02_framewise_variation_audit --report --demo drift
    .\\py.ps1 -m formal.python.tools.ovucff02_framewise_variation_audit --report --pinned
    .\\py.ps1 -m formal.python.tools.ovucff02_framewise_variation_audit --write

Optional
  Provide X via JSON:
    {"X": [[...], [...], ...]}

    .\\py.ps1 -m formal.python.tools.ovucff02_framewise_variation_audit --report --input-json path/to/x.json
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
import os
from pathlib import Path
import sys

import numpy as np

from formal.python.toe.observables.ovucff02_framewise_variation_audit import (
    default_demo_inputs,
    default_pinned_input_path,
    default_reference_report_path,
    load_pinned_input_X,
    write_reference_report_from_ovucff02,
    ovucff02_framewise_variation_audit,
    write_ovucff02_framewise_variation_artifact,
)


def _canonical_json_sha256(path: Path) -> str:
    raw = json.loads(Path(path).read_text(encoding="utf-8"))
    b = json.dumps(raw, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    import hashlib

    return hashlib.sha256(b).hexdigest()


def _load_X(path: Path) -> np.ndarray:
    raw = json.loads(path.read_text(encoding="utf-8"))
    X = raw.get("X")
    if not isinstance(X, list):
        raise ValueError("input JSON must contain key 'X' as a 2D list")
    return np.asarray(X, dtype=float)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input-json", default=None, help="JSON file containing {'X': [[...], ...]} (optional)")
    p.add_argument(
        "--pinned",
        action="store_true",
        help=(
            "Use the canonical pinned input artifact for OV-UCFF-02. "
            "Ignored if --input-json is provided."
        ),
    )
    p.add_argument("--demo", default="drift", choices=["constant", "drift"], help="Demo input selection")
    p.add_argument("--eps", type=float, default=1e-12)
    p.add_argument("--report", action="store_true", help="Print the JSON report")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    p.add_argument(
        "--write-reference",
        action="store_true",
        help=(
            "Write the frozen reference report for OV-UCFF-02 pinned input "
            "to artifacts/input/OV-UCFF-02/reference_ovucff02_pinned_report.json. "
            "Safety-gated; requires --pinned, --force, and TOE_ALLOW_REFERENCE_WRITES=1."
        ),
    )
    p.add_argument(
        "--force",
        action="store_true",
        help="Required with --write-reference (explicit acknowledgement).",
    )
    args = p.parse_args(argv)

    if args.report:
        if args.input_json:
            X = _load_X(Path(args.input_json))
        elif args.pinned:
            X = load_pinned_input_X(path=default_pinned_input_path())
        else:
            X = default_demo_inputs()[str(args.demo)]
        rep = ovucff02_framewise_variation_audit(X=X, eps=float(args.eps))
        print(json.dumps(rep.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovucff02_framewise_variation_artifact()
        print(f"Wrote {out.as_posix()}")

    if args.write_reference:
        if args.input_json is not None:
            print("REFUSE: --write-reference requires --pinned (no --input-json).", file=sys.stderr)
            return 3
        if not args.pinned:
            print("REFUSE: --write-reference requires --pinned.", file=sys.stderr)
            return 3
        if not args.force:
            print("REFUSE: --write-reference requires --force.", file=sys.stderr)
            return 3
        if os.environ.get("TOE_ALLOW_REFERENCE_WRITES") != "1":
            print(
                "REFUSE: reference writes are disabled. Set TOE_ALLOW_REFERENCE_WRITES=1 and re-run with --force.",
                file=sys.stderr,
            )
            return 3

        ref_path = default_reference_report_path()
        old_ref_sha = _canonical_json_sha256(ref_path) if ref_path.exists() else None

        tool_source_sha = __import__("hashlib").sha256(Path(__file__).read_bytes()).hexdigest()
        out = write_reference_report_from_ovucff02(
            path=ref_path,
            pinned_input_path=default_pinned_input_path(),
            eps=float(args.eps),
            tool_module=__name__,
            tool_source_sha256=tool_source_sha,
        )

        new_ref_sha = _canonical_json_sha256(ref_path)
        pinned_raw = json.loads(default_pinned_input_path().read_text(encoding="utf-8"))

        print(f"Wrote {out.as_posix()}")
        print("REFERENCE WRITE RECEIPT")
        print(f"  reference_path: {ref_path.as_posix()}")
        print(f"  old_reference_sha256_canonical_json: {old_ref_sha}")
        print(f"  new_reference_sha256_canonical_json: {new_ref_sha}")
        print(f"  pinned_input_path: {default_pinned_input_path().as_posix()}")
        print(f"  pinned_input_schema: {pinned_raw.get('schema')}")
        print(f"  pinned_input_fingerprint: {pinned_raw.get('fingerprint')}")
        print(f"  pinned_input_sha256_canonical_json: {_canonical_json_sha256(default_pinned_input_path())}")

    if not args.report and not args.write and not args.write_reference:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
