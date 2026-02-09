"""CLI for OV-ZPF-01 brain–ZPF resonance overlap audit scaffold.

Usage
  .\py.ps1 -m formal.python.tools.ovzpf01_brain_zpf_resonance_audit --report
  .\py.ps1 -m formal.python.tools.ovzpf01_brain_zpf_resonance_audit --write

Optional
  Provide explicit inputs via JSON:
    {
      "eeg_bands": [{"name": "gamma", "f_low_hz": 30, "f_high_hz": 80}, ...],
      "zpf_mode_bands": [{"name": "mode1", "f_low_hz": 38, "f_high_hz": 42}, ...]
    }

  .\py.ps1 -m formal.python.tools.ovzpf01_brain_zpf_resonance_audit --report --input-json path/to/inputs.json
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
from pathlib import Path

from formal.python.toe.observables.ovzpf01_brain_zpf_resonance_audit import (
    FrequencyBand,
    default_demo_inputs,
    ovzpf01_brain_zpf_resonance_audit,
    write_ovzpf01_brain_zpf_resonance_artifact,
)


def _load_inputs(path: Path) -> tuple[list[FrequencyBand], list[FrequencyBand]]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    eeg_raw = raw.get("eeg_bands")
    zpf_raw = raw.get("zpf_mode_bands")
    if not isinstance(eeg_raw, list) or not isinstance(zpf_raw, list):
        raise ValueError("input JSON must contain 'eeg_bands' and 'zpf_mode_bands' lists")

    eeg = [FrequencyBand(**b) for b in eeg_raw]
    zpf = [FrequencyBand(**b) for b in zpf_raw]
    return eeg, zpf


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input-json", default=None, help="Path to JSON inputs (optional)")
    p.add_argument("--T-K", type=float, default=295.0, help="Temperature in Kelvin")
    p.add_argument("--min-mode-overlap-frac", type=float, default=0.05)
    p.add_argument("--report", action="store_true", help="Print the JSON report payload")
    p.add_argument("--write", action="store_true", help="Write the canonical JSON artifact")
    args = p.parse_args(argv)

    if args.input_json:
        eeg, zpf = _load_inputs(Path(args.input_json))
    else:
        eeg, zpf = default_demo_inputs()

    if args.report:
        rep = ovzpf01_brain_zpf_resonance_audit(
            eeg_bands=eeg,
            zpf_mode_bands=zpf,
            temperature_K=float(args.T_K),
            min_mode_overlap_fraction=float(args.min_mode_overlap_frac),
        )
        print(json.dumps(rep.to_jsonable(), indent=2, sort_keys=True))

    if args.write:
        out = write_ovzpf01_brain_zpf_resonance_artifact(
            temperature_K=float(args.T_K),
            min_mode_overlap_fraction=float(args.min_mode_overlap_frac),
        )
        print(f"Wrote {out.as_posix()}")

    if not args.report and not args.write:
        p.print_help()
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
