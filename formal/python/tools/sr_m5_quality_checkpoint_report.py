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
from datetime import date
from pathlib import Path


def _repo_root_from_this_file() -> Path:
    return Path(__file__).resolve().parents[3]


def _cycle_from_text(text: str) -> int:
    m = re.search(r"cycle(\d+)", text)
    if m is None:
        raise RuntimeError(f"Could not parse cycle from `{text}`")
    return int(m.group(1))


def _arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Generate SR M5 periodic quality checkpoint report.")
    p.add_argument("--cycle", type=int, default=None, help="Explicit cycle number. Defaults to active cycle.")
    return p


def main() -> int:
    args = _arg_parser().parse_args()
    repo = _repo_root_from_this_file()

    registry_path = repo / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
    registry = json.loads(registry_path.read_text(encoding="utf-8"))

    active_gate = str(registry.get("sr_m5_theory_parity_gate_path", ""))
    if not active_gate:
        raise RuntimeError("Registry missing sr_m5_theory_parity_gate_path")

    active_cycle = _cycle_from_text(active_gate)
    report_cycle = args.cycle if args.cycle is not None else active_cycle

    gate_files = sorted((repo / "formal" / "python" / "tests").glob("test_sr_m5_theory_parity_link_cycle*_gate.py"))
    artifact_files = sorted((repo / "formal" / "output").glob("sr_m5_theory_parity_link_cycle*_v0.json"))

    non_skipped = 0
    for gate in gate_files:
        text = gate.read_text(encoding="utf-8")
        if "pytestmark = pytest.mark.skip(" not in text:
            non_skipped += 1

    payload = {
        "artifact_id": f"sr_m5_quality_checkpoint_cycle{report_cycle}_v0",
        "artifact_version": "v0",
        "generated_on": date.today().isoformat(),
        "active_cycle": report_cycle,
        "active_gate_path": active_gate,
        "artifact_count": len(artifact_files),
        "gate_count": len(gate_files),
        "non_skipped_gate_count": non_skipped,
        "scope": "sr_m5_periodic_quality_checkpoint",
    }

    out = repo / "formal" / "output" / f"sr_m5_quality_checkpoint_cycle{report_cycle}_v0.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    print(str(out.relative_to(repo)).replace("\\", "/"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
