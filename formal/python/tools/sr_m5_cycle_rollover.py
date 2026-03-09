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
import copy
import hashlib
import json
import re
from datetime import date
from pathlib import Path


SKIP_MARKER = (
    "import pytest\n\n\n"
    "pytestmark = pytest.mark.skip(\n"
    "    reason=\"Historical SR M5 cycle gate retained for archive traceability; active gate is registry-driven.\"\n"
    ")\n"
)

CANONICAL_UPDATE_FILES = (
    "governance_suite.ps1",
    "formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md",
    "formal/python/tests/test_pillar_deep_maturity_program_gate.py",
    "formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md",
    "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
    "State_of_the_Theory.md",
)

PRECHECK_CONTAINS = {
    "governance_suite.ps1": ("gate",),
    "formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md": ("gate",),
    "formal/python/tests/test_pillar_deep_maturity_program_gate.py": ("gate",),
    "formal/docs/paper/DERIVATION_TARGET_SR_M5_THEORY_PARITY_LINK_v0.md": ("gate", "artifact_path", "artifact_id", "delta", "hash"),
    "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md": (
        "gate",
        "artifact_path",
        "artifact_id",
        "delta",
        "hash",
    ),
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md": ("gate", "artifact_path", "artifact_id", "delta", "hash"),
    "State_of_the_Theory.md": ("gate", "artifact_path", "artifact_id", "delta", "hash"),
}


def _repo_root_from_this_file() -> Path:
    return Path(__file__).resolve().parents[3]


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read_text(path))


def _write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _cycle_from_ref(text: str) -> int:
    m = re.search(r"cycle(\d+)", text)
    if m is None:
        raise RuntimeError(f"Could not infer cycle number from: {text}")
    return int(m.group(1))


def _replace_cycle_tokens(text: str, current: int, nxt: int) -> str:
    prev = current - 1
    text = text.replace(f"cycle{current}", f"cycle{nxt}")
    text = text.replace(f"CYCLE{current}", f"CYCLE{nxt}")
    text = text.replace(f"cycle{prev}", f"cycle{current}")
    text = text.replace(f"CYCLE{prev}", f"CYCLE{current}")
    text = re.sub(
        r"# Cycle\d+ objective: exactly one active pointer, no legacy leakage from cycle\d+, and stable token ordering\.",
        f"# Cycle{nxt} objective: exactly one active pointer, no legacy leakage from cycle{current}, and stable token ordering.",
        text,
    )
    return text


def _archive_gate_text(gate_text: str) -> str:
    if "pytestmark = pytest.mark.skip(" in gate_text:
        return gate_text
    if "from pathlib import Path\n" not in gate_text:
        raise RuntimeError("Could not insert skip marker; expected pathlib import line.")
    return gate_text.replace("from pathlib import Path\n", "from pathlib import Path\n\n\n" + SKIP_MARKER, 1)


def _arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Roll SR M5 theory-parity gate/artifact to the next cycle.")
    p.add_argument("--next-cycle", type=int, default=None, help="Explicit next cycle number. Defaults to current+1.")
    return p


def _preflight_verify_current_cycle_surface(
    *,
    repo: Path,
    current_gate_rel: str,
    current_artifact_rel: str,
    current_artifact_id: str,
    old_delta: str,
    old_hash: str,
) -> None:
    token_map = {
        "gate": current_gate_rel,
        "artifact_path": current_artifact_rel,
        "artifact_id": current_artifact_id,
        "delta": old_delta,
        "hash": old_hash,
    }
    for rel, required_tokens in PRECHECK_CONTAINS.items():
        text = _read_text(repo / rel)
        for key in required_tokens:
            token = token_map[key]
            if token not in text:
                raise RuntimeError(f"Preflight failed: expected `{token}` in `{rel}`.")


def main() -> int:
    args = _arg_parser().parse_args()
    repo = _repo_root_from_this_file()

    registry_path = repo / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
    registry = _read_json(registry_path)

    current_gate_rel = registry["sr_m5_theory_parity_gate_path"]
    sr_row = next(row for row in registry["pillars"] if row.get("pillar_id") == "PILLAR-SR")
    current_artifact_rel = sr_row["m5_theory_parity"]["artifact_path"]

    current_cycle = _cycle_from_ref(current_gate_rel)
    next_cycle = args.next_cycle if args.next_cycle is not None else current_cycle + 1
    if next_cycle <= current_cycle:
        raise RuntimeError(f"next cycle must be > current cycle ({current_cycle}), got {next_cycle}")

    current_gate_path = repo / current_gate_rel
    current_artifact_path = repo / current_artifact_rel
    if not current_gate_path.exists() or not current_artifact_path.exists():
        raise RuntimeError("Current SR M5 gate/artifact path does not exist.")

    old_hash = _sha256_file(current_artifact_path)

    next_gate_rel = current_gate_rel.replace(f"cycle{current_cycle}", f"cycle{next_cycle}")
    next_artifact_rel = current_artifact_rel.replace(f"cycle{current_cycle}", f"cycle{next_cycle}")
    next_gate_path = repo / next_gate_rel
    next_artifact_path = repo / next_artifact_rel
    if next_gate_path.exists() or next_artifact_path.exists():
        raise RuntimeError("Next cycle gate/artifact already exists; refusing to overwrite.")

    current_artifact_json = _read_json(current_artifact_path)
    current_artifact_id = str(current_artifact_json["artifact_id"])
    old_delta = f"CYCLE{current_cycle}_POINTER_PARITY_ADVANCEMENT_v0"

    _preflight_verify_current_cycle_surface(
        repo=repo,
        current_gate_rel=current_gate_rel,
        current_artifact_rel=current_artifact_rel,
        current_artifact_id=current_artifact_id,
        old_delta=old_delta,
        old_hash=old_hash,
    )

    next_artifact_json = copy.deepcopy(current_artifact_json)
    next_artifact_json["artifact_id"] = str(next_artifact_json["artifact_id"]).replace(
        f"cycle{current_cycle}", f"cycle{next_cycle}"
    )
    payload = next_artifact_json.setdefault("payload", {})
    basis = payload.setdefault("basis", {})
    basis["cycle"] = f"cycle{next_cycle}"
    payload["phase5_advancement_delta_token"] = f"CYCLE{next_cycle}_POINTER_PARITY_ADVANCEMENT_v0"
    payload["generated_on"] = date.today().isoformat()

    next_artifact_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(next_artifact_path, next_artifact_json)
    new_hash = _sha256_file(next_artifact_path)

    current_gate_text = _read_text(current_gate_path)
    next_gate_text = _replace_cycle_tokens(current_gate_text, current_cycle, next_cycle)
    next_gate_path.parent.mkdir(parents=True, exist_ok=True)
    _write_text(next_gate_path, next_gate_text)

    archived_gate_text = _archive_gate_text(current_gate_text)
    _write_text(current_gate_path, archived_gate_text)

    registry["sr_m5_theory_parity_gate_path"] = next_gate_rel
    sr_row["m5_theory_parity"]["artifact_path"] = next_artifact_rel
    sr_row["m5_theory_parity"]["gate_path"] = next_gate_rel
    _write_json(registry_path, registry)

    next_artifact_id = next_artifact_json["artifact_id"]
    new_delta = f"CYCLE{next_cycle}_POINTER_PARITY_ADVANCEMENT_v0"

    for rel in CANONICAL_UPDATE_FILES:
        path = repo / rel
        text = _read_text(path)
        updated = text
        updated = updated.replace(current_gate_rel, next_gate_rel)
        updated = updated.replace(current_artifact_rel, next_artifact_rel)
        updated = updated.replace(current_artifact_id, next_artifact_id)
        updated = updated.replace(old_delta, new_delta)
        updated = updated.replace(old_hash, new_hash)
        if updated != text:
            _write_text(path, updated)

    print(f"SR M5 rollover complete: cycle{current_cycle} -> cycle{next_cycle}")
    print(f"active gate: {next_gate_rel}")
    print(f"active artifact: {next_artifact_rel}")
    print(f"artifact sha256: {new_hash}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
