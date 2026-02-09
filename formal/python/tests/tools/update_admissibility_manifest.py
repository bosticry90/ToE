from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Dict, List


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))

TOEFORMAL_CONSTRAINTS = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Constraints"
TOEFORMAL_GATES = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Gates"
LEAN_MANIFEST_SRC = TOEFORMAL_CONSTRAINTS / "AD00_AdmissibilityManifest.lean"
MANIFEST_PATH = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest.json"

# Policy: this list must match ToeFormal.Gates.defaultEnabled in
# formal/toe_formal/ToeFormal/Constraints/AD00_AdmissibilityManifest.lean.
#
# We do not parse Lean here (overkill); instead we pin the policy in Python and guard it with tests.
DEFAULT_ENABLED_GATES: List[str] = []


_LEAN_JSON_RE = re.compile(
    r"BEGIN_ADMISSIBILITY_MANIFEST_JSON\s*(\{.*?\})\s*END_ADMISSIBILITY_MANIFEST_JSON",
    flags=re.DOTALL,
)


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_json_canonical(obj: object) -> str:
    b = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _to_relpath(p: Path, repo_root: Path) -> str:
    """Return a stable repo-relative path with forward slashes.

    Raises RuntimeError if p is outside repo_root.
    """

    rp = p.resolve()
    rr = repo_root.resolve()
    try:
        rel = rp.relative_to(rr)
    except ValueError as e:
        raise RuntimeError(f"Path is outside --repo-root: {rp}") from e
    return str(rel).replace("\\", "/")


def load_lean_manifest_literal() -> dict:
    if not LEAN_MANIFEST_SRC.exists():
        raise FileNotFoundError(f"Missing Lean manifest source: {LEAN_MANIFEST_SRC}")
    text = LEAN_MANIFEST_SRC.read_text(encoding="utf-8", errors="replace")
    m = _LEAN_JSON_RE.search(text)
    if m is None:
        raise RuntimeError(
            "Lean manifest source is missing BEGIN/END markers for JSON literal: "
            f"{LEAN_MANIFEST_SRC}"
        )
    return json.loads(m.group(1))


def list_gate_files(prefix: str) -> List[Path]:
    if not TOEFORMAL_CONSTRAINTS.exists():
        raise FileNotFoundError(f"ToeFormal Constraints root not found: {TOEFORMAL_CONSTRAINTS}")
    return sorted([p for p in TOEFORMAL_CONSTRAINTS.glob(f"{prefix}*.lean") if p.is_file()])


def tracked_hashes(files: List[Path], *, repo_root: Path) -> Dict[str, str]:
    tracked: Dict[str, str] = {}
    for p in files:
        tracked[_to_relpath(p, repo_root)] = sha256_file(p)
    return dict(sorted(tracked.items()))


def lean_gate_file(gate_id: str) -> Path:
    """Return the Lean stub gate file for a given gate id."""
    if gate_id not in {"CT01", "SYM01", "CAUS01"}:
        raise ValueError(f"Unknown gate id: {gate_id}")
    return TOEFORMAL_GATES / f"{gate_id}.lean"


def _resolve_under(repo_root: Path, p: str | None, *, default: Path) -> Path:
    if p is None:
        return default
    pp = Path(p)
    if pp.is_absolute():
        return pp
    return repo_root / pp


def _load_existing_manifest_enabled(manifest_path: Path, gate_ids: list[str]) -> dict[str, bool]:
    if not manifest_path.exists():
        # Conservative default: start disabled.
        return {k: False for k in gate_ids}
    try:
        obj = json.loads(manifest_path.read_text(encoding="utf-8"))
    except Exception:
        # If manifest is corrupt, force a hard failure.
        raise RuntimeError(f"Existing manifest is not valid JSON: {manifest_path}")

    gates = obj.get("gates", {})
    if not isinstance(gates, dict):
        return {k: False for k in gate_ids}
    out: dict[str, bool] = {}
    for k in gate_ids:
        out[k] = bool(gates.get(k, {}).get("enabled", False))
    return out


def _compute_desired_enabled_from_lean(lean_lit: dict, gate_ids: list[str]) -> dict[str, bool]:
    desired = {k: bool(lean_lit.get("gates", {}).get(k, {}).get("enabled", False)) for k in gate_ids}

    # Extra guard: Lean literal enablement must match pinned Python policy.
    # This ensures “Lean is source of truth” is not purely rhetorical.
    policy_set = set(DEFAULT_ENABLED_GATES)
    desired_set = {k for k, v in desired.items() if bool(v)}
    if desired_set != policy_set:
        raise RuntimeError(
            "Lean gate enablement does not match pinned Python policy. "
            f"Lean enabled={sorted(desired_set)}, Python DEFAULT_ENABLED_GATES={sorted(policy_set)}"
        )
    return desired


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Update admissibility manifest (deterministic).")
    p.add_argument(
        "--allow-enable",
        action="store_true",
        help="Allow enabling gates (false→true) based on Lean intent. Without this flag, enabling is refused.",
    )
    p.add_argument(
        "--enable-gates",
        default=None,
        help=(
            "Explicitly enable a comma-separated list of gates (CT01,SYM01,CAUS01). "
            "Requires --allow-enable. Does not change Lean defaults; intended for writing a separate override manifest."
        ),
    )
    p.add_argument("--repo-root", default=None, help="Override repo root (for tests).")
    p.add_argument("--manifest-path", default=None, help="Override output manifest path (for tests).")
    p.add_argument("--lean-manifest-src", default=None, help="Override Lean manifest literal source path (for tests).")
    p.add_argument("--constraints-root", default=None, help="Override ToeFormal/Constraints root (for tests).")
    p.add_argument("--gates-root", default=None, help="Override ToeFormal/Gates root (for tests).")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    global TOEFORMAL_CONSTRAINTS, TOEFORMAL_GATES, LEAN_MANIFEST_SRC

    args = parse_args(argv)

    repo_root = REPO_ROOT if args.repo_root is None else Path(args.repo_root).resolve()
    constraints_root = _resolve_under(repo_root, args.constraints_root, default=TOEFORMAL_CONSTRAINTS)
    gates_root = _resolve_under(repo_root, args.gates_root, default=TOEFORMAL_GATES)
    lean_manifest_src = _resolve_under(repo_root, args.lean_manifest_src, default=LEAN_MANIFEST_SRC)
    manifest_path = _resolve_under(repo_root, args.manifest_path, default=MANIFEST_PATH)

    # Rebind globals used by helper functions (keeps changes minimal).
    TOEFORMAL_CONSTRAINTS = constraints_root
    TOEFORMAL_GATES = gates_root
    LEAN_MANIFEST_SRC = lean_manifest_src

    manifest_path.parent.mkdir(parents=True, exist_ok=True)

    lean_lit = load_lean_manifest_literal()
    lean_origin_hash = sha256_json_canonical(lean_lit)
    gate_ids = ["CT01", "SYM01", "CAUS01"]

    explicit_enable: list[str] = []
    if args.enable_gates:
        explicit_enable = [s.strip() for s in str(args.enable_gates).split(",") if s.strip()]
        unknown = sorted([g for g in explicit_enable if g not in set(gate_ids)])
        if unknown:
            sys.stderr.write("Unknown gate ids in --enable-gates: " + ",".join(unknown) + "\n")
            return 2

    desired_enabled = _compute_desired_enabled_from_lean(lean_lit, gate_ids)
    existing_enabled = _load_existing_manifest_enabled(manifest_path, gate_ids)

    # Target enablement combines Lean intent (source-of-truth) with any explicit enable list.
    # Explicit enablement is intended for writing a separate override manifest without changing Lean defaults.
    target_enabled: dict[str, bool] = {}
    for k in gate_ids:
        target_enabled[k] = bool(desired_enabled[k]) or (k in set(explicit_enable))

    # One-way sync rule:
    # - Disabling is always allowed (safe).
    # - Enabling (false→true) is refused unless --allow-enable is provided.
    to_enable = [k for k in gate_ids if target_enabled[k] and not existing_enabled.get(k, False)]
    to_enable = sorted(set(to_enable))
    if to_enable and not bool(args.allow_enable):
        sys.stderr.write(
            "Refusing to enable gates without --allow-enable: " + ",".join(to_enable) + "\n"
        )
        return 2

    final_enabled = dict(target_enabled)

    ct_files = list_gate_files("CT01_")
    sym_files = list_gate_files("SYM01_")
    caus_files = list_gate_files("CAUS01_")

    gates = {
        "CT01": {
            "enabled": bool(final_enabled["CT01"]),
            "tracked": tracked_hashes(ct_files, repo_root=repo_root),
        },
        "SYM01": {
            "enabled": bool(final_enabled["SYM01"]),
            "tracked": tracked_hashes(sym_files, repo_root=repo_root),
        },
        "CAUS01": {
            "enabled": bool(final_enabled["CAUS01"]),
            "tracked": tracked_hashes(caus_files, repo_root=repo_root),
        },
    }

    # Attach deterministic tracking for Lean gate predicate stubs.
    for gate_id in gate_ids:
        p = lean_gate_file(gate_id)
        if not p.exists():
            raise FileNotFoundError(f"Missing Lean gate stub: {p}")
        gates[gate_id]["lean_relpath"] = _to_relpath(p, repo_root)
        gates[gate_id]["lean_sha256"] = sha256_file(p)

    all_tracked: Dict[str, str] = {}
    for g in gates.values():
        all_tracked.update(g["tracked"])
    all_tracked = dict(sorted(all_tracked.items()))

    manifest = {
        "version": 1,
        "root": "formal/toe_formal/ToeFormal/Constraints",
        "origin": {
            "type": "lean_literal",
            "path": _to_relpath(LEAN_MANIFEST_SRC, repo_root),
            "sha256": str(lean_origin_hash),
        },
        "gates": gates,
        "tracked": all_tracked,
    }

    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Updated manifest: {manifest_path}")
    print(f"Tracked files: {len(all_tracked)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
