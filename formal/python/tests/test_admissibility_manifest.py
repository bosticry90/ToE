from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Dict, List
from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import admissibility_manifest_current_identity as identity


REPO_ROOT = find_repo_root(Path(__file__))

TOEFORMAL_CONSTRAINTS = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Constraints"
TOEFORMAL_GATES = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Gates"
LEAN_MANIFEST_SRC = TOEFORMAL_CONSTRAINTS / "AD00_AdmissibilityManifest.lean"
MANIFEST_PATH = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest.json"


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


def lean_gate_file(gate_id: str) -> Path:
    if gate_id not in {"CT01", "SYM01", "CAUS01"}:
        raise ValueError(f"Unknown gate id: {gate_id}")
    return TOEFORMAL_GATES / f"{gate_id}.lean"


def sha256_json_canonical(obj: object) -> str:
    b = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def load_lean_manifest_literal() -> dict:
    if not LEAN_MANIFEST_SRC.exists():
        raise FileNotFoundError(f"Missing Lean manifest source: {LEAN_MANIFEST_SRC}")
    text = LEAN_MANIFEST_SRC.read_text(encoding="utf-8", errors="replace")
    m = _LEAN_JSON_RE.search(text)
    if m is None:
        raise RuntimeError(f"Missing BEGIN/END JSON markers in: {LEAN_MANIFEST_SRC}")
    return json.loads(m.group(1))


def list_gate_files(prefix: str) -> List[Path]:
    if not TOEFORMAL_CONSTRAINTS.exists():
        return []
    return sorted([p for p in TOEFORMAL_CONSTRAINTS.glob(f"{prefix}*.lean") if p.is_file()])


def compute_current_hashes() -> Dict[str, str]:
    current: Dict[str, str] = {}
    for prefix in ["CT01_", "SYM01_", "CAUS01_"]:
        for p in list_gate_files(prefix):
            rel = str(p.relative_to(REPO_ROOT)).replace("\\", "/")
            current[rel] = sha256_file(p)
    return dict(sorted(current.items()))


def load_manifest() -> Dict:
    if not MANIFEST_PATH.exists():
        raise FileNotFoundError(f"Missing admissibility manifest: {MANIFEST_PATH}")
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def test_admissibility_manifest_exists_and_matches_current():
    assert MANIFEST_PATH.exists(), (
        f"Missing admissibility manifest: {MANIFEST_PATH}\n"
        "To generate it:\n"
        "  python formal\\python\\tests\\tools\\update_admissibility_manifest.py\n"
    )

    manifest = load_manifest()
    resolved = identity.validate_contract()
    current_paths = set(compute_current_hashes())
    contract_paths = {
        path
        for path, binding in resolved.items()
        if binding["role"] == "CURRENT_CONSTRAINT_SOURCE"
    }
    assert contract_paths == current_paths
    assert identity.load_contract()["legacy_manifest"] == {
        "path": "formal/markdown locks/gates/admissibility_manifest.json",
        "role": "HISTORICAL_SNAPSHOT",
        "rewritten": False,
    }
    assert manifest["version"] == 1


def test_admissibility_manifest_origin_matches_lean_literal():
    manifest = load_manifest()
    origin = manifest.get("origin", {})

    assert origin.get("type") == "lean_literal"
    assert origin.get("path") == "formal/toe_formal/ToeFormal/Constraints/AD00_AdmissibilityManifest.lean"

    lean_lit = load_lean_manifest_literal()
    expected = sha256_json_canonical(lean_lit)
    assert origin.get("sha256") == expected

    gates = manifest.get("gates", {})
    for gate_id in ["CT01", "SYM01", "CAUS01"]:
        assert bool(gates.get(gate_id, {}).get("enabled", False)) == bool(
            lean_lit.get("gates", {}).get(gate_id, {}).get("enabled", False)
        )


def test_admissibility_manifest_tracks_lean_gate_stubs_deterministically() -> None:
    manifest = load_manifest()
    gates = manifest.get("gates", {})
    resolved = identity.validate_contract()

    for gate_id in ["CT01", "SYM01", "CAUS01"]:
        entry = gates.get(gate_id, {})
        assert isinstance(entry, dict)

        relpath = entry.get("lean_relpath")
        assert isinstance(relpath, str) and relpath
        p = REPO_ROOT / relpath
        assert p.exists(), f"Lean gate stub missing on disk: {relpath}"
        assert resolved[relpath]["role"] == "CURRENT_GATE_STUB"
        assert len(resolved[relpath]["git_blob"]) == 40
        assert len(resolved[relpath]["sha256"]) == 64


def test_lean_gate_stubs_do_not_imply_enabled_by_default() -> None:
    """Presence of Lean stub files must not be interpreted as an enable signal."""

    manifest = load_manifest()
    gates = manifest.get("gates", {})

    for gate_id in ["CT01", "SYM01", "CAUS01"]:
        # File exists.
        assert lean_gate_file(gate_id).exists()
        # Default posture is disabled unless explicitly enabled.
        assert bool(gates.get(gate_id, {}).get("enabled", False)) is False
