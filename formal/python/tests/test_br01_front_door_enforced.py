import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
assert (REPO_ROOT / "formal" / "python" / "tests").exists(), (
    "Repo-root resolution invariant failed; expected formal/python/tests at computed root: "
    f"{REPO_ROOT}"
)

# Hard policy: do not import candidate internals outside the allowlist.
FORBIDDEN_IMPORT = re.compile(
    r"(^|\n)\s*("
    r"from\s+formal\.python\.toe\.bridges\.br01_candidates\s+import\s+"
    r"|import\s+formal\.python\.toe\.bridges\.br01_candidates\b"
    r"|from\s+formal\.python\.toe\.bridges\s+import\s+br01_candidates\b"
    r")",
    re.M,
)

ALLOWLIST_SUFFIXES = {
    "formal/python/toe/bridges/br01_dispersion_to_metric.py",
    "formal/python/toe/bridges/br01_candidates.py",
    "formal/python/tests/test_br01_front_door_enforced.py",
    "formal/python/tests/test_br01_candidate_table.py",
}


def _iter_py_files():
    scan_root = REPO_ROOT / "formal" / "python"
    assert scan_root.exists(), f"Expected scan root does not exist: {scan_root}"
    for path in scan_root.rglob("*.py"):
        yield path


def _rel_posix(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT).as_posix()


def test_br01_front_door_forbids_internal_candidate_imports():
    offenders = []
    for path in _iter_py_files():
        rel = _rel_posix(path)
        if rel in ALLOWLIST_SUFFIXES:
            continue
        text = path.read_text(encoding="utf-8")
        if FORBIDDEN_IMPORT.search(text):
            offenders.append(rel)

    assert not offenders, (
        "BR-01 front-door violation: files import br01_candidates directly. "
        "Import formal.python.toe.bridges.br01_dispersion_to_metric instead. "
        f"Offenders: {offenders}"
    )
