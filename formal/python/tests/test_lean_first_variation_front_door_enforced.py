import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
assert (REPO_ROOT / "formal" / "python" / "tests").exists(), (
    "Repo-root resolution invariant failed; expected formal/python/tests at computed root: "
    f"{REPO_ROOT}"
)

# Hard policy: do not import the legacy Field2D lane outside the allowlist.
FORBIDDEN_IMPORT = re.compile(
    r"(^|\n)\s*import\s+ToeFormal\.Variational\.FirstVariationDeclared\b",
    re.M,
)

ALLOWLIST_SUFFIXES = {
    "formal/toe_formal/ToeFormal/Variational/FirstVariationDeclared.lean",
    "formal/toe_formal/ToeFormal/Variational/FirstVariationUniqueness.lean",
    "formal/toe_formal/ToeFormal/Variational/DischargeELMatchesFN01Pcubic.lean",
    "formal/python/tests/test_lean_first_variation_front_door_enforced.py",
}


def _iter_lean_files():
    scan_root = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal"
    assert scan_root.exists(), f"Expected scan root does not exist: {scan_root}"
    for path in scan_root.rglob("*.lean"):
        yield path


def _rel_posix(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT).as_posix()


def test_first_variation_front_door_forbids_legacy_imports():
    offenders = []
    for path in _iter_lean_files():
        rel = _rel_posix(path)
        if rel in ALLOWLIST_SUFFIXES:
            continue
        text = path.read_text(encoding="utf-8")
        if FORBIDDEN_IMPORT.search(text):
            offenders.append(rel)

    assert not offenders, (
        "First-variation front-door violation: files import the legacy Field2D lane. "
        "Import ToeFormal.Variational.FirstVariationDeclaredFrontDoor instead. "
        f"Offenders: {offenders}"
    )
