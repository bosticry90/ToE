import re
from pathlib import Path


# Lean-side FN-01 “front door” enforcement:
# If a Lean file references an FN-01 named candidate (P_cubic, P_conj, ...)
# or a per-candidate DR corollary, it must import the Candidate API module.


LEAN_ROOT = Path(__file__).resolve().parents[2] / "toe_formal" / "ToeFormal"


CANDIDATE_TOKENS = [
    "P_cubic",
    "P_conj",
    "P_xpsi",
    "P_lap",
    "P_dxx",
    "P_dxx_minus_dyy",
    "P_constant_source",
    "preserves_DR01_onPlaneWaves_of_P_cubic",
    "preserves_DR01_onPlaneWaves_of_P_xpsi",
    "preserves_DR01_onPlaneWaves_of_P_lap",
    "preserves_DR01_onPlaneWaves_of_P_dxx",
    "preserves_DR01_onPlaneWaves_of_P_dxx_minus_dyy",
]


# Files allowed to mention candidate tokens without importing the API.
ALLOWLIST_SUFFIXES = {
    "ToeFormal/Constraints/FN01_CandidateMembership.lean",
    "ToeFormal/Constraints/FN01_CandidateAPI.lean",
}


IMPORT_PATTERN = re.compile(r"^import\s+ToeFormal\.Constraints\.FN01_CandidateAPI\s*$", re.M)
MEMBERSHIP_IMPORT_PATTERN = re.compile(r"^import\s+ToeFormal\.Constraints\.FN01_CandidateMembership\s*$", re.M)


def _rel_posix(path: Path) -> str:
    return path.as_posix().split("/toe_formal/")[-1]


def _iter_lean_files():
    assert LEAN_ROOT.exists(), f"Lean root not found: {LEAN_ROOT}"
    yield from LEAN_ROOT.rglob("*.lean")


def _mentions_candidate_token(text: str) -> bool:
    # Token-level search to avoid matching arbitrary 'P_' identifiers.
    for tok in CANDIDATE_TOKENS:
        if re.search(rf"\b{re.escape(tok)}\b", text):
            return True
    return False


def test_fn01_candidate_api_front_door_enforced():
    offenders = []
    raw_import_offenders = []

    for path in _iter_lean_files():
        rel = _rel_posix(path)
        if rel in ALLOWLIST_SUFFIXES:
            continue

        text = path.read_text(encoding="utf-8")

        # Hard rule: no direct imports of the membership module outside the allowlist.
        # Everyone should import CandidateAPI instead.
        if MEMBERSHIP_IMPORT_PATTERN.search(text):
            raw_import_offenders.append(rel)

        if not _mentions_candidate_token(text):
            continue

        if not IMPORT_PATTERN.search(text):
            offenders.append(rel)

    assert not raw_import_offenders, (
        "Lean-side FN-01 front-door violation: files directly import ToeFormal.Constraints.FN01_CandidateMembership. "
        "Import ToeFormal.Constraints.FN01_CandidateAPI instead (or update allowlist if intentional). "
        f"Offenders: {raw_import_offenders}"
    )

    assert not offenders, (
        "Lean-side FN-01 front-door violation: files reference named FN candidates "
        "or per-candidate DR corollaries without importing ToeFormal.Constraints.FN01_CandidateAPI. "
        "Add `import ToeFormal.Constraints.FN01_CandidateAPI` to each file, or update allowlist if intentional. "
        f"Offenders: {offenders}"
    )
