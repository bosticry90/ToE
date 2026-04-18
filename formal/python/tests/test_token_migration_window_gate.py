from __future__ import annotations

from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))

MIGRATION_WINDOW_ID = "MIGRATION_WINDOW_QFT_NO_AUTOFIP_TO_NO_AUTOFLIP_v0"
DEPRECATION_WINDOW_START = "2026-02-22"
DEPRECATION_WINDOW_END = "2026-06-30"
DEPRECATION_WINDOW_PHASE = "WITHIN_WINDOW"
LEGACY_TOKEN = "NO_AUTOFIP"
CANONICAL_TOKEN = "NO_AUTOFLIP"

MIGRATION_SURFACES = [
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md",
    REPO_ROOT / "formal" / "python" / "tests" / "test_qft_full_derivation_discharge_gate.py",
]

AUTHORITY_DOC_SURFACES = [
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file for {MIGRATION_WINDOW_ID}: {path}"
    return path.read_text(encoding="utf-8")


def _normalize_surface_text(path: Path, text: str) -> str:
    active_text, _ = split_active_and_archived(text, path)
    return active_text


def _strip_deprecation_header_lines(text: str) -> str:
    keep: list[str] = []
    for line in text.splitlines():
        if "DEPRECATION_WINDOW_START:" in line:
            continue
        if "DEPRECATION_WINDOW_END:" in line:
            continue
        if "DEPRECATION_WINDOW_PHASE:" in line:
            continue
        if "DEPRECATED_TOKENS:" in line:
            continue
        if "REPLACEMENT_TOKENS:" in line:
            continue
        keep.append(line)
    return "\n".join(keep)


def _assert_deprecation_header(text: str, path: Path) -> None:
    required_lines = [
        f"DEPRECATION_WINDOW_START: {DEPRECATION_WINDOW_START}",
        f"DEPRECATION_WINDOW_END: {DEPRECATION_WINDOW_END}",
        f"DEPRECATION_WINDOW_PHASE: {DEPRECATION_WINDOW_PHASE}",
        f"DEPRECATED_TOKENS: {LEGACY_TOKEN}",
        f"REPLACEMENT_TOKENS: {CANONICAL_TOKEN}",
    ]
    missing = [line for line in required_lines if line not in text]
    assert not missing, f"{path}: missing deprecation header field(s): {', '.join(missing)}"


def test_token_migration_window_is_explicit_and_non_silent() -> None:
    assert DEPRECATION_WINDOW_PHASE in {"BEFORE_WINDOW", "WITHIN_WINDOW", "AFTER_WINDOW"}

    seen_legacy = False
    seen_canonical = False

    for path in AUTHORITY_DOC_SURFACES:
        text = _normalize_surface_text(path, _read(path))
        _assert_deprecation_header(text, path)

    for path in MIGRATION_SURFACES:
        text = _normalize_surface_text(path, _read(path))
        usage_text = _strip_deprecation_header_lines(text)
        has_legacy = LEGACY_TOKEN in usage_text
        has_canonical = CANONICAL_TOKEN in usage_text

        if DEPRECATION_WINDOW_PHASE == "BEFORE_WINDOW":
            assert not has_canonical, f"{path}: canonical token appears before migration window opens."
        elif DEPRECATION_WINDOW_PHASE == "WITHIN_WINDOW":
            assert not (has_legacy and has_canonical), (
                f"{path}: mixed legacy and canonical tokens in the same surface is forbidden during migration window."
            )
        elif DEPRECATION_WINDOW_PHASE == "AFTER_WINDOW":
            assert not has_legacy, f"{path}: legacy token persists after migration window close."

        seen_legacy = seen_legacy or has_legacy
        seen_canonical = seen_canonical or has_canonical

    assert seen_legacy or seen_canonical, (
        f"{MIGRATION_WINDOW_ID}: expected at least one governed token occurrence across migration surfaces."
    )
