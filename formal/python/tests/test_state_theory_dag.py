# C:\Users\psboy\Documents\ToE\formal\python\tests\test_state_theory_dag.py
from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, List, Set, Tuple


# ----------------------------
# Repo rooting (NO git needed)
# ----------------------------
def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


# ----------------------------
# Locate canonical inventory file
# ----------------------------
def locate_state_of_the_theory(repo_root: Path) -> Path:
    primary = repo_root / "State_of_the_Theory.md"

    def _norm(p: Path) -> str:
        # Windows filesystems are often case-insensitive, so treat same-resolved-path
        # (modulo case) as the same file to avoid false drift failures.
        return str(p.resolve()).replace("\\", "/").lower()

    legacy_candidates = [
        repo_root / "State of the Theory.md",
        repo_root / "state_of_the_theory.md",
        repo_root / "STATE_OF_THE_THEORY.md",
        repo_root / "formal" / "State_of_the_Theory.md",
        repo_root / "formal" / "State of the Theory.md",
        repo_root / "formal" / "state_of_the_theory.md",
        repo_root / "formal" / "STATE_OF_THE_THEORY.md",
    ]

    if primary.exists():
        primary_key = _norm(primary)
        offenders = [p for p in legacy_candidates if p.exists() and _norm(p) != primary_key]
        assert not offenders, (
            "Inventory file drift detected. Canonical file exists, but legacy copies also exist:\n"
            + "\n".join([f"  - {p}" for p in offenders])
            + "\nFix: keep only repo-root State_of_the_Theory.md."
        )
        return primary

    hits = [p for p in legacy_candidates if p.exists()]
    # De-dup in case of case-insensitive aliases.
    dedup: Dict[str, Path] = {}
    for p in hits:
        dedup.setdefault(_norm(p), p)
    uniq = list(dedup.values())

    assert len(uniq) == 1, (
        "Could not uniquely locate State_of_the_Theory.md.\n"
        "Expected exactly one inventory file among candidates, found:\n"
        + "\n".join([f"  - {p}" for p in uniq])
        + "\nFix: create repo-root State_of_the_Theory.md and delete/move all other copies."
    )
    return uniq[0]


STATE_PATH = locate_state_of_the_theory(REPO_ROOT)


# ----------------------------
# Parsing helpers
# ----------------------------
ID_LINE = re.compile(r"^\s*ID:\s*(\S+)\s*$")
DEP_LINE = re.compile(r"^\s*Dependencies:\s*(.*?)\s*$")

# Treat as "path-like evidence" if it contains a slash/backslash OR ends with a common artifact suffix.
PATHLIKE_SUFFIXES = (
    ".lean",
    ".py",
    ".md",
    ".pdf",
    ".csv",
    ".png",
    ".jpg",
    ".jpeg",
    ".txt",
    ".json",
    ".yml",
    ".yaml",
    ".toml",
    ".ipynb",
)
PATHLIKE_HAS_SLASH = re.compile(r"[\\/]")


def parse_dependencies_field(raw: str) -> List[str]:
    raw = raw.strip()
    if not raw or raw.lower() == "none":
        return []
    # Dependencies must be IDs only (per your rules). Support comma-separated.
    parts = [p.strip() for p in raw.split(",") if p.strip()]
    return parts


def parse_inventory_dependencies(md_text: str) -> Dict[str, List[str]]:
    """
    Parses inventory entries of the canonical form:
      ID:
      ...
      Dependencies:
      ...
    into a dict mapping ID -> dependency list.
    """
    lines = md_text.splitlines()
    items: Dict[str, List[str]] = {}

    current_id: str | None = None
    current_deps: List[str] = []

    def flush():
        nonlocal current_id, current_deps
        if current_id is not None:
            if current_id in items:
                raise AssertionError(f"Duplicate inventory ID detected: {current_id}")
            items[current_id] = list(current_deps)
        current_id = None
        current_deps = []

    for line in lines:
        m_id = ID_LINE.match(line)
        if m_id:
            flush()
            current_id = m_id.group(1)
            continue

        if current_id is None:
            continue

        m_dep = DEP_LINE.match(line)
        if m_dep:
            current_deps = parse_dependencies_field(m_dep.group(1))
            continue

    flush()
    return items


def is_pathlike(token: str) -> bool:
    t = token.strip()
    if PATHLIKE_HAS_SLASH.search(t):
        return True
    tl = t.lower()
    return any(tl.endswith(suf) for suf in PATHLIKE_SUFFIXES)


def normalize_rel_path(token: str) -> str:
    # normalize to forward slashes
    return token.strip().replace("\\", "/")


def assert_no_cycles(graph: Dict[str, List[str]]) -> None:
    visiting: Set[str] = set()
    visited: Set[str] = set()

    def dfs(n: str, stack: List[str]) -> None:
        if n in visited:
            return
        if n in visiting:
            cycle_start = stack.index(n) if n in stack else 0
            cycle = stack[cycle_start:] + [n]
            raise AssertionError(f"Dependency cycle detected: {' -> '.join(cycle)}")
        visiting.add(n)
        stack.append(n)
        for m in graph.get(n, []):
            dfs(m, stack)
        stack.pop()
        visiting.remove(n)
        visited.add(n)

    for node in graph.keys():
        dfs(node, [])


# ----------------------------
# Tests
# ----------------------------
def test_inventory_ids_exist_and_dependencies_are_valid_and_acyclic():
    text = STATE_PATH.read_text(encoding="utf-8", errors="replace")
    items = parse_inventory_dependencies(text)

    assert items, f"No inventory items parsed from {STATE_PATH}"

    missing_deps: List[Tuple[str, str]] = []
    bad_dep_tokens: List[Tuple[str, str]] = []

    # Build dependency graph
    graph: Dict[str, List[str]] = {}

    for iid, deps_raw in items.items():
        deps = []
        for d in deps_raw:
            # Enforce "IDs only" rule for dependencies (no slashes, no file suffixes).
            if is_pathlike(d):
                bad_dep_tokens.append((iid, d))
                continue
            if d not in items:
                missing_deps.append((iid, d))
                continue
            deps.append(d)
        graph[iid] = deps

    assert not bad_dep_tokens, (
        "Dependencies field contains path-like tokens (violates 'IDs only' rule):\n"
        + "\n".join([f"  {src} -> {tok}" for src, tok in bad_dep_tokens])
    )

    assert not missing_deps, (
        "Missing dependency IDs referenced in Dependencies fields:\n"
        + "\n".join([f"  {src} -> {dep}" for src, dep in missing_deps])
    )

    assert_no_cycles(graph)
