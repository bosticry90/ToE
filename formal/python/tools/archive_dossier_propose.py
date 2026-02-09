from __future__ import annotations

"""Archive dossier proposal generator (quarantine-safe).

Goal
- Rank legacy `archive/` items for reintegration triage.
- Emit 10 (default) deterministic dossier stubs under `formal/quarantine/dossiers/`.

Policy alignment
- Read-only access to archive files.
- Does not import from `archive/`.
- Bookkeeping only: no epistemic status changes.

Outputs
- `formal/output/archive_candidate_ranking.json`
- `formal/quarantine/dossiers/DOSSIER_0001_<slug>.md` ...
"""

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
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple


KEYWORDS: Tuple[str, ...] = (
    "ucff",
    "crft",
    "lcrd",
    "cp-nlse",
    "coherence functional",
    "spectral",
    "soliton",
    "lagrangian",
    "euler-lagrange",
    "dispersion",
    "sympy",
    "equation",
    "front door",
    "front_door",
    "observable",
)

REF_TOKENS: Tuple[str, ...] = (
    "lock_",
    "ov-",
    "mt-",
    "state_of_the_theory",
    "equation_inventory",
    "front_door",
    "observable",
)

PENALTY_TOKENS: Tuple[Tuple[str, int], ...] = (
    ("__pycache__", 80),
    (".pyc", 80),
    ("housekeeping_log", 200),
    ("logs", 20),
    ("deprecated", 20),
    ("old", 10),
    ("junk", 30),
)


DOC_FAMILY_PENALTIES: Tuple[Tuple[str, int], ...] = (
    ("equation_inventory", 80),
    ("state_of_the_theory", 60),
    ("inventory", 20),
)


def _is_doc_family(path_lower: str) -> bool:
    return any(tok in path_lower for tok, _ in DOC_FAMILY_PENALTIES)


def _doc_family_penalty(path_lower: str) -> int:
    penalty = 0
    for tok, p in DOC_FAMILY_PENALTIES:
        if tok in path_lower:
            penalty -= p
    return penalty


def _doc_family_key(path: str) -> str:
    # Group versioned variants deterministically.
    # Example: equation_inventory_finalv5.md -> equation_inventory_final.md
    p = path.replace("\\", "/")
    p = re.sub(r"v\d+(?=\.[a-zA-Z0-9]+$)", "", p)
    return p.lower()


def _collect_surface_tokens(repo_root: Path) -> Tuple[str, ...]:
    # Deterministically collect non-archive identifiers that represent existing
    # canonical surfaces (modules, locks). Keep tokens specific to reduce false hits.
    tokens: set[str] = {
        "ov-ucff-",
        "mt-01a",
        "formal/python/crft/acoustic_metric.py",
        "formal.python.crft.acoustic_metric",
    }

    def add_relpath_token(p: Path) -> None:
        rel = str(p.relative_to(repo_root)).replace("\\", "/").lower()
        tokens.add(rel)

    crft_root = repo_root / "formal" / "python" / "crft"
    if crft_root.exists():
        for p in sorted(crft_root.rglob("*.py")):
            add_relpath_token(p)
            tokens.add(f"formal.python.crft.{p.stem.lower()}")

    obs_root = repo_root / "formal" / "python" / "toe" / "observables"
    if obs_root.exists():
        for p in sorted(obs_root.rglob("*.py")):
            add_relpath_token(p)
            if p.stem.lower().startswith("ovucff"):
                tokens.add(p.stem.lower())

    locks_root = repo_root / "formal" / "markdown locks"
    if locks_root.exists():
        for p in sorted([pp for pp in locks_root.rglob("*.md") if pp.is_file()]):
            tokens.add(p.stem.lower())

    toks = sorted(tokens)
    if len(toks) > 5000:
        toks = toks[:5000]
    return tuple(toks)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _read_text_best_effort(p: Path, limit: int = 256_000) -> str:
    data = p.read_bytes()
    if len(data) > limit:
        data = data[:limit]
    return data.decode("utf-8", errors="replace")


def _slugify(path: str, max_len: int = 60) -> str:
    s = path.replace("\\", "/")
    s = re.sub(r"[^a-zA-Z0-9]+", "_", s).strip("_").lower()
    if len(s) > max_len:
        s = s[:max_len].rstrip("_")
    return s or "item"


def _count_equation_signals(kind: str, text: str) -> int:
    # Lightweight, deterministic heuristic.
    t = text
    if kind in {"markdown", "text"}:
        return (
            t.count("$$")
            + t.lower().count("\\begin{equation}")
            + t.lower().count("\\begin{align}")
        )
    if kind == "python":
        return t.count("sympy") + t.count("Eq(") + t.count("Matrix(")
    return 0


@dataclass(frozen=True)
class ScoredCandidate:
    path: str
    sha256: str
    bytes: int
    kind: str
    title: Optional[str]
    docstring: Optional[str]
    score_total: int
    score_base: int
    score_keywords: int
    score_equations: int
    score_refs: int
    score_penalty: int
    score_tests: int
    score_family: int
    score_feasibility: int
    keyword_hits: Tuple[str, ...]
    ref_hits: Tuple[str, ...]
    equation_signals: int
    doc_family_key: str
    doc_family_version_rank: int
    feasibility_hits: Tuple[str, ...]


def score_row(
    repo_root: Path,
    row: Dict[str, Any],
    *,
    doc_family_rank: Dict[str, int],
    surface_tokens: Tuple[str, ...],
) -> ScoredCandidate:
    path = str(row["path"])
    path_lower = path.replace("\\", "/").lower()
    kind = str(row.get("kind") or "")

    base = {
        "python": 50,
        "markdown": 30,
        "text": 5,
        "binary": 0,
    }.get(kind, 0)

    score_tests = 0
    if "/tests/" in path_lower or Path(path_lower).name.startswith("test_"):
        score_tests += 50

    # Optional: enrich with a deterministic text read for better scoring.
    text = ""
    p = repo_root / path
    if kind in {"python", "markdown", "text"} and p.exists():
        text = _read_text_best_effort(p)

    haystack = "\n".join(
        [
            path,
            str(row.get("title") or ""),
            str(row.get("docstring") or ""),
            text,
        ]
    ).lower()

    keyword_hits = tuple(sorted({kw for kw in KEYWORDS if kw in haystack}))
    score_keywords = min(40, 5 * len(keyword_hits))

    equation_signals = _count_equation_signals(kind=kind, text=text)
    if kind in {"markdown", "text"} and _is_doc_family(path_lower):
        score_equations = min(20, 2 * equation_signals)
    else:
        score_equations = min(80, 6 * equation_signals) if kind in {"markdown", "text"} else min(40, 4 * equation_signals)

    ref_hits = tuple(sorted({tok for tok in REF_TOKENS if tok in haystack}))
    score_refs = min(60, 20 * len(ref_hits))

    score_penalty = 0
    for token, penalty in PENALTY_TOKENS:
        if token in path.lower():
            score_penalty -= penalty

    score_family = _doc_family_penalty(path_lower)

    doc_key = _doc_family_key(path)
    version_rank = int(doc_family_rank.get(path_lower, 0))
    if _is_doc_family(doc_key) and version_rank > 0:
        # Prefer lexicographically-highest within family as "newest".
        score_family -= 10 * version_rank

    feasibility_hits = tuple(sorted({t for t in surface_tokens if t and t in haystack}))
    score_feasibility = min(40, 40 if feasibility_hits else 0)

    total = (
        base
        + score_tests
        + score_keywords
        + score_equations
        + score_refs
        + score_family
        + score_feasibility
        + score_penalty
    )

    return ScoredCandidate(
        path=path,
        sha256=str(row["sha256"]),
        bytes=int(row["bytes"]),
        kind=kind,
        title=row.get("title"),
        docstring=row.get("docstring"),
        score_total=int(total),
        score_base=int(base),
        score_keywords=int(score_keywords),
        score_equations=int(score_equations),
        score_refs=int(score_refs),
        score_penalty=int(score_penalty),
        score_tests=int(score_tests),
        score_family=int(score_family),
        score_feasibility=int(score_feasibility),
        keyword_hits=keyword_hits,
        ref_hits=ref_hits,
        equation_signals=int(equation_signals),
        doc_family_key=doc_key,
        doc_family_version_rank=version_rank,
        feasibility_hits=feasibility_hits,
    )


def rank_candidates(repo_root: Path, intake_payload: Dict[str, Any]) -> List[ScoredCandidate]:
    rows = intake_payload.get("files")
    if not isinstance(rows, list):
        raise ValueError("Invalid intake payload: expected 'files' to be a list")

    # Determine family version ranks deterministically across the whole intake set.
    family_to_versions: Dict[str, List[str]] = {}
    for r in rows:
        p = str(r.get("path") or "")
        k = _doc_family_key(p)
        family_to_versions.setdefault(k, []).append(p)
    path_to_version_rank: Dict[str, int] = {}
    for _family_key, versions in family_to_versions.items():
        versions_sorted = sorted(set(versions), reverse=True)
        for idx, original_path in enumerate(versions_sorted):
            # idx=0 => newest by lexicographic order (deterministic)
            path_to_version_rank[original_path.replace("\\", "/").lower()] = idx

    surface_tokens = _collect_surface_tokens(repo_root)

    scored = [
        score_row(
            repo_root,
            r,
            doc_family_rank=path_to_version_rank,
            surface_tokens=surface_tokens,
        )
        for r in rows
    ]
    scored.sort(key=lambda c: (-c.score_total, c.path))
    return scored


def _classify(c: ScoredCandidate) -> str:
    if c.kind == "python":
        return "diagnostic_candidate"
    if c.kind in {"markdown", "text"} and c.equation_signals > 0:
        return "equation_candidate"
    if c.kind in {"markdown", "text"}:
        return "doc_claim_candidate"
    return "reference_only"


def _dossier_markdown(rank: int, c: ScoredCandidate) -> str:
    classification = _classify(c)
    lines: list[str] = []

    lines.append(f"# DOSSIER {rank:04d}: {c.path}")
    lines.append("")
    lines.append("## Source")
    lines.append("")
    lines.append(f"- Path: {c.path}")
    lines.append(f"- SHA256: {c.sha256}")
    lines.append(f"- Bytes: {c.bytes}")
    lines.append(f"- Kind: {c.kind}")
    if c.title:
        lines.append(f"- Title: {c.title}")
    if c.docstring:
        lines.append(f"- Docstring: {c.docstring.splitlines()[0][:200]}")

    lines.append("")
    lines.append("## Why It Scored High")
    lines.append("")
    lines.append(f"- Total: {c.score_total}")
    lines.append(
        "- Breakdown: "
        f"base={c.score_base} tests={c.score_tests} keywords={c.score_keywords} equations={c.score_equations} refs={c.score_refs} family={c.score_family} feasibility={c.score_feasibility} penalty={c.score_penalty}"
    )
    lines.append(f"- Keyword hits: {', '.join(c.keyword_hits) if c.keyword_hits else '(none)'}")
    lines.append(f"- Reference hits: {', '.join(c.ref_hits) if c.ref_hits else '(none)'}")
    lines.append(f"- Equation signals: {c.equation_signals}")
    if c.doc_family_key:
        lines.append(f"- Doc family key: {c.doc_family_key}")
        if c.doc_family_version_rank:
            lines.append(f"- Doc family version rank: {c.doc_family_version_rank} (0=newest)")
    if c.feasibility_hits:
        lines.append(f"- Feasibility hits (non-archive surfaces): {', '.join(c.feasibility_hits[:12])}")

    lines.append("")
    lines.append("## Candidate Classification")
    lines.append("")
    lines.append(f"- Classification: {classification}")

    lines.append("")
    lines.append("## Proposed Reintegration Target")
    lines.append("")
    lines.append("- Existing canonical surface (if any): TBD")
    lines.append("- Otherwise: new front door required (clean-room)")

    lines.append("")
    lines.append("## Validation Plan")
    lines.append("")
    lines.append("- Symbolic: TBD")
    lines.append("- Numeric: TBD")
    lines.append("- Locks/tests: TBD")

    lines.append("")
    lines.append("## Exit Condition")
    lines.append("")
    lines.append("- Accepted / Rejected / Reference-only: TBD")

    return "\n".join(lines) + "\n"


def write_outputs(
    repo_root: Path,
    ranked: List[ScoredCandidate],
    top_n: int,
    ranking_out: Path,
    dossiers_dir: Path,
) -> None:
    dossiers_dir.mkdir(parents=True, exist_ok=True)
    ranking_out.parent.mkdir(parents=True, exist_ok=True)

    # Deterministic output: remove stale dossier stubs from previous runs.
    for p in sorted(dossiers_dir.glob("DOSSIER_*.md")):
        p.unlink()

    top = ranked[:top_n]

    ranking_payload = {
        "schema_version": 1,
        "top_n": top_n,
        "ranked": [
            {
                "path": c.path,
                "sha256": c.sha256,
                "bytes": c.bytes,
                "kind": c.kind,
                "score_total": c.score_total,
                "breakdown": {
                    "base": c.score_base,
                    "tests": c.score_tests,
                    "keywords": c.score_keywords,
                    "equations": c.score_equations,
                    "refs": c.score_refs,
                    "family": c.score_family,
                    "feasibility": c.score_feasibility,
                    "penalty": c.score_penalty,
                },
                "keyword_hits": list(c.keyword_hits),
                "ref_hits": list(c.ref_hits),
                "equation_signals": c.equation_signals,
                "doc_family_key": c.doc_family_key,
                "doc_family_version_rank": c.doc_family_version_rank,
                "feasibility_hits": list(c.feasibility_hits),
                "title": c.title,
                "docstring": c.docstring,
            }
            for c in ranked
        ],
    }

    ranking_out.write_text(
        json.dumps(ranking_payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    # Write top-N dossier stubs deterministically.
    for i, c in enumerate(top, start=1):
        slug = _slugify(c.path)
        dossier_path = dossiers_dir / f"DOSSIER_{i:04d}_{slug}.md"
        dossier_path.write_text(_dossier_markdown(i, c), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Propose top dossier candidates from an archive intake index."
    )
    parser.add_argument(
        "--index",
        default="formal/output/archive_intake_index.json",
        help="Repo-relative path to the archive intake index JSON",
    )
    parser.add_argument(
        "--top",
        type=int,
        default=10,
        help="Number of dossier stubs to generate",
    )
    parser.add_argument(
        "--ranking-out",
        default="formal/output/archive_candidate_ranking.json",
        help="Repo-relative output JSON path for full ranked list",
    )
    parser.add_argument(
        "--dossiers-dir",
        default="formal/quarantine/dossiers",
        help="Repo-relative directory to write dossier stubs",
    )

    args = parser.parse_args(argv)
    if args.top <= 0:
        raise SystemExit("--top must be positive")

    repo_root = _find_repo_root(Path(__file__))

    index_path = repo_root / args.index
    if not index_path.exists():
        raise SystemExit(f"Intake index not found: {args.index}")

    intake_payload = json.loads(index_path.read_text(encoding="utf-8"))
    ranked = rank_candidates(repo_root=repo_root, intake_payload=intake_payload)

    write_outputs(
        repo_root=repo_root,
        ranked=ranked,
        top_n=args.top,
        ranking_out=repo_root / args.ranking_out,
        dossiers_dir=repo_root / args.dossiers_dir,
    )

    # Minimal receipt (deterministic paths only; no timestamps).
    print(str(Path(args.ranking_out).as_posix()))
    print(str(Path(args.dossiers_dir).as_posix()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
