from __future__ import annotations

"""CRFT claims extractor (quarantine-safe).

Goal
- Extract a deterministic, reviewable claim list from a legacy CRFT markdown/text spec.

Policy alignment
- Read-only: loads source file by path.
- Does not import from `archive/`.
- Output is bookkeeping only (no status upgrades).

Output schema (v1)
{
  "schema_version": 1,
  "source": {"path": "...", "sha256": "..."},
  "claims": [
    {"id": "CLM-0001", "section": "...", "kind": "definition|equation|criteria|diagnostic|parameter|note", "text": "..."}
  ],
  "candidate_equations": ["CLM-0007", ...],
  "validation_shortlist": [
    {"claim_id": "CLM-0007", "target_surface": "...", "plan": ["...", "..."], "exit_condition": "..."}
  ]
}
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
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _read_text(p: Path) -> str:
    return p.read_text(encoding="utf-8", errors="replace")


def _is_equation_line(line: str) -> bool:
    s = line.strip()
    if not s:
        return False
    if s.startswith("#"):
        return False
    if s.startswith("•"):
        return False
    # Very lightweight heuristic: equation-like when it contains '=' and at least one symbol.
    if "=" in s and re.search(r"[A-Za-zρφχωλβν∂]", s):
        return True
    # PDE-like forms
    if re.search(r"\b(\w+)_t\b", s) and ("=" in s or "-" in s):
        return True
    return False


@dataclass(frozen=True)
class Claim:
    section: str
    kind: str
    text: str


def extract_claims(text: str) -> List[Claim]:
    claims: List[Claim] = []

    section = "(preamble)"
    in_pass = False
    in_diag = False

    for raw in text.splitlines():
        line = raw.rstrip("\r\n")
        s = line.strip()

        if not s:
            in_pass = False
            in_diag = False
            continue

        # Section headers like "C6 — ..."
        if re.match(r"^C\d+\s+—\s+", s):
            section = s
            in_pass = False
            in_diag = False
            continue

        if s.lower().startswith("purpose:"):
            claims.append(Claim(section=section, kind="note", text=s))
            continue

        if s.lower().startswith("fields:"):
            claims.append(Claim(section=section, kind="note", text=s))
            continue

        if s.lower().startswith("diagnostics:"):
            in_diag = True
            claims.append(Claim(section=section, kind="note", text=s))
            continue

        if s.lower().startswith("pass criteria"):
            in_pass = True
            claims.append(Claim(section=section, kind="note", text=s))
            continue

        if s.lower().startswith("with:"):
            claims.append(Claim(section=section, kind="note", text=s))
            continue

        # Bullet definitions / specs
        if s.startswith("•"):
            claims.append(Claim(section=section, kind="definition", text=s.lstrip("•").strip()))
            continue

        # Indented equations/spec lines
        if _is_equation_line(line):
            kind = "equation"
            if in_pass:
                kind = "criteria"
            elif in_diag:
                kind = "diagnostic"
            claims.append(Claim(section=section, kind=kind, text=s))
            continue

        # Parameter/spec constants
        if re.match(r"^(rho0|g_eff|lam|beta|nu_eff|ν_eff)\b", s, flags=re.IGNORECASE):
            claims.append(Claim(section=section, kind="parameter", text=s))
            continue

        # Keep a small amount of narrative if it contains strong modal language.
        if re.search(r"\b(must|verify|define|consistent|authoritative)\b", s, flags=re.IGNORECASE):
            claims.append(Claim(section=section, kind="note", text=s))

    # Deduplicate exact repeats deterministically while preserving order.
    seen = set()
    out: List[Claim] = []
    for c in claims:
        key = (c.section, c.kind, c.text)
        if key in seen:
            continue
        seen.add(key)
        out.append(c)
    return out


def build_payload(source_path: Path, repo_root: Path) -> dict:
    text = _read_text(source_path)
    claims = extract_claims(text)

    def rel(p: Path) -> str:
        try:
            return p.resolve().relative_to(repo_root.resolve()).as_posix()
        except Exception:
            return p.as_posix()

    # Candidate equations are the equation/criteria items; keep IDs stable by order.
    claim_rows = []
    candidate_equations: List[str] = []

    for i, c in enumerate(claims, start=1):
        cid = f"CLM-{i:04d}"
        claim_rows.append(
            {
                "id": cid,
                "section": c.section,
                "kind": c.kind,
                "text": c.text,
            }
        )
        if c.kind in {"equation", "criteria"}:
            candidate_equations.append(cid)

    def first_claim_id(predicate) -> Optional[str]:
        for row in claim_rows:
            if predicate(row):
                return str(row["id"])
        return None

    def claim_ids(predicate, limit: int) -> List[str]:
        out: List[str] = []
        for row in claim_rows:
            if predicate(row):
                out.append(str(row["id"]))
            if len(out) >= int(limit):
                break
        return out

    validation_shortlist: List[dict] = []

    # C6 — 2D CP–NLSE prototype equation
    c6_cp_nlse_id = first_claim_id(
        lambda r: str(r["section"]).startswith("C6")
        and r["kind"] == "equation"
        and ("∇" in r["text"] or "nabla" in r["text"] or "∂xx" in r["text"])
        and "g_eff" in r["text"]
    )
    if c6_cp_nlse_id is not None:
        validation_shortlist.append(
            {
                "claim_id": c6_cp_nlse_id,
                "target_surface": "formal/python/crft/cp_nlse_2d.py",
                "plan": [
                    "Map PDE sign/phase convention to rhs_cp_nlse_2d().",
                    "Use existing dispersion regression (C6) as the primary executable check.",
                    "Add/confirm a pinned-input norm drift check for N_2D(t) on a periodic grid.",
                ],
                "exit_condition": "C6 dispersion regression passes; norm drift meets spec on pinned grid/time step.",
            }
        )

    # Additional C6 pass-criteria lines (kept as separate tickets for auditability).
    for cid in claim_ids(
        lambda r: str(r["section"]).startswith("C6")
        and r["kind"] in {"definition", "criteria"}
        and ("drift" in r["text"].lower() or "ω" in r["text"] or "omega" in r["text"].lower()),
        limit=2,
    ):
        validation_shortlist.append(
            {
                "claim_id": cid,
                "target_surface": "formal/python/crft/cp_nlse_2d.py",
                "plan": [
                    "Bind the criterion to bounded pytest evidence (norm drift + dispersion/eigenfunction checks).",
                    "Keep inputs deterministic and runtime small.",
                ],
                "exit_condition": "Referenced pytest evidence passes under pinned conditions.",
            }
        )

    # C7 — Acoustic metric diagnostic definition(s)
    c7_acoustic_metric_id = first_claim_id(
        lambda r: str(r["section"]).startswith("C7")
        and r["kind"] == "equation"
        and ("c_s" in r["text"] or "g_tt" in r["text"])
    )
    if c7_acoustic_metric_id is not None:
        validation_shortlist.append(
            {
                "claim_id": c7_acoustic_metric_id,
                "target_surface": "formal/python/crft/acoustic_metric.py",
                "plan": [
                    "Map (rho, u, g_eff) inputs to MT-01a front door.",
                    "Verify g_tt < 0 and det(g) < 0 inequalities pointwise on pinned fields.",
                    "Lean on the existing MT-01a lock regression for stability/compatibility.",
                ],
                "exit_condition": "MT-01a lock regression passes; diagnostic inequalities are verified for pinned inputs.",
            }
        )

    # Additional C7 defining equations (map to the same canonical MT-01a front door).
    for cid in claim_ids(
        lambda r: str(r["section"]).startswith("C7")
        and r["kind"] == "equation"
        and any(tok in r["text"] for tok in ("g_tt", "g_tx", "g_ty", "g_xx", "g_yy")),
        limit=4,
    ):
        validation_shortlist.append(
            {
                "claim_id": cid,
                "target_surface": "formal/python/crft/acoustic_metric.py",
                "plan": [
                    "Validate that MT-01a front door implements this defining equation.",
                    "Verify signature/inequality diagnostics on deterministic pinned inputs.",
                ],
                "exit_condition": "MT-01a lock regression passes; defining equations are consistent with the canonical implementation.",
            }
        )

    return {
        "schema_version": 1,
        "source": {"path": rel(source_path), "sha256": _sha256_path(source_path)},
        "claims": claim_rows,
        "candidate_equations": candidate_equations,
        "validation_shortlist": validation_shortlist,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Extract claims from a CRFT legacy spec.")
    parser.add_argument(
        "--source",
        required=True,
        help="Repo-relative path to the source markdown/text file (may be under archive/)",
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Repo-relative output JSON path (recommended under formal/quarantine/claims)",
    )

    args = parser.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    src = repo_root / args.source
    if not src.exists():
        raise SystemExit(f"Source not found: {args.source}")

    payload = build_payload(source_path=src, repo_root=repo_root)

    out = repo_root / args.out
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(str(Path(args.out).as_posix()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
