"""Scan PDF text spans for density-like tokens (debug helper).

Why
- Some figure labels/captions may appear in the PDF text layer with coordinates,
  but not show up cleanly in page.extract_text().

Output
- Prints matches with page number and bounding box in PDF points.
"""

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
import re
from pathlib import Path

import fitz  # PyMuPDF


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--pdf-relpath",
        required=True,
        help="Repo-relative PDF path (must be under formal/external_evidence/).",
    )
    ap.add_argument(
        "--pattern",
        default=r"\b\d+(?:\.\d+)?\s*x\s*10\s*\^?\s*\d+\s*cm\s*-\s*3\b|\b\d+(?:\.\d+)?\s*x\s*10\d+\s*cm\s*-\s*3\b",
        help="Regex to search within span text.",
    )
    args = ap.parse_args(argv)

    pdf_rel = str(args.pdf_relpath).replace("\\", "/")
    if not pdf_rel.startswith("formal/external_evidence/"):
        raise ValueError("pdf-relpath must be under formal/external_evidence/")

    repo_root = _find_repo_root(Path(__file__))
    pdf_path = repo_root / pdf_rel
    doc = fitz.open(str(pdf_path))

    pat = re.compile(str(args.pattern), flags=re.IGNORECASE)

    for page_index in range(int(doc.page_count)):
        page = doc.load_page(page_index)
        d = page.get_text("dict")
        for block in d.get("blocks", []):
            for line in block.get("lines", []):
                for span in line.get("spans", []):
                    txt = str(span.get("text", ""))
                    txt_norm = (
                        txt.replace("\u2212", "-")
                        .replace("\u2013", "-")
                        .replace("\u2014", "-")
                        .replace("\u00d7", "x")
                    )
                    if pat.search(txt_norm) is None:
                        continue
                    bbox = span.get("bbox")
                    print(
                        f"page {page_index+1}: {txt_norm} bbox={bbox} size={span.get('size')} font={span.get('font')}"
                    )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
