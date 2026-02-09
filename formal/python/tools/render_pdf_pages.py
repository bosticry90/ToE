"""Render PDF pages to deterministic PNGs (for governed digitization).

Purpose
- Produce pinned page images under formal/external_evidence/... so that any
  subsequent figure/table digitization can reference a deterministic raster.

Design constraints
- Deterministic naming and zoom.
- No timestamps in outputs.
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
        "--out-dir-relpath",
        required=True,
        help="Repo-relative output directory (must be under formal/external_evidence/).",
    )
    ap.add_argument("--zoom", type=float, default=4.0, help="Render zoom factor (default 4.0)")
    ap.add_argument(
        "--pages",
        default="all",
        help="Page selector: 'all' or '1,2,5' or '2-4'. 1-based.",
    )
    args = ap.parse_args(argv)

    pdf_rel = str(args.pdf_relpath).replace("\\", "/")
    out_dir_rel = str(args.out_dir_relpath).replace("\\", "/")
    if not pdf_rel.startswith("formal/external_evidence/"):
        raise ValueError("pdf-relpath must be under formal/external_evidence/")
    if not out_dir_rel.startswith("formal/external_evidence/"):
        raise ValueError("out-dir-relpath must be under formal/external_evidence/")

    repo_root = _find_repo_root(Path(__file__))
    pdf_path = repo_root / pdf_rel
    out_dir = repo_root / out_dir_rel
    out_dir.mkdir(parents=True, exist_ok=True)

    doc = fitz.open(str(pdf_path))
    n_pages = int(doc.page_count)

    def parse_pages(spec: str) -> list[int]:
        spec = str(spec).strip().lower()
        if spec == "all":
            return list(range(1, n_pages + 1))
        if "," in spec:
            return [int(x.strip()) for x in spec.split(",") if x.strip()]
        if "-" in spec:
            a, b = spec.split("-", 1)
            start = int(a.strip())
            end = int(b.strip())
            return list(range(start, end + 1))
        return [int(spec)]

    pages = parse_pages(str(args.pages))
    for pno in pages:
        if pno < 1 or pno > n_pages:
            raise ValueError(f"Invalid page number: {pno} (pdf has {n_pages} pages)")
        page = doc.load_page(pno - 1)
        mat = fitz.Matrix(float(args.zoom), float(args.zoom))
        pix = page.get_pixmap(matrix=mat, alpha=False)
        out_path = out_dir / f"page{pno}_z{float(args.zoom):g}.png"
        pix.save(str(out_path))
        print(out_path.as_posix())

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
