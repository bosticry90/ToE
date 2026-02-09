from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.crft_surface_feasibility_scan import scan_crft_surface_feasibility


def test_crft_surface_feasibility_scan_is_deterministic(tmp_path: Path) -> None:
    repo_root = tmp_path

    # Minimal repo skeleton.
    (repo_root / "formal" / "python" / "crft").mkdir(parents=True, exist_ok=True)
    (repo_root / "formal" / "python" / "toe" / "observables").mkdir(parents=True, exist_ok=True)

    # No CRFT turbulence surface.
    (repo_root / "formal" / "python" / "crft" / "cp_nlse_2d.py").write_text("# no turbulence here\n", encoding="utf-8")

    # Related non-CRFT observable contains a keyword.
    (repo_root / "formal" / "python" / "toe" / "observables" / "ov_dummy.py").write_text(
        "# turbulence spectrum\n",
        encoding="utf-8",
    )

    p1 = scan_crft_surface_feasibility(repo_root=repo_root, token="C8")
    p2 = scan_crft_surface_feasibility(repo_root=repo_root, token="C8")

    assert json.dumps(p1, sort_keys=True) == json.dumps(p2, sort_keys=True)
    assert p1["surface"]["token"] == "C8"
    assert p1["found"] is False
    assert p1["canonical_front_doors"] == []
    assert len(p1["related_non_crft_surfaces"]) == 1
