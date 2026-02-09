from __future__ import annotations

import inspect


def test_no_module_level_pdfplumber_imports_in_density_records() -> None:
    # Policy test: these modules must not import pdfplumber at module import time.
    # pdfplumber may appear only in lazy import helpers.
    from formal.python.toe.observables import ovsnd03n_central_density_digitized as m03n
    from formal.python.toe.observables import ovsnd03n2_secondary_density_conditions_digitized as m03n2

    src1 = inspect.getsource(m03n)
    src2 = inspect.getsource(m03n2)

    assert "import pdfplumber" in src1
    assert "import pdfplumber" in src2

    # Disallow top-level import statements (we only allow it inside _require_pdfplumber())
    assert "\nimport pdfplumber" not in src1
    assert "\nimport pdfplumber" not in src2

    # Sanity check the helper exists.
    assert "def _require_pdfplumber" in src1
    assert "def _require_pdfplumber" in src2
