import importlib
import os
from pathlib import Path


def test_imports_survive_arbitrary_cwd(tmp_path):
    nested = tmp_path / "nested" / "deeper"
    nested.mkdir(parents=True, exist_ok=True)

    old_cwd = Path.cwd()
    try:
        os.chdir(nested)
        mod = importlib.import_module("formal.python.toe.bridges.br01_dispersion_to_metric")
        assert hasattr(mod, "br01_metric_from_DR01")
        assert hasattr(mod, "br01_metric_from_DR01_fit")
        assert hasattr(mod, "br01_check_consistency")
    finally:
        os.chdir(old_cwd)
