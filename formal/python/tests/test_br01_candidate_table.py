import ast
from pathlib import Path

from formal.python.toe.bridges import br01_candidates as cands


REPO_ROOT = Path(__file__).resolve().parents[3]
assert (REPO_ROOT / "formal" / "python" / "tests").exists(), (
    "Repo-root resolution invariant failed; expected formal/python/tests at computed root: "
    f"{REPO_ROOT}"
)
CANDIDATE_FILE = REPO_ROOT / "formal" / "python" / "toe" / "bridges" / "br01_candidates.py"


def _find_candidate_defs() -> set[str]:
    tree = ast.parse(CANDIDATE_FILE.read_text(encoding="utf-8"), filename=str(CANDIDATE_FILE))
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name.startswith("BR01_"):
            names.add(node.name)
    return names


def test_br01_candidate_table_is_complete_and_not_stale():
    # Canonical candidate registry for BR-01. If/when multiple candidates are introduced,
    # they must be named and tabled here.
    table = {
        "BR01_metric_from_DR01_fit_unit_density": {
            "fn": cands.BR01_metric_from_DR01_fit_unit_density,
            "uses_dr01_fit": True,
        },
        "BR01_metric_from_DR01_fit_constant_density": {
            "fn": cands.BR01_metric_from_DR01_fit_constant_density,
            "uses_dr01_fit": True,
        },
        "BR01_metric_from_DR01_fit_rest_frame_u0": {
            "fn": cands.BR01_metric_from_DR01_fit_rest_frame_u0,
            "uses_dr01_fit": True,
        },
        "BR01_metric_from_DR01_fit_unit_density_structural_fail": {
            "fn": cands.BR01_metric_from_DR01_fit_unit_density_structural_fail,
            "uses_dr01_fit": True,
        },
    }

    for name, spec in table.items():
        assert spec["uses_dr01_fit"], f"BR-01 candidate must use DR-01 fit artifact: {name}"

    defined = _find_candidate_defs()
    tabled = set(table.keys())

    missing = sorted(defined - tabled)
    stale = sorted(tabled - defined)

    assert not missing, f"Missing BR-01 candidates in table: {missing}"
    assert not stale, f"Stale BR-01 candidates in table: {stale}"
