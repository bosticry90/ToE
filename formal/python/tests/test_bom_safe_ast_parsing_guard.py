from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]

BOM_SAFE_AST_SOURCES = [
    REPO_ROOT / "formal" / "python" / "tests" / "test_br01_candidate_table.py",
    REPO_ROOT / "formal" / "python" / "tests" / "test_ov_dr_br01_candidate_family_coverage.py",
    REPO_ROOT / "formal" / "python" / "tests" / "test_ov_dr_br01_no_implicit_cv01_coupling.py",
    REPO_ROOT / "formal" / "python" / "toe" / "observables" / "ovdrbr00_br01_prediction_declarations_record.py",
    REPO_ROOT / "formal" / "python" / "toe" / "observables" / "ovdrbr01_candidate_pruning_table_record.py",
    REPO_ROOT
    / "formal"
    / "python"
    / "toe"
    / "observables"
    / "ovbrfn00_fn01_metric_residual_prediction_declarations_record.py",
    REPO_ROOT / "formal" / "python" / "toe" / "observables" / "ovfnwt00_fn01_weight_policy_declarations_record.py",
]


def test_bom_safe_ast_read_paths_use_utf8_sig() -> None:
    missing: list[str] = []
    for path in BOM_SAFE_AST_SOURCES:
        text = path.read_text(encoding="utf-8")
        if 'read_text(encoding="utf-8-sig")' not in text:
            missing.append(str(path.relative_to(REPO_ROOT)))

    assert not missing, (
        "AST source parsers must use utf-8-sig for BOM-safe decoding in guarded files: "
        + ", ".join(sorted(missing))
    )
