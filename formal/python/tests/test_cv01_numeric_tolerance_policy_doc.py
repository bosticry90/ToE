from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC = REPO_ROOT / "formal" / "docs" / "cv01_numeric_tolerance_policy.md"


def test_cv01_numeric_tolerance_policy_doc_declares_profiles():
    text = DOC.read_text(encoding="utf-8")
    assert "TOE_CV01_TOLERANCE_PROFILE" in text
    assert "`pinned`" in text
    assert "`portable`" in text
