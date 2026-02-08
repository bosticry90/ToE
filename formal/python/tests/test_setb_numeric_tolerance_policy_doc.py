from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC = REPO_ROOT / "formal" / "docs" / "setb_numeric_tolerance_policy.md"


def test_setb_numeric_tolerance_policy_doc_declares_profiles():
    text = DOC.read_text(encoding="utf-8")
    assert "TOE_NUMERIC_TOLERANCE_PROFILE" in text
    assert "`pinned`" in text
    assert "`portable`" in text
