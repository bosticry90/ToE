from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC = REPO_ROOT / "formal" / "docs" / "first_empirical_comparator_domain_bec_bragg.md"


def test_first_empirical_comparator_domain_is_pinned_and_bec_bragg():
    text = DOC.read_text(encoding="utf-8")
    assert "Domain ID: `DRBR-DOMAIN-01`" in text
    assert "Selected domain: BEC Bragg" in text
    assert "no status upgrade" in text


def test_first_empirical_comparator_domain_references_typed_fingerprinted_artifacts():
    text = DOC.read_text(encoding="utf-8")
    assert "dr01_fit_artifact.json" in text
    assert "dr01_fit_artifact_curved.json" in text
    assert "data_fingerprint" in text
    assert "source_kind" in text
    assert "source_ref" in text
