import json
from pathlib import Path

from formal.python.toe.dr01_fit import DR01Fit1D


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC = REPO_ROOT / "formal" / "docs" / "first_empirical_comparator_domain_bec_bragg.md"
ARTIFACT_DIR = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"


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


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _as_sample_kw(raw_sample_kw: list[list[float]]) -> tuple[tuple[float, float], ...]:
    return tuple((float(k), float(w)) for (k, w) in raw_sample_kw)


def test_first_empirical_domain_artifacts_exist_and_fingerprint_checks_hold():
    linear = ARTIFACT_DIR / "dr01_fit_artifact.json"
    curved = ARTIFACT_DIR / "dr01_fit_artifact_curved.json"

    assert linear.exists(), f"Missing pinned domain artifact: {linear}"
    assert curved.exists(), f"Missing pinned domain artifact: {curved}"

    for path in [linear, curved]:
        payload = _load_json(path)
        assert str(payload.get("source_kind", ""))
        assert str(payload.get("source_ref", ""))
        assert str(payload.get("fit_method_tag", ""))
        assert str(payload.get("data_fingerprint", ""))

        sample_kw = _as_sample_kw(payload["sample_kw"])
        expected = DR01Fit1D.data_fingerprint_from_sample(sample_kw)
        assert payload["data_fingerprint"] == expected
