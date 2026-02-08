from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC = REPO_ROOT / "formal" / "docs" / "second_empirical_comparator_domain_design_gate.md"


def test_second_empirical_comparator_domain_design_gate_doc_contains_required_constraints():
    text = DOC.read_text(encoding="utf-8")
    required = [
        "Domain ID (design): `DRBR-DOMAIN-02`",
        "design-only",
        "typed artifact schema with deterministic fingerprints",
        "does not select or activate `DRBR-DOMAIN-02`",
    ]
    for token in required:
        assert token in text, f"Missing token in second domain design gate doc: {token}"
