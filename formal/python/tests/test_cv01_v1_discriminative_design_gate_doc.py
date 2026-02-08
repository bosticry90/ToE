from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC = REPO_ROOT / "formal" / "docs" / "cv01_v1_discriminative_design_gate.md"


def test_cv01_v1_design_gate_doc_contains_required_constraints():
    text = DOC.read_text(encoding="utf-8")
    required = [
        "integrity_only",
        "non-tautological",
        "linear-vs-curved cross-artifact consistency residual",
        "negative control",
        "Promotion gate",
    ]
    for token in required:
        assert token in text, f"Missing token in CV01 v1 design gate doc: {token}"
