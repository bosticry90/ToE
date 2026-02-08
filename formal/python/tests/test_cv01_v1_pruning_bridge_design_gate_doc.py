from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC = REPO_ROOT / "formal" / "docs" / "cv01_v1_pruning_bridge_design_gate.md"


def test_cv01_v1_pruning_bridge_design_gate_doc_contains_required_constraints():
    text = DOC.read_text(encoding="utf-8")
    required = [
        "design-only",
        "MUST NOT consume CV01 outputs by default",
        "explicit and test-enforced",
        "cv01_fail_linear_vs_curved_speed_inconsistent",
        "deterministic lock proving at least one elimination",
    ]
    for token in required:
        assert token in text, f"Missing token in CV01 pruning bridge design gate doc: {token}"
