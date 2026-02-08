from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
PROBE_LADDER_DOC = REPO_ROOT / "formal" / "docs" / "probe_generalization_ladder_ct_sym_caus_br01.md"
UCFF_GATE_DOC = REPO_ROOT / "formal" / "docs" / "ucff_comparator_expansion_design_gate.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required design gate document: {path}"
    return path.read_text(encoding="utf-8")


def test_probe_generalization_ladder_doc_has_abc_sets_and_promotion_gates():
    text = _read(PROBE_LADDER_DOC)
    for token in ["Set A", "Set B", "Set C", "A -> B", "B -> C"]:
        assert token in text, f"Probe ladder doc missing token: {token}"
    for lane in ["CT-01", "SYM-01", "CAUS-01", "BR-01"]:
        assert lane in text, f"Probe ladder doc missing lane: {lane}"


def test_ucff_comparator_design_gate_doc_has_block_rule_and_front_door_requirements():
    text = _read(UCFF_GATE_DOC)
    required_tokens = [
        "No new comparator implementation is admissible",
        "Phase 1 dynamics-match closure",
        "Phase 3 Noether linkage",
        "Front-door API only",
        "fingerprinted empirical artifact",
        "deterministic metric vector",
    ]
    for token in required_tokens:
        assert token in text, f"UCFF comparator gate doc missing token: {token}"
