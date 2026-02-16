from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
CONS_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "GR" / "ConservationContract.lean"
CONS_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md"
)
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
ALIGNMENT_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md"
)
CHECKLIST_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md"
)
NEWTONIAN_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
DER01_LEAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01DerivationScaffoldPromotion.lean"
)
REQUIRED_GR_CLOSURE_ROWS = ("TOE-GR-DER-01", "TOE-GR-DER-02", "TOE-GR-CONS-01")
DEFAULT_QUOTIENT_LOCK_POINTERS = (
    "formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hAction_provenance_v0.md",
    "formal/markdown/locks/functionals/FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md",
    "formal/markdown/locks/functionals/FN-DERIVE_default_quotient_bridge_discharge_object_v0.md",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _result_status_for(row_id: str, results_text: str) -> str:
    pattern = rf"^\| {re.escape(row_id)} \| `([^`]+)` \|"
    m = re.search(pattern, results_text, flags=re.MULTILINE)
    assert m is not None, f"Missing result row: {row_id}"
    return m.group(1)


def _roadmap_token_value(token: str, roadmap_text: str) -> str:
    pattern = rf"{re.escape(token)}:\s*([A-Za-z0-9_]+)"
    m = re.search(pattern, roadmap_text)
    assert m is not None, f"Missing roadmap token: {token}"
    return m.group(1)


def test_gr01_dual_layer_policy_tokens_are_present() -> None:
    text = _read(ROADMAP_PATH)
    required_tokens = [
        "## Dual-Layer Closure Semantics (v0)",
        "PILLAR-GR_PHYSICS_STATUS:",
        "PILLAR-GR_GOVERNANCE_STATUS:",
        "PROCEED_GATE_GR:",
        "MATRIX_CLOSURE_GATE_GR:",
        "REQUIRED_GR_CLOSURE_ROWS: TOE-GR-DER-01,TOE-GR-DER-02,TOE-GR-CONS-01",
        "TOE-GR-DER-02",
        "TOE-GR-CONS-01",
    ]
    for token in required_tokens:
        assert token in text, f"Missing dual-layer closure token in roadmap: {token}"


def test_gr01_required_blocker_rows_are_present_in_results_table() -> None:
    text = _read(RESULTS_PATH)
    for row_id in REQUIRED_GR_CLOSURE_ROWS:
        _ = _result_status_for(row_id, text)


def test_gr01_proceed_gate_requires_physics_closed() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_status = _roadmap_token_value("PILLAR-GR_PHYSICS_STATUS", roadmap_text)
    proceed_gate = _roadmap_token_value("PROCEED_GATE_GR", roadmap_text)
    if proceed_gate.startswith("ALLOWED_"):
        assert physics_status.startswith("CLOSED_"), (
            "Proceed gate is ALLOWED but PHYSICS status is not CLOSED."
        )


def test_gr01_matrix_closure_gate_requires_all_required_blockers_non_blocked() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)
    governance_status = _roadmap_token_value("PILLAR-GR_GOVERNANCE_STATUS", roadmap_text)
    matrix_gate = _roadmap_token_value("MATRIX_CLOSURE_GATE_GR", roadmap_text)
    blocked_required_rows = [
        row_id
        for row_id in REQUIRED_GR_CLOSURE_ROWS
        if _result_status_for(row_id, results_text).startswith("B-")
    ]

    if matrix_gate.startswith("ALLOWED_"):
        assert governance_status.startswith("CLOSED_"), (
            "Matrix closure gate is ALLOWED but GOVERNANCE status is not CLOSED."
        )
        assert not blocked_required_rows, (
            "Matrix closure gate is ALLOWED while required GR blockers remain B-*: "
            + ", ".join(blocked_required_rows)
        )


def test_gr01_conservation_contract_token_is_pinned_when_cons_row_mentions_it() -> None:
    results_text = _read(RESULTS_PATH)
    lean_text = _read(CONS_LEAN_PATH)

    if "gr01_conservation_compatibility_from_poisson_residual_v0" in results_text:
        assert (
            "theorem gr01_conservation_compatibility_from_poisson_residual_v0" in lean_text
        ), (
            "Results table mentions conservation compatibility theorem token, "
            "but Lean theorem declaration is missing."
        )


def test_gr01_cons01_promotion_requires_bridge_theorem_and_assumption_bindings() -> None:
    results_text = _read(RESULTS_PATH)
    cons_status = _result_status_for("TOE-GR-CONS-01", results_text)
    if not cons_status.startswith("B-"):
        lean_text = _read(CONS_LEAN_PATH)
        cons_doc = _read(CONS_DOC_PATH)
        assumption_registry = _read(ASSUMPTION_REGISTRY_PATH)
        required_lean_tokens = [
            "theorem gr01_conservation_compatibility_from_poisson_residual_v0",
            "theorem gr01_conservation_compatibility_from_bridge_promotion_chain_v0",
        ]
        missing = [token for token in required_lean_tokens if token not in lean_text]
        assert not missing, (
            "TOE-GR-CONS-01 is non-blocked, but required conservation theorem token(s) are missing: "
            + ", ".join(missing)
        )
        required_assumption_tokens = [
            "ASM-GR01-CONS-01",
            "ASM-GR01-CONS-02",
            "gr01_conservation_compatibility_from_bridge_promotion_chain_v0",
        ]
        for token in required_assumption_tokens:
            assert token in assumption_registry, (
                f"TOE-GR-CONS-01 is non-blocked, but conservation assumption binding token "
                f"'{token}' is missing from ASSUMPTION_REGISTRY_v1.md."
            )
        required_non_claim_lines = [
            "This artifact does not claim full GR conservation-law recovery.",
            "This artifact does not claim Noether-theorem completion.",
        ]
        for line in required_non_claim_lines:
            assert line in cons_doc, (
                "TOE-GR-CONS-01 is non-blocked, but required non-claim boundary line is missing: "
                + line
            )


def test_gr01_der01_promotion_requires_scaffold_bundle_token() -> None:
    results_text = _read(RESULTS_PATH)
    der01_status = _result_status_for("TOE-GR-DER-01", results_text)
    if not der01_status.startswith("B-"):
        der01_lean_text = _read(DER01_LEAN_PATH)
        assert (
            "theorem gr01_der01_scaffold_bundle_under_promoted_assumptions" in der01_lean_text
        ), (
            "TOE-GR-DER-01 is non-blocked, but DER-01 scaffold bundle theorem token "
            "is missing."
        )


def test_gr01_der02_promotion_requires_alignment_and_checklist_closure_tokens() -> None:
    results_text = _read(RESULTS_PATH)
    der02_status = _result_status_for("TOE-GR-DER-02", results_text)
    if not der02_status.startswith("B-"):
        alignment_text = _read(ALIGNMENT_PATH)
        checklist_text = _read(CHECKLIST_PATH)
        assert "ALIGNMENT_ADJUDICATION: DISCHARGED_CONDITIONAL_PUBLISH_v0" in alignment_text, (
            "TOE-GR-DER-02 is non-blocked, but alignment adjudication is not discharged."
        )
        assert "DER02_CHECKLIST_ADJUDICATION: DISCHARGED_CONDITIONAL_v0" in checklist_text, (
            "TOE-GR-DER-02 is non-blocked, but DER-02 checklist adjudication token is missing."
        )


def test_gr01_der02_promotion_requires_lock_pointer_sync_across_required_surfaces() -> None:
    results_text = _read(RESULTS_PATH)
    der02_status = _result_status_for("TOE-GR-DER-02", results_text)
    if not der02_status.startswith("B-"):
        surfaces = {
            "checklist": _read(CHECKLIST_PATH),
            "newtonian_target": _read(NEWTONIAN_TARGET_PATH),
            "roadmap": _read(ROADMAP_PATH),
            "state": _read(STATE_PATH),
        }
        for pointer in DEFAULT_QUOTIENT_LOCK_POINTERS:
            for name, text in surfaces.items():
                assert pointer in text, (
                    f"TOE-GR-DER-02 is non-blocked, but lock pointer '{pointer}' is "
                    f"missing from {name} surface."
                )
