from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    current = start.resolve()
    while current != current.parent:
        if (current / "formal").exists() and (current / "README.md").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
TARGET_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_26_DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSURE_ATTEMPT_v0.md"
)
MICRO25_DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_25_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_ATTEMPT_v0.md"
)
LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"
GATE_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tests"
    / "test_em_u1_micro26_double_divergence_binding_theorem_closure_attempt.py"
)
OUTPUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "em_u1_micro26_double_divergence_binding_theorem_closure_attempt_execution_surface_v0.json"
)
OUTPUT_RELATIVE_PATH = "formal/output/em_u1_micro26_double_divergence_binding_theorem_closure_attempt_execution_surface_v0.json"

SPEC_ID = "DERIVATION_TARGET_EM_U1_MICRO_26_DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSURE_ATTEMPT_v0"
TARGET_ID = "TARGET-EM-U1-MICRO-26-DOUBLE-DIVERGENCE-BINDING-THEOREM-CLOSURE-ATTEMPT-v0"
ADJUDICATION = "EM_U1_MICRO26_DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSURE_ADJUDICATION: NOT_YET_DISCHARGED"
ASSUMPTION_IDS = [
    "ASM-EM-U1-PHY-SOURCE-01",
    "ASM-EM-U1-MATH-SMOOTH-01",
    "ASM-EM-U1-MATH-DISTRIB-01",
]
THEOREM_NAMES = [
    "em_u1_cycle026_dd_symmetry_from_commuting_partials_v0",
    "em_u1_cycle026_dd_antisymmetry_from_F_antisym_v0",
    "em_u1_cycle026_double_divergence_zero_for_field_strength_v0",
    "em_u1_cycle026_double_divergence_zero_for_potential_field_strength_v0",
]
STEP_TOKENS = [
    "DD_BINDING_STEP_v0: DEFINE_DD_FROM_FIELD_STRENGTH_OBJECT",
    "DD_BINDING_STEP_v0: PROVE_DD_SYMMETRY_FROM_COMMUTING_PARTIALS_SEAM",
    "DD_BINDING_STEP_v0: PROVE_DD_ANTISYMMETRY_FROM_FIELD_ANTISYMMETRY_SEAM",
    "DD_BINDING_STEP_v0: APPLY_CYCLE25_KERNEL_THEOREM_TO_BOUND_OBJECT",
    "DD_BINDING_TARGET_v0: DD_FROM_FIELD_STRENGTH_ZERO_UNDER_BOUND_ASSUMPTIONS",
]
PREREQUISITE_TOKENS = [
    "EM_U1_PROGRESS_CYCLE25_v0: DOUBLE_DIVERGENCE_THEOREM_CLOSURE_ATTEMPT_TOKEN_PINNED",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_ROUTE_v0: ANTISYM_COMMUTATION_THEOREM_SURFACE_PINNED",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_LOCALIZATION_GATE_v0: CYCLE25_ARTIFACTS_ONLY",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
    "EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED",
    "EM_U1_ANTISYM_SURFACE_v0: F_ANTISYM_STATEMENT_PINNED",
    "EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED",
    "EM_U1_MAXWELL_CONTINUITY_ROUTE_CLOSURE_ATTEMPT_v0: CANONICAL_ROUTE_CLOSURE_ATTEMPT_PINNED",
    "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
    "EM_U1_DISTRIBUTIONAL_SEMANTICS_MAPPING_ROUTE_v0: CLASSIFICATION_SURFACES_PINNED",
    "EM_U1_DISTRIBUTIONAL_REFERENCE_SURFACE_ROUTE_v0: REFERENCE_ONLY_SEMANTICS_PINNED",
]
KERNEL_THEOREM_NAME = "em_u1_cycle025_double_divergence_zero_of_antisymmetry_and_commuting_partials_v0"


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def _contains_all(text: str, tokens: list[str]) -> bool:
    return all(token in text for token in tokens)


def build_report() -> dict[str, object]:
    target_text = _read(TARGET_DOC_PATH)
    micro25_text = _read(MICRO25_DOC_PATH)
    lean_text = _read(LEAN_PATH)
    gate_text = _read(GATE_PATH)

    missing: list[str] = []

    if not _contains_all(target_text, STEP_TOKENS):
        missing.append("target_doc_step_tokens")
    if not _contains_all(target_text, PREREQUISITE_TOKENS):
        missing.append("target_doc_prerequisite_tokens")
    if not _contains_all(lean_text, THEOREM_NAMES):
        missing.append("lean_theorem_surfaces")
    if KERNEL_THEOREM_NAME not in lean_text:
        missing.append("cycle25_kernel_theorem_reference")
    if SPEC_ID not in gate_text or TARGET_ID not in gate_text:
        missing.append("gate_identity_tokens")
    if SPEC_ID not in target_text or TARGET_ID not in target_text:
        missing.append("target_identity_tokens")
    if ADJUDICATION not in target_text:
        missing.append("target_adjudication_token")
    if SPEC_ID not in micro25_text and "DERIVATION_TARGET_EM_U1_MICRO_25_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_ATTEMPT_v0" not in micro25_text:
        missing.append("cycle25_artifact_identity")

    status = "bounded_execution_surface_pinned" if not missing else "drift_detected"

    return {
        "report_id": "EM_U1_MICRO26_DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSURE_EXECUTION_SURFACE_v0",
        "spec_id": SPEC_ID,
        "target_id": TARGET_ID,
        "family": "EM_U1_MICRO26",
        "classification": "P-POLICY",
        "execution_surface_status": status,
        "adjudication": ADJUDICATION,
        "packet_01_scope_status": "frozen_out_of_scope",
        "verification_tranche_status": "complete_green",
        "bounded_scope": "cycle26_only_attempt_only",
        "inputs": {
            "target_doc": _relative(TARGET_DOC_PATH),
            "direct_prerequisite_doc": _relative(MICRO25_DOC_PATH),
            "lean_module": _relative(LEAN_PATH),
            "gate": _relative(GATE_PATH),
            "generator": _relative(Path(__file__)),
            "output_report": OUTPUT_RELATIVE_PATH,
        },
        "assumption_ids": ASSUMPTION_IDS,
        "theorem_binding_steps": STEP_TOKENS,
        "theorem_names": THEOREM_NAMES,
        "direct_prerequisites": {
            "cycle25_kernel_artifact": _relative(MICRO25_DOC_PATH),
            "cycle25_kernel_theorem_name": KERNEL_THEOREM_NAME,
            "prerequisite_tokens": PREREQUISITE_TOKENS,
        },
        "checks": {
            "target_doc_contains_step_tokens": "target_doc_step_tokens" not in missing,
            "target_doc_contains_prerequisite_tokens": "target_doc_prerequisite_tokens" not in missing,
            "lean_contains_cycle26_theorem_names": "lean_theorem_surfaces" not in missing,
            "lean_references_cycle25_kernel_theorem": "cycle25_kernel_theorem_reference" not in missing,
            "gate_contains_micro26_identity_tokens": "gate_identity_tokens" not in missing,
            "target_doc_contains_identity_tokens": "target_identity_tokens" not in missing,
            "target_doc_contains_adjudication_token": "target_adjudication_token" not in missing,
            "cycle25_artifact_present": "cycle25_artifact_identity" not in missing,
        },
        "missing": missing,
    }


def main() -> None:
    report = build_report()
    OUTPUT_PATH.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()