from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
STATE_DOC = REPO_ROOT / "State_of_the_Theory.md"
TAXONOMY_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "CLAIM_TAXONOMY_v0.md"
TOE_CLAIM_SURFACE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CLAIM_SURFACE_v0.md"
STRUCTURAL_CLOSENESS_MAP_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "STRUCTURAL_CLOSENESS_MAP_v0.md"
ASSUMPTION_REGISTRY_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
QM_MEASUREMENT_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md"
)
QM_EVOLUTION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md"
)
QM_SYMMETRY_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md"
)
QFT_EVOLUTION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
)
QFT_GAUGE_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md"
)
GR_GEOMETRY_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md"
)
GR_CONSERVATION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md"
)
GR01_BRIDGE_PROMOTION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md"
)
GR01_REGIME_PROMOTION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md"
)
GR01_SCALING_PROMOTION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md"
)
GR01_SYMMETRY_PROMOTION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md"
)
GR01_END2END_CLOSURE_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md"
)
THEORY_SPEC_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "THEORY_SPEC_v1.md"
FIRST_DERIVATION_TARGET_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md"
)
TOE_GR01_THEOREM_SURFACE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_THEOREM_SURFACE_v0.md"
TOE_GR01_BRIDGE_SPEC_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md"
TOE_GR01_EXPANSION_NOTE_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md"
TOE_GR01_POTENTIAL_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md"
TOE_GR01_LAPLACIAN_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_LAPLACIAN_EXTRACTION_v0.md"
TOE_GR01_CALIBRATION_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_KAPPA_CALIBRATION_v0.md"
TOE_GR01_ANALYTIC_DISCHARGE_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ANALYTIC_DISCHARGE_v0.md"
)
TOE_GR01_THEOREM_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "WeakFieldPoissonLimit.lean"
)
QM_MEASUREMENT_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "MeasurementSemantics.lean"
)
QM_EVOLUTION_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "EvolutionContract.lean"
)
QM_SYMMETRY_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "SymmetryContract.lean"
)
QFT_EVOLUTION_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "EvolutionContract.lean"
)
QFT_GAUGE_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "GaugeContract.lean"
)
GR_GEOMETRY_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "GR" / "GeometryContract.lean"
)
GR_CONSERVATION_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "GR" / "ConservationContract.lean"
)
GR01_BRIDGE_PROMOTION_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01BridgePromotion.lean"
)
GR01_SCALING_PROMOTION_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01ScalingPromotion.lean"
)
GR01_SYMMETRY_PROMOTION_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01SymmetryPromotion.lean"
)
GR01_END2END_CLOSURE_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01EndToEndClosure.lean"
)
TOE_GR01_CALIBRATION_RECORD = REPO_ROOT / "formal" / "output" / "toe_gr01_kappa_calibration_v0.json"
TOE_GR01_CALIBRATION_LOCK = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "functionals" / "TOE-GR-01_kappa_calibration_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def _slice_lean_decl_body(text: str, decl_sig_end: int) -> str:
    """
    Return the declaration body slice from `decl_sig_end` to the next top-level
    declaration or namespace close token.
    """
    assert decl_sig_end >= 0
    tail = text[decl_sig_end:]
    boundary = re.search(
        r"(?m)^(theorem\s+|def\s+|structure\s+|class\s+|abbrev\s+|instance\s+|axiom\s+|end\s+QM\b|end\s+QFT\b|end\s+GR\b|end\s+ToeFormal\b)",
        tail,
    )
    if boundary is None:
        return tail
    return tail[: boundary.start()]


def test_paper_ready_gate_tokens_and_fn_derive_scope_are_present() -> None:
    text = _read(STATE_DOC)
    required_tokens = [
        "PAPER-READY-PHYSICS_v0",
        "Canonical claims inventory (paper-facing)",
        "FN-DERIVE scope statement (paper-facing):",
        "RAC is policy-level",
        "FN-DERIVE_default_quotient_hAction_provenance_v0.md",
        "FN-DERIVE_default_quotient_hRAC_obligation_bundle_v0.md",
        "FN-DERIVE_default_quotient_bridge_discharge_object_v0.md",
        "TOE-COMPLETE-TRACK_v0",
        "TOE_CLAIM_SURFACE_v0.md",
        "PHYSICS_PAPER_OUTLINE_v0.md",
        "STRUCTURAL_CLOSENESS_MAP_v0.md",
        "ASSUMPTION_REGISTRY_v1.md",
        "TOE-QM-THM-01",
        "DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md",
        "DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md",
        "DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md",
        "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
        "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md",
        "DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md",
        "DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md",
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md",
        "QM/MeasurementSemantics.lean",
        "QM/EvolutionContract.lean",
        "QM/SymmetryContract.lean",
        "QFT/EvolutionContract.lean",
        "QFT/GaugeContract.lean",
        "GR/GeometryContract.lean",
        "GR/ConservationContract.lean",
        "Variational/GR01BridgePromotion.lean",
        "Variational/GR01ScalingPromotion.lean",
        "Variational/GR01SymmetryPromotion.lean",
        "Variational/GR01EndToEndClosure.lean",
        "THEORY_SPEC_v1.md",
        "DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md",
        "TOE_GR01_THEOREM_SURFACE_v0.md",
        "TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md",
        "TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0.md",
        "TOE_GR01_POTENTIAL_IDENTIFICATION_v0.md",
        "TOE_GR01_LAPLACIAN_EXTRACTION_v0.md",
        "TOE_GR01_KAPPA_CALIBRATION_v0.md",
        "TOE_GR01_ANALYTIC_DISCHARGE_v0.md",
        "TOE_GR01_ACTION_RAC_STANCE_v0.md",
        "TOE_GR01_CONSERVATION_COMPATIBILITY_v0.md",
        "nabla_3D^2 Phi = kappa * rho",
        "DiscreteLaplacian3D",
        "PoissonEquation3D",
        "Separable3DMappingAssumptions",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "TARGET-GR01-BRIDGE-PROMO-PLAN",
        "TARGET-GR01-REG-PROMO-PLAN",
        "TARGET-GR01-SCALING-PROMO-PLAN",
        "TARGET-GR01-SYM-PROMO-PLAN",
        "TARGET-GR01-END2END-CLOSURE-PLAN",
        "toe_gr01_kappa_calibration_v0.json",
        "TOE-GR-01_kappa_calibration_v0.md",
        "WeakFieldPoissonLimit.lean",
        "ProjectionMapWellFormed",
        "WeakFieldTruncationSound",
        "ELImpliesDiscretePoissonResidual",
        "OperatorToDiscreteResidual",
        "No new comparator lanes are authorized until TOE-GR-01 reaches derivation-grade closure.",
    ]
    for token in required_tokens:
        assert token in text, f"Missing paper-ready/FN-DERIVE token: {token}"


def test_main_path_does_not_import_legacy_field2d_fn_lane() -> None:
    variational_root = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational"
    main_path_relpaths = [
        "ActionToFirstVariationBridgeRep32.lean",
        "ActionRep32CubicLane.lean",
        "ActionRep64CubicLane.lean",
        "FirstVariationDeclaredFrontDoor.lean",
        "FirstVariationDeclaredFieldRep.lean",
    ]
    forbidden = re.compile(
        r"(^|\n)\s*import\s+ToeFormal\.Variational\.(FirstVariationDeclared|DischargeELMatchesFN01Pcubic)\b",
        re.MULTILINE,
    )

    offenders: list[str] = []
    for rel in main_path_relpaths:
        path = variational_root / rel
        text = _read(path)
        if forbidden.search(text):
            offenders.append(path.as_posix())

    assert offenders == [], (
        "Main-path modules import legacy Field2D FN lane surfaces.\n"
        + "\n".join(offenders)
    )


def test_claim_taxonomy_doc_and_inventory_section_exist() -> None:
    taxonomy = _read(TAXONOMY_DOC)
    state = _read(STATE_DOC)
    claim_surface = _read(TOE_CLAIM_SURFACE_DOC)
    structural_map = _read(STRUCTURAL_CLOSENESS_MAP_DOC)
    assumption_registry = _read(ASSUMPTION_REGISTRY_DOC)
    qm_measurement_target = _read(QM_MEASUREMENT_TARGET_DOC)
    qm_evolution_target = _read(QM_EVOLUTION_TARGET_DOC)
    qm_symmetry_target = _read(QM_SYMMETRY_TARGET_DOC)
    qft_evolution_target = _read(QFT_EVOLUTION_TARGET_DOC)
    qft_gauge_target = _read(QFT_GAUGE_TARGET_DOC)
    gr_geometry_target = _read(GR_GEOMETRY_TARGET_DOC)
    gr_conservation_target = _read(GR_CONSERVATION_TARGET_DOC)
    gr01_bridge_promotion_target = _read(GR01_BRIDGE_PROMOTION_TARGET_DOC)
    gr01_regime_promotion_target = _read(GR01_REGIME_PROMOTION_TARGET_DOC)
    gr01_scaling_promotion_target = _read(GR01_SCALING_PROMOTION_TARGET_DOC)
    gr01_symmetry_promotion_target = _read(GR01_SYMMETRY_PROMOTION_TARGET_DOC)
    gr01_end2end_closure_target = _read(GR01_END2END_CLOSURE_TARGET_DOC)
    theory_spec = _read(THEORY_SPEC_DOC)
    target = _read(FIRST_DERIVATION_TARGET_DOC)
    theorem_surface = _read(TOE_GR01_THEOREM_SURFACE_DOC)
    bridge_spec = _read(TOE_GR01_BRIDGE_SPEC_DOC)
    expansion_note = _read(TOE_GR01_EXPANSION_NOTE_DOC)
    potential_note = _read(TOE_GR01_POTENTIAL_DOC)
    laplacian_note = _read(TOE_GR01_LAPLACIAN_DOC)
    calibration_note = _read(TOE_GR01_CALIBRATION_DOC)
    analytic_discharge_note = _read(TOE_GR01_ANALYTIC_DISCHARGE_DOC)
    theorem_lean = _read(TOE_GR01_THEOREM_LEAN)
    qm_measurement_lean = _read(QM_MEASUREMENT_LEAN)
    qm_evolution_lean = _read(QM_EVOLUTION_LEAN)
    qm_symmetry_lean = _read(QM_SYMMETRY_LEAN)
    qft_evolution_lean = _read(QFT_EVOLUTION_LEAN)
    qft_gauge_lean = _read(QFT_GAUGE_LEAN)
    gr_geometry_lean = _read(GR_GEOMETRY_LEAN)
    gr_conservation_lean = _read(GR_CONSERVATION_LEAN)
    gr01_bridge_promotion_lean = _read(GR01_BRIDGE_PROMOTION_LEAN)
    gr01_scaling_promotion_lean = _read(GR01_SCALING_PROMOTION_LEAN)
    gr01_symmetry_promotion_lean = _read(GR01_SYMMETRY_PROMOTION_LEAN)
    gr01_end2end_closure_lean = _read(GR01_END2END_CLOSURE_LEAN)
    calibration_record = json.loads(_read(TOE_GR01_CALIBRATION_RECORD))
    calibration_lock = _read(TOE_GR01_CALIBRATION_LOCK)

    for token in ["`T-PROVED`", "`T-CONDITIONAL`", "`E-REPRO`", "`P-POLICY`", "`B-BLOCKED`"]:
        assert token in taxonomy, f"Claim taxonomy missing label token: {token}"

    assert "Canonical claims inventory (paper-facing)" in state
    for token in [
        "TOE_CLAIM_SURFACE_v0",
        "theorem path (Lean)",
        "analytic derivation",
        "computational evidence",
        "STRUCTURAL_CLOSENESS_MAP_v0.md",
        "ASSUMPTION_REGISTRY_v1.md",
        "DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md",
        "DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md",
        "DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md",
        "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
        "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md",
        "DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md",
        "DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md",
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md",
        "GR01BridgePromotion.lean",
        "GR01ScalingPromotion.lean",
        "GR01SymmetryPromotion.lean",
        "GR01EndToEndClosure.lean",
        "TOE_GR01_ANALYTIC_DISCHARGE_v0.md",
        "TOE-QM-THM-01",
        "TARGET-GR01-BRIDGE-PROMO-PLAN",
        "TARGET-GR01-REG-PROMO-PLAN",
        "TARGET-GR01-SCALING-PROMO-PLAN",
        "TARGET-GR01-SYM-PROMO-PLAN",
        "TARGET-GR01-END2END-CLOSURE-PLAN",
    ]:
        assert token in claim_surface, f"Claim surface doc missing token: {token}"
    for token in [
        "STRUCTURAL_CLOSENESS_MAP_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "ABSENT",
        "PILLAR-CFT",
        "PILLAR-SR",
        "PILLAR-QM",
        "PILLAR-QFT",
        "PILLAR-GR",
        "PILLAR-STAT",
        "TOE-GR-01",
        "TOE-QM-01",
        "TOE-QM-THM-01",
        "TOE-SR-01",
        "TOE-TH-01",
        "TARGET-QM-MEAS-PLAN",
        "TARGET-QM-EVOL-PLAN",
        "TARGET-QM-SYMM-PLAN",
        "TARGET-QFT-EVOL-PLAN",
        "TARGET-QFT-GAUGE-PLAN",
        "TARGET-GR-GEOM-PLAN",
        "TARGET-GR-CONS-PLAN",
        "TARGET-GR01-BRIDGE-PROMO-PLAN",
        "TARGET-GR01-REG-PROMO-PLAN",
        "TARGET-GR01-SCALING-PROMO-PLAN",
        "TARGET-GR01-SYM-PROMO-PLAN",
        "DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md",
        "DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md",
        "DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md",
        "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
        "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md",
        "DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md",
        "DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md",
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md",
        "measurement/data anchoring (planning-pointer)",
        "evolution rule (planning-pointer)",
        "symmetry machinery (planning-pointer)",
        "conservation laws (planning-pointer)",
        "limit recoveries (planning-pointer)",
        "end-to-end closure criteria (planning-pointer)",
        "projection consistency (planning-pointer)",
        "3D weak-field mapping (embedding example)",
        "3D weak-field mapping (separable)",
        "3D weak-field mapping (mainstream-class gate)",
        "TOE-GR-3D-01",
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TOE-GR-CONS-01",
        "conservation compatibility (weak-field)",
        "TARGET-GR01-3D-03-PLAN",
        "DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md",
    ]:
        assert token in structural_map, f"Structural closeness map missing token: {token}"
    assert structural_map.count("`ABSENT`") >= 3, (
        "Structural closeness map must keep explicit ABSENT entries to prevent optimism drift."
    )
    for token in ["recovers gr", "derives standard model", "proof of everything"]:
        assert token not in structural_map.lower(), (
            "Structural closeness map must not contain direct promotion language."
        )
    map_rows = re.findall(r"^\|\s*`(PILLAR-[A-Z]+)`\s*\|\s*([^|]+?)\s*\|", structural_map, flags=re.MULTILINE)
    assert map_rows, "Structural closeness map must contain pillar rows."
    exact_counts: dict[tuple[str, str], int] = {}
    base_object_counts: dict[tuple[str, str], int] = {}
    base_object_has_pointer: dict[tuple[str, str], bool] = {}
    for pillar, raw_object in map_rows:
        object_label = " ".join(raw_object.strip().split())
        exact_key = (pillar, object_label.lower())
        exact_counts[exact_key] = exact_counts.get(exact_key, 0) + 1
        is_pointer = "(planning-pointer)" in object_label.lower()
        base_label = object_label.lower().replace(" (planning-pointer)", "")
        base_key = (pillar, base_label)
        base_object_counts[base_key] = base_object_counts.get(base_key, 0) + 1
        base_object_has_pointer[base_key] = base_object_has_pointer.get(base_key, False) or is_pointer
    duplicate_exact = sorted([k for k, c in exact_counts.items() if c > 1])
    assert duplicate_exact == [], (
        "Structural closeness map has exact duplicate (pillar, structural object) rows:\n"
        + "\n".join([f"{pillar} | {obj}" for pillar, obj in duplicate_exact])
    )
    invalid_base_dups = sorted([
        key for key, count in base_object_counts.items()
        if count > 1 and not base_object_has_pointer.get(key, False)
    ])
    assert invalid_base_dups == [], (
        "Structural closeness map duplicates a pillar/object without planning-pointer marker:\n"
        + "\n".join([f"{pillar} | {obj}" for pillar, obj in invalid_base_dups])
    )
    assert (
        "| `PILLAR-QM` | evolution rule | `T-CONDITIONAL` | `TOE-QM-THM-01` |"
        in structural_map
    ), "Structural closeness map must pin the promoted QM evolution theorem status."
    for token in [
        "ASSUMPTION_REGISTRY_v1",
        "Classification:",
        "`P-POLICY`",
        "Taxonomy Classes",
        "`STRUCTURAL`",
        "`REGIME`",
        "`APPROXIMATION`",
        "`SYMMETRY`",
        "`BOUNDARY`",
        "`NORMALIZATION`",
        "`CALIBRATION`",
        "ASM-QM-EVOL-STR-01",
        "ASM-QM-EVOL-STR-02",
        "ASM-QM-EVOL-APP-01",
        "ASM-GR01-REG-01",
        "ASM-GR01-REG-02",
        "ASM-GR01-APP-01",
        "ASM-GR01-APP-02",
        "ASM-GR01-APP-03",
        "ASM-GR01-APP-04",
        "gr01_first_order_truncation_sound",
        "ASM-GR01-SYM-01",
        "gr01_projection_map_well_formed",
        "gr01_end_to_end_chain_bundle_under_promoted_assumptions",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
        "GR01 Promotion Intent",
        "intended theorem-level",
        "intended policy-level permanent",
        "support-only permanent",
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md",
    ]:
        assert token in assumption_registry, f"Assumption registry missing token: {token}"
    asm_gr01_app02_rows = re.findall(
        r"^\|\s*`ASM-GR01-APP-02`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert len(asm_gr01_app02_rows) == 1, (
        "Assumption registry must have exactly one canonical row for ASM-GR01-APP-02."
    )
    asm_gr01_app02_status_match = re.search(
        r"^\|\s*`ASM-GR01-APP-02`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert asm_gr01_app02_status_match is not None, (
        "Assumption registry must include a canonical status row for ASM-GR01-APP-02."
    )
    asm_gr01_app02_status = asm_gr01_app02_status_match.group(1)
    assert asm_gr01_app02_status in {"P-POLICY", "T-CONDITIONAL"}, (
        "ASM-GR01-APP-02 status must be either P-POLICY or T-CONDITIONAL."
    )
    if asm_gr01_app02_status == "T-CONDITIONAL":
        for token in [
            "theorem gr01_discrete_residual_from_bridge_promotion_chain",
            "def ELImpliesOperatorResidualUnderBound",
        ]:
            assert token in gr01_bridge_promotion_lean, (
                "ASM-GR01-APP-02 cannot be promoted to T-CONDITIONAL without "
                "bridge-promotion theorem tokens."
            )
    asm_gr01_reg01_rows = re.findall(
        r"^\|\s*`ASM-GR01-REG-01`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert len(asm_gr01_reg01_rows) == 1, (
        "Assumption registry must have exactly one canonical row for ASM-GR01-REG-01."
    )
    asm_gr01_reg01_status_match = re.search(
        r"^\|\s*`ASM-GR01-REG-01`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert asm_gr01_reg01_status_match is not None, (
        "Assumption registry must include a canonical status row for ASM-GR01-REG-01."
    )
    asm_gr01_reg01_status = asm_gr01_reg01_status_match.group(1)
    assert asm_gr01_reg01_status in {"P-POLICY", "T-CONDITIONAL"}, (
        "ASM-GR01-REG-01 status must be either P-POLICY or T-CONDITIONAL."
    )
    if asm_gr01_reg01_status == "T-CONDITIONAL":
        for token in [
            "def WeakFieldRegimePredicate",
            "theorem gr01_regime_predicate_under_uniform_bound",
        ]:
            assert token in gr01_bridge_promotion_lean, (
                "ASM-GR01-REG-01 cannot be promoted to T-CONDITIONAL without "
                "regime-promotion theorem tokens."
            )
    asm_gr01_app01_rows = re.findall(
        r"^\|\s*`ASM-GR01-APP-01`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert len(asm_gr01_app01_rows) == 1, (
        "Assumption registry must have exactly one canonical row for ASM-GR01-APP-01."
    )
    asm_gr01_app01_status_match = re.search(
        r"^\|\s*`ASM-GR01-APP-01`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert asm_gr01_app01_status_match is not None, (
        "Assumption registry must include a canonical status row for ASM-GR01-APP-01."
    )
    asm_gr01_app01_status = asm_gr01_app01_status_match.group(1)
    assert asm_gr01_app01_status in {"P-POLICY", "T-CONDITIONAL"}, (
        "ASM-GR01-APP-01 status must be either P-POLICY or T-CONDITIONAL."
    )
    if asm_gr01_app01_status == "T-CONDITIONAL":
        for token in [
            "def WeakFieldScalingHierarchy",
            "def HigherOrderTermsNegligible",
            "theorem gr01_first_order_truncation_sound",
        ]:
            assert token in gr01_scaling_promotion_lean, (
                "ASM-GR01-APP-01 cannot be promoted to T-CONDITIONAL without "
                "scaling-promotion theorem tokens."
            )
    asm_gr01_sym01_rows = re.findall(
        r"^\|\s*`ASM-GR01-SYM-01`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert len(asm_gr01_sym01_rows) == 1, (
        "Assumption registry must have exactly one canonical row for ASM-GR01-SYM-01."
    )
    asm_gr01_sym01_status_match = re.search(
        r"^\|\s*`ASM-GR01-SYM-01`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        assumption_registry,
        flags=re.MULTILINE,
    )
    assert asm_gr01_sym01_status_match is not None, (
        "Assumption registry must include a canonical status row for ASM-GR01-SYM-01."
    )
    asm_gr01_sym01_status = asm_gr01_sym01_status_match.group(1)
    assert asm_gr01_sym01_status in {"P-POLICY", "T-CONDITIONAL"}, (
        "ASM-GR01-SYM-01 status must be either P-POLICY or T-CONDITIONAL."
    )
    if asm_gr01_sym01_status == "T-CONDITIONAL":
        for token in [
            "def ProjectionMapWellFormedPredicate",
            "theorem gr01_projection_map_well_formed_under_regime_predicate",
            "theorem gr01_projection_map_well_formed",
        ]:
            assert token in gr01_symmetry_promotion_lean, (
                "ASM-GR01-SYM-01 cannot be promoted to T-CONDITIONAL without "
                "symmetry-promotion theorem tokens."
            )
    for token in [
        "TOE_GR01_ANALYTIC_DISCHARGE_v0",
        "Classification:",
        "`B-BLOCKED`",
        "Assumption Freeze (with IDs)",
        "Approximation Regime Statement",
        "Scaling Hierarchy",
        "Analytic Derivation Chain (Narrative)",
        "ELImpliesDiscretePoissonResidual",
        "ASM-GR01-APP-02",
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0",
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0",
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0",
        "ASM-GR01-SYM-01",
        "TARGET-GR01-END2END-CLOSURE-PLAN",
        "GR01EndToEndClosureBundle",
        "gr01_end_to_end_chain_bundle_under_promoted_assumptions",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
    ]:
        assert token in analytic_discharge_note, (
            f"GR01 analytic discharge note missing token: {token}"
        )
    for token in [
        "DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "does not authorize new comparator lanes",
        "Minimum Structural Objects Required",
        "Probability map object",
        "Measurement semantics object",
        "Classification bridge surface",
        "Theorem-Surface Contract",
        "Closure Definition",
        "ABSENT -> P-POLICY",
        "P-POLICY -> T-CONDITIONAL",
        "No new comparator lanes are authorized",
        "TARGET-QM-MEAS-PLAN",
        "h_context_consistency",
        "boundary-condition assumption",
        "zero-extension boundary lemmas",
        "Expectation",
        "ExpectedObservable",
        "weights_eq_zero_extension_of_context_consistency",
        "expectation_eq_of_context_consistency_with_zero_extension",
        "expectation_add",
        "expectation_smul",
        "expectation_nonneg_of_nonneg_weights_and_observable",
        "expected_observable_nonneg_of_support_nonneg",
        "nonneg_support",
    ]:
        assert token in qm_measurement_target, f"QM measurement target doc missing token: {token}"
    for token in [
        "formal/toe_formal/ToeFormal/QM/MeasurementSemantics.lean",
        "qm_measurement_weights_normalized_under_assumptions",
        "not a Born-rule claim",
    ]:
        assert token in qm_measurement_target, f"QM measurement target doc missing theorem contract token: {token}"
    for token in [
        "DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "does not authorize new comparator lanes",
        "does not claim Schrodinger-equation derivation",
        "does not claim unitary dynamics recovery",
        "Minimum Structural Objects Required",
        "Time parameter object",
        "QM-state object",
        "Evolution operator object",
        "Evolution context object",
        "Evolution contract surface",
        "Theorem-Surface Contract",
        "Closure Definition",
        "ABSENT -> P-POLICY",
        "P-POLICY -> T-CONDITIONAL",
        "No new comparator lanes are authorized",
        "TARGET-QM-EVOL-PLAN",
        "TOE-QM-THM-01",
        "Assumption Classification (Promotion Draft)",
        "ASSUMPTION_REGISTRY_v1.md",
        "ASM-QM-EVOL-STR-01",
        "ASM-QM-EVOL-STR-02",
        "ASM-QM-EVOL-APP-01",
        "qm_evolution_under_contract_assumptions",
        "QMStateEvolvesUnderContract",
    ]:
        assert token in qm_evolution_target, f"QM evolution target doc missing token: {token}"
    for token in [
        "formal/toe_formal/ToeFormal/QM/EvolutionContract.lean",
        "qm_evolution_under_contract_assumptions",
        "No Schrodinger derivation claim",
    ]:
        assert token in qm_evolution_target, f"QM evolution target doc missing theorem contract token: {token}"
    for token in [
        "DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "does not authorize new comparator lanes",
        "does not claim Schrodinger-equation recovery",
        "Minimum Structural Objects Required",
        "Symmetry group object",
        "Symmetry action object",
        "Symmetry context object",
        "QM-state object",
        "Invariance contract surface",
        "Theorem-Surface Contract",
        "Closure Definition",
        "ABSENT -> P-POLICY",
        "P-POLICY -> T-CONDITIONAL",
        "No new comparator lanes are authorized",
        "TARGET-QM-SYMM-PLAN",
        "qm_state_fixed_under_symmetry_contract_assumptions",
        "StateFixedUnderSymmetryAction",
    ]:
        assert token in qm_symmetry_target, f"QM symmetry target doc missing token: {token}"
    for token in [
        "formal/toe_formal/ToeFormal/QM/SymmetryContract.lean",
        "qm_state_fixed_under_symmetry_contract_assumptions",
        "No QM interpretation claim",
    ]:
        assert token in qm_symmetry_target, f"QM symmetry target doc missing theorem contract token: {token}"
    for token in [
        "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "does not authorize new comparator lanes",
        "does not claim Schrodinger/Dirac/Klein-Gordon derivation",
        "does not claim Standard Model dynamics recovery",
        "Minimum Structural Objects Required",
        "Time parameter object",
        "Field-state object",
        "Evolution operator object",
        "Evolution context object",
        "Evolution contract surface",
        "Theorem-Surface Contract",
        "Closure Definition",
        "ABSENT -> P-POLICY",
        "P-POLICY -> T-CONDITIONAL",
        "No new comparator lanes are authorized",
        "TARGET-QFT-EVOL-PLAN",
        "qft_evolution_under_contract_assumptions",
        "EvolvesUnderContract",
    ]:
        assert token in qft_evolution_target, f"QFT evolution target doc missing token: {token}"
    for token in [
        "formal/toe_formal/ToeFormal/QFT/EvolutionContract.lean",
        "qft_evolution_under_contract_assumptions",
        "No Standard Model claim",
    ]:
        assert token in qft_evolution_target, f"QFT evolution target doc missing theorem contract token: {token}"
    for token in [
        "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "does not authorize new comparator lanes",
        "does not claim Standard Model recovery",
        "Minimum Structural Objects Required",
        "Gauge group object",
        "Gauge action object",
        "Gauge context object",
        "Gauge field object",
        "Invariance contract surface",
        "Theorem-Surface Contract",
        "Closure Definition",
        "ABSENT -> P-POLICY",
        "P-POLICY -> T-CONDITIONAL",
        "No new comparator lanes are authorized",
        "TARGET-QFT-GAUGE-PLAN",
        "qft_gauge_invariance_under_contract_assumptions",
        "FieldFixedUnderGaugeAction",
    ]:
        assert token in qft_gauge_target, f"QFT gauge target doc missing token: {token}"
    for token in [
        "formal/toe_formal/ToeFormal/QFT/GaugeContract.lean",
        "qft_gauge_invariance_under_contract_assumptions",
        "No Standard Model claim",
    ]:
        assert token in qft_gauge_target, f"QFT gauge target doc missing theorem contract token: {token}"
    assert "GaugeInvarianceUnderAction" not in state, (
        "State surface must not retain legacy QFT predicate token GaugeInvarianceUnderAction."
    )
    assert "GaugeInvarianceUnderAction" not in qft_gauge_target, (
        "QFT gauge target doc must not retain legacy predicate token GaugeInvarianceUnderAction."
    )
    assert "GaugeInvarianceUnderAction" not in qft_gauge_lean, (
        "QFT gauge Lean surface must not retain legacy predicate token GaugeInvarianceUnderAction."
    )
    for token in [
        "DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "does not authorize new comparator lanes",
        "does not claim GR field-equation recovery",
        "Minimum Structural Objects Required",
        "Spacetime chart object",
        "Diffeomorphism action object",
        "Metric object",
        "Invariance contract surface",
        "Theorem-Surface Contract",
        "Closure Definition",
        "ABSENT -> P-POLICY",
        "P-POLICY -> T-CONDITIONAL",
        "No new comparator lanes are authorized",
        "TARGET-GR-GEOM-PLAN",
        "gr_metric_invariance_under_contract_assumptions",
        "MetricInvarianceUnderAction",
    ]:
        assert token in gr_geometry_target, f"GR geometry target doc missing token: {token}"
    for token in [
        "formal/toe_formal/ToeFormal/GR/GeometryContract.lean",
        "gr_metric_invariance_under_contract_assumptions",
        "No GR field-equation claim",
    ]:
        assert token in gr_geometry_target, f"GR geometry target doc missing theorem contract token: {token}"
    for token in [
        "DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote",
        "does not authorize new comparator lanes",
        "does not claim Einstein-equation recovery",
        "does not claim Noether theorem derivation",
        "Minimum Structural Objects Required",
        "Flow context object",
        "Divergence operator object",
        "Conserved quantity object",
        "Conservation contract surface",
        "Theorem-Surface Contract",
        "Closure Definition",
        "ABSENT -> P-POLICY",
        "P-POLICY -> T-CONDITIONAL",
        "No new comparator lanes are authorized",
        "TARGET-GR-CONS-PLAN",
        "gr_conservation_under_contract_assumptions",
        "ConservationLawUnderFlow",
    ]:
        assert token in gr_conservation_target, f"GR conservation target doc missing token: {token}"
    for token in [
        "formal/toe_formal/ToeFormal/GR/ConservationContract.lean",
        "gr_conservation_under_contract_assumptions",
        "No GR field-equation claim",
    ]:
        assert token in gr_conservation_target, f"GR conservation target doc missing theorem contract token: {token}"
    for token in [
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
            "non-claim",
            "does not authorize new comparator lanes",
            "ASM-GR01-APP-02",
            "ELImpliesDiscretePoissonResidual",
            "GR01BridgePromotion.lean",
            "WeakFieldUniformBound",
            "FirstOrderRemainderSuppressed",
            "ELImpliesOperatorResidualUnderBound",
            "gr01_discrete_residual_from_bridge_promotion_chain",
            "ASM-GR01-REG-02",
            "ASM-GR01-APP-03",
            "ASM-GR01-APP-04",
            "Promotion Strategy Options",
            "Preferred route: discharged lemma chain",
        "Fallback route: sharply delimited postulate freeze",
        "Acceptable Assumption Strengthening (allowed in this target)",
        "Forbidden shortcut",
        "No new comparator lanes are authorized",
        "TARGET-GR01-BRIDGE-PROMO-PLAN",
    ]:
        assert token in gr01_bridge_promotion_target, (
            f"GR01 bridge-promotion target doc missing token: {token}"
        )
    for token in [
        "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not authorize new comparator lanes",
        "ASM-GR01-REG-01",
        "GR01BridgePromotion.lean",
        "WeakFieldRegimePredicate",
        "gr01_regime_predicate_under_uniform_bound",
        "Promotion checkpoint (`P-POLICY -> T-CONDITIONAL`)",
        "TARGET-GR01-REG-PROMO-PLAN",
    ]:
        assert token in gr01_regime_promotion_target, (
            f"GR01 regime-promotion target doc missing token: {token}"
        )
    for token in [
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not authorize new comparator lanes",
        "ASM-GR01-APP-01",
        "GR01ScalingPromotion.lean",
        "WeakFieldScalingHierarchy",
        "HigherOrderTermsNegligible",
        "gr01_scaling_hierarchy_under_regime_predicate",
        "gr01_first_order_truncation_sound",
        "Promotion checkpoint (`P-POLICY -> T-CONDITIONAL`)",
        "TARGET-GR01-SCALING-PROMO-PLAN",
    ]:
        assert token in gr01_scaling_promotion_target, (
            f"GR01 scaling-promotion target doc missing token: {token}"
        )
    for token in [
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not authorize new comparator lanes",
        "ASM-GR01-SYM-01",
        "GR01SymmetryPromotion.lean",
        "ProjectionMapWellFormedPredicate",
        "gr01_projection_map_well_formed_under_regime_predicate",
        "gr01_projection_map_well_formed",
        "Promotion checkpoint (`P-POLICY -> T-CONDITIONAL`)",
        "TARGET-GR01-SYM-PROMO-PLAN",
    ]:
        assert token in gr01_symmetry_promotion_target, (
            f"GR01 symmetry-promotion target doc missing token: {token}"
        )
    for token in [
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0",
        "Classification:",
        "`P-POLICY`",
        "planning-only",
        "non-claim",
        "does not promote claim labels by itself",
        "no comparator-lane authorization",
        "TARGET-GR01-END2END-CLOSURE-PLAN",
        "GR01EndToEndClosure.lean",
        "GR01EndToEndClosureBundle",
        "gr01_end_to_end_chain_bundle_under_promoted_assumptions",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
        "Closure criteria (tokenized)",
        "ProjectionMapWellFormed",
        "WeakFieldRegimePredicate",
        "WeakFieldScalingHierarchy",
        "DiscretePoissonResidual1D",
    ]:
        assert token in gr01_end2end_closure_target, (
            f"GR01 end-to-end closure target doc missing token: {token}"
        )
    for token in ["THEORY_SPEC_v1", "Fundamental Degrees of Freedom", "Action / Variational Object", "Units and Dimensional Analysis Posture"]:
        assert token in theory_spec, f"Theory spec doc missing token: {token}"
    for token in [
        "DERIVATION_TARGET_NEWTONIAN_LIMIT_v0",
        "TOE-GR-01",
        "nabla^2 Phi = kappa * rho",
        "ASSUMPTION_REGISTRY_v1.md",
        "TOE_GR01_ANALYTIC_DISCHARGE_v0.md",
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md",
        "TARGET-GR01-END2END-CLOSURE-PLAN",
        "GR01EndToEndClosure.lean",
        "gr01_end_to_end_chain_bundle_under_promoted_assumptions",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
        "TOE_GR01_PROJECTION_BRIDGE_SPEC_v0.md",
        "No new comparator lanes are authorized until `TOE-GR-01` reaches derivation-grade closure.",
    ]:
        assert token in target, f"Derivation target doc missing token: {token}"
    for token in [
        "TOE_GR01_THEOREM_SURFACE_v0",
        "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions",
        "nabla_3D^2 Phi = kappa * rho",
        "DiscreteLaplacian3D",
        "PoissonEquation3D",
        "Separable3DMappingAssumptions",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "Lift1DTo3DMappingAssumptions",
        "poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
        "TOE_GR01_ACTION_RAC_STANCE_v0.md",
        "GR01EndToEndClosure.lean",
        "gr01_end_to_end_chain_bundle_under_promoted_assumptions",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
    ]:
        assert token in theorem_surface, f"Theorem-surface doc missing token: {token}"
    for token in [
        "TOE_GR01_PROJECTION_BRIDGE_SPEC_v0",
        "ProjectionMapWellFormed",
        "WeakFieldTruncationSound",
        "ELImpliesDiscretePoissonResidual",
        "OperatorToDiscreteResidual",
        "mkWeakFieldProjectionFromCore",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md",
        "GR01EndToEndClosure.lean",
    ]:
        assert token in bridge_spec, f"Projection-bridge spec missing token: {token}"
    assert "OperatorToDiscreteResidual" in bridge_spec and "`T-CONDITIONAL`" in bridge_spec, (
        "Projection bridge spec must classify OperatorToDiscreteResidual as non-policy transport target."
    )
    assert "ELImpliesDiscretePoissonResidual" in bridge_spec, (
        "Projection bridge spec must include ELImpliesDiscretePoissonResidual bridge term."
    )
    if asm_gr01_app02_status == "T-CONDITIONAL":
        assert "`T-CONDITIONAL`" in bridge_spec, (
            "Projection bridge spec must classify ELImpliesDiscretePoissonResidual as "
            "T-CONDITIONAL after ASM-GR01-APP-02 promotion."
        )
        assert "policy-scoped" not in bridge_spec.lower(), (
            "Projection bridge spec cannot describe ELImpliesDiscretePoissonResidual as "
            "policy-scoped after promotion."
        )
    else:
        assert "`P-POLICY`" in bridge_spec, (
            "Projection bridge spec must classify ELImpliesDiscretePoissonResidual as "
            "P-POLICY before promotion."
        )
    if asm_gr01_sym01_status == "T-CONDITIONAL":
        assert "ProjectionMapWellFormed" in bridge_spec and "`T-CONDITIONAL`" in bridge_spec, (
            "Projection bridge spec must classify ProjectionMapWellFormed as "
            "T-CONDITIONAL after ASM-GR01-SYM-01 promotion."
        )
    else:
        assert "ProjectionMapWellFormed" in bridge_spec and "`P-POLICY`" in bridge_spec, (
            "Projection bridge spec must classify ProjectionMapWellFormed as "
            "P-POLICY before promotion."
        )
    for token in ["TOE_GR01_WEAK_FIELD_EXPANSION_NOTE_v0", "weak-field"]:
        assert token in expansion_note, f"Expansion note missing token: {token}"
    for token in ["TOE_GR01_POTENTIAL_IDENTIFICATION_v0", "scalar potential"]:
        assert token in potential_note, f"Potential note missing token: {token}"
    for token in ["TOE_GR01_LAPLACIAN_EXTRACTION_v0", "nabla^2 Phi = kappa * rho"]:
        assert token in laplacian_note, f"Laplacian note missing token: {token}"
    for token in ["nabla_3D^2 Phi = kappa * rho", "DiscreteLaplacian3D", "PoissonEquation3D"]:
        assert token in laplacian_note, f"Laplacian note missing 3D posture token: {token}"
    for token in [
        "Separable3DMappingAssumptions",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "Lift1DTo3DMappingAssumptions",
        "poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
    ]:
        assert token in laplacian_note, f"Laplacian note missing 3D mapping token: {token}"
    for token in ["## Units Dictionary (Scoped)", "## Falsifiability Hooks", "TOE_GR01_ACTION_RAC_STANCE_v0.md"]:
        assert token in analytic_discharge_note, (
            f"Analytic discharge note missing derivation-grade token: {token}"
        )
    for token in ["TOE_GR01_KAPPA_CALIBRATION_v0", "kappa = 4 * pi * G_N"]:
        assert token in calibration_note, f"Kappa calibration note missing token: {token}"
    for token in [
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions",
        "def DiscreteLaplacian1D",
        "def DiscretePoissonResidual1D",
        "def DiscreteLaplacian3D",
        "def DiscretePoissonResidual3D",
        "def PoissonEquation3D",
        "def WeakFieldPoissonLimitStatement3D",
        "structure Lift1DTo3DMappingAssumptions",
        "structure Separable3DMappingAssumptions",
        "theorem discreteLaplacian3D_of_lift_x_only",
        "theorem discretePoissonResidual3D_of_lift_x_only",
        "theorem poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
        "theorem weakFieldPoissonLimitStatement3D_of_weakFieldPoissonLimitStatement_under_lift_x_only",
        "theorem discreteLaplacian3D_of_separable",
        "theorem discretePoissonResidual3D_of_separable",
        "theorem poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "theorem weakFieldPoissonLimitStatement3D_of_componentwise_poissonEquation1D_under_separable",
        "WeakFieldPoissonLimitStatement",
        "WeakFieldProjectionFromCore",
        "discrete_residual_zero_from_core",
        "ProjectionMapWellFormed",
        "WeakFieldTruncationSound",
        "ELImpliesDiscretePoissonResidual",
        "theorem OperatorToDiscreteResidual",
        "def mkWeakFieldProjectionFromCore",
        "theorem weakFieldResidualFromProjection",
        "theorem weakFieldPoissonResidualOfProjection",
        "WeakFieldAnsatz",
        "LaplacianExtraction",
        "UnitsAndCalibration",
    ]:
        assert token in theorem_lean, f"Lean theorem surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace QM",
        "Contract-only theorem surface.",
        "No Born-rule claim and no external truth claim.",
        "structure OutcomeSpace",
        "structure MeasurementContext",
        "structure ProbabilityMap",
        "def NormalizedWeights",
        "def Expectation",
        "def ExpectedObservable",
        "theorem weights_eq_zero_extension_of_context_consistency",
        "theorem expectation_eq_of_context_consistency_with_zero_extension",
        "theorem expectation_add",
        "theorem expectation_smul",
        "theorem expectation_nonneg_of_nonneg_weights_and_observable",
        "theorem expected_observable_nonneg_of_support_nonneg",
        "theorem qm_measurement_weights_normalized_under_assumptions",
    ]:
        assert token in qm_measurement_lean, f"QM measurement Lean surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace QM",
        "Contract-only theorem surface.",
        "No Schrodinger derivation claim and no external truth claim.",
        "No unitary dynamics recovery claim.",
        "structure TimeParameter",
        "structure EvolutionOperator",
        "structure EvolutionContext",
        "def QMStateEvolvesUnderContract",
        "theorem qm_evolution_under_contract_assumptions",
    ]:
        assert token in qm_evolution_lean, f"QM evolution Lean surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace QM",
        "Contract-only theorem surface.",
        "No QM interpretation claim and no external truth claim.",
        "structure SymmetryGroup",
        "structure SymmetryAction",
        "structure SymmetryContext",
        "structure QMState",
        "def StateFixedUnderSymmetryAction",
        "theorem qm_state_fixed_under_symmetry_contract_assumptions",
    ]:
        assert token in qm_symmetry_lean, f"QM symmetry Lean surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace QFT",
        "Contract-only theorem surface.",
        "No Standard Model claim and no external truth claim.",
        "No Schrodinger/Dirac/Klein-Gordon derivation claim.",
        "structure TimeParameter",
        "structure FieldState",
        "structure EvolutionOperator",
        "structure EvolutionContext",
        "def EvolvesUnderContract",
        "theorem qft_evolution_under_contract_assumptions",
    ]:
        assert token in qft_evolution_lean, f"QFT evolution Lean surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace QFT",
        "Contract-only theorem surface.",
        "No Standard Model claim and no external truth claim.",
        "structure GaugeGroup",
        "structure GaugeAction",
        "structure GaugeContext",
        "structure GaugeField",
        "def FieldFixedUnderGaugeAction",
        "theorem qft_gauge_invariance_under_contract_assumptions",
    ]:
        assert token in qft_gauge_lean, f"QFT gauge Lean surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace GR",
        "Contract-only theorem surface.",
        "No GR field-equation claim and no external truth claim.",
        "structure SpacetimeChart",
        "structure DiffeomorphismAction",
        "structure GeometryContext",
        "structure MetricField",
        "def MetricInvarianceUnderAction",
        "theorem gr_metric_invariance_under_contract_assumptions",
    ]:
        assert token in gr_geometry_lean, f"GR geometry Lean surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace GR",
        "Contract-only theorem surface.",
        "No GR field-equation claim and no external truth claim.",
        "No Noether theorem derivation claim.",
        "structure FlowContext",
        "structure DivergenceOperator",
        "structure ConservedQuantity",
        "def ConservationLawUnderFlow",
        "theorem gr_conservation_under_contract_assumptions",
    ]:
        assert token in gr_conservation_lean, f"GR conservation Lean surface missing token: {token}"
    for token in [
        "namespace ToeFormal",
        "namespace Variational",
        "Bridge-promotion theorem surface for GR01 blocker discharge work.",
        "No external truth claim.",
        "No Einstein-field-equation recovery claim.",
        "No comparator-lane expansion semantics.",
        "def WeakFieldUniformBound",
        "def FirstOrderRemainderSuppressed",
        "def ELImpliesOperatorResidualUnderBound",
        "theorem gr01_extraction_agrees_with_suppressed_remainder",
        "theorem gr01_operator_residual_from_bound_bridge_assumptions",
        "def WeakFieldRegimePredicate",
        "theorem gr01_regime_predicate_under_uniform_bound",
        "theorem gr01_discrete_residual_from_bridge_promotion_chain",
    ]:
        assert token in gr01_bridge_promotion_lean, (
            f"GR01 bridge-promotion Lean surface missing token: {token}"
        )
    for token in [
        "namespace ToeFormal",
        "namespace Variational",
        "Scaling-promotion theorem surface for GR01 approximation discharge work.",
        "No external truth claim.",
        "No Einstein-field-equation recovery claim.",
        "No comparator-lane expansion semantics.",
        "def WeakFieldScalingHierarchy",
        "def HigherOrderTermsNegligible",
        "theorem gr01_scaling_hierarchy_under_regime_predicate",
        "theorem gr01_first_order_truncation_sound",
    ]:
        assert token in gr01_scaling_promotion_lean, (
            f"GR01 scaling-promotion Lean surface missing token: {token}"
        )
    for token in [
        "namespace ToeFormal",
        "namespace Variational",
        "Symmetry-promotion theorem surface for GR01 projection-map discharge work.",
        "No external truth claim.",
        "No Einstein-field-equation recovery claim.",
        "No comparator-lane expansion semantics.",
        "structure ProjectionCarrierWitness",
        "def ProjectionMapWellFormedPredicate",
        "theorem gr01_projection_map_well_formed_under_regime_predicate",
        "theorem gr01_projection_map_well_formed",
    ]:
        assert token in gr01_symmetry_promotion_lean, (
            f"GR01 symmetry-promotion Lean surface missing token: {token}"
        )
    for token in [
        "namespace ToeFormal",
        "namespace Variational",
        "End-to-end chain-composition theorem surface for GR01 closure work.",
        "No external truth claim.",
        "No Einstein-field-equation recovery claim.",
        "No comparator-lane expansion semantics.",
        "def GR01EndToEndClosureBundle",
        "theorem gr01_end_to_end_chain_bundle_under_promoted_assumptions",
        "theorem gr01_end_to_end_poisson_equation_under_promoted_assumptions",
    ]:
        assert token in gr01_end2end_closure_lean, (
            f"GR01 end-to-end Lean surface missing token: {token}"
        )

    forbidden_tokens = [
        "def PoissonEquation1D (_Φ _ρ : ScalarField1D) (_κ : Real) : Prop :=\n  True",
        "def WeakFieldAnsatz : Prop := True",
        "def SmallPerturbationExpansion : Prop := True",
        "def PotentialIdentification : Prop := True",
        "def SourceIdentification : Prop := True",
        "def LaplacianExtraction : Prop := True",
        "def UnitsAndCalibration : Prop := True",
        "(hPoissonLimit : WeakFieldPoissonLimitStatement)",
        "exact hPoissonLimit",
        "ELImpliesProjectedResidual",
    ]
    for token in forbidden_tokens:
        assert token not in theorem_lean, f"Lean theorem surface still contains forbidden vacuous token: {token}"
    qm_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem qm_measurement_weights_normalized_under_assumptions :\n    ∃",
        "(hMeasurementPostulate : True)",
    ]
    for token in qm_forbidden_tokens:
        assert token not in qm_measurement_lean, f"QM measurement Lean surface contains forbidden vacuous token: {token}"
    qm_evolution_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem qm_evolution_under_contract_assumptions :\n    ∃",
        "(hEvolutionPostulate : True)",
        "derives schrodinger equation",
        "recovers unitary dynamics",
        "born rule derivation",
    ]
    qm_evolution_lean_lower = qm_evolution_lean.lower()
    for token in qm_evolution_forbidden_tokens:
        if token.islower():
            assert token not in qm_evolution_lean_lower, (
                f"QM evolution Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in qm_evolution_lean, (
                f"QM evolution Lean surface contains forbidden vacuous token: {token}"
            )
    qm_symmetry_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem qm_state_fixed_under_symmetry_contract_assumptions :\n    ∃",
        "(hSymmetryPostulate : True)",
        "schrodinger equation derivation",
        "born rule derivation",
    ]
    qm_symmetry_lean_lower = qm_symmetry_lean.lower()
    for token in qm_symmetry_forbidden_tokens:
        if token.islower():
            assert token not in qm_symmetry_lean_lower, (
                f"QM symmetry Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in qm_symmetry_lean, (
                f"QM symmetry Lean surface contains forbidden vacuous token: {token}"
            )
    qft_evolution_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem qft_evolution_under_contract_assumptions :\n    ∃",
        "(hEvolutionPostulate : True)",
        "schrodinger equation derivation",
        "dirac equation derivation",
        "klein-gordon recovery",
        "standard model dynamics",
    ]
    qft_evolution_lean_lower = qft_evolution_lean.lower()
    for token in qft_evolution_forbidden_tokens:
        if token.islower():
            assert token not in qft_evolution_lean_lower, (
                f"QFT evolution Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in qft_evolution_lean, (
                f"QFT evolution Lean surface contains forbidden vacuous token: {token}"
            )
    qft_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem qft_gauge_invariance_under_contract_assumptions :\n    ∃",
        "(hGaugePostulate : True)",
        "derives standard model",
        "su(3)×su(2)×u(1) recovery",
        "su(3)xsu(2)xu(1) recovery",
    ]
    qft_lean_lower = qft_gauge_lean.lower()
    for token in qft_forbidden_tokens:
        if token.islower():
            assert token not in qft_lean_lower, (
                f"QFT gauge Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in qft_gauge_lean, (
                f"QFT gauge Lean surface contains forbidden vacuous token: {token}"
            )
    gr_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem gr_metric_invariance_under_contract_assumptions :\n    ∃",
        "(hGeometryPostulate : True)",
        "einstein field equation",
        "g_{mu nu}",
    ]
    gr_lean_lower = gr_geometry_lean.lower()
    for token in gr_forbidden_tokens:
        if token.islower():
            assert token not in gr_lean_lower, (
                f"GR geometry Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in gr_geometry_lean, (
                f"GR geometry Lean surface contains forbidden vacuous token: {token}"
            )
    gr_conservation_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem gr_conservation_under_contract_assumptions :\n    ∃",
        "(hConservationPostulate : True)",
        "einstein field equation",
        "derives noether theorem",
    ]
    gr_conservation_lean_lower = gr_conservation_lean.lower()
    for token in gr_conservation_forbidden_tokens:
        if token.islower():
            assert token not in gr_conservation_lean_lower, (
                f"GR conservation Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in gr_conservation_lean, (
                f"GR conservation Lean surface contains forbidden vacuous token: {token}"
            )
    gr01_bridge_promotion_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem gr01_discrete_residual_from_bridge_promotion_chain :\n    ∃",
        "(hBridgePostulate : True)",
        "elimpliesprojectedresidual",
        "new comparator lane",
        "einstein field equation recovery",
    ]
    gr01_bridge_promotion_lean_lower = gr01_bridge_promotion_lean.lower()
    for token in gr01_bridge_promotion_forbidden_tokens:
        if token.islower():
            assert token not in gr01_bridge_promotion_lean_lower, (
                f"GR01 bridge-promotion Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in gr01_bridge_promotion_lean, (
                f"GR01 bridge-promotion Lean surface contains forbidden vacuous token: {token}"
            )
    gr01_scaling_promotion_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem gr01_first_order_truncation_sound :\n    ∃",
        "(hScalingPostulate : True)",
        "new comparator lane",
        "einstein field equation recovery",
    ]
    gr01_scaling_promotion_lean_lower = gr01_scaling_promotion_lean.lower()
    for token in gr01_scaling_promotion_forbidden_tokens:
        if token.islower():
            assert token not in gr01_scaling_promotion_lean_lower, (
                f"GR01 scaling-promotion Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in gr01_scaling_promotion_lean, (
                f"GR01 scaling-promotion Lean surface contains forbidden vacuous token: {token}"
            )
    gr01_symmetry_promotion_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem gr01_projection_map_well_formed :\n    ∃",
        "(hSymmetryPostulate : True)",
        "⟨trivial, trivial⟩",
        "new comparator lane",
        "einstein field equation recovery",
    ]
    gr01_symmetry_promotion_lean_lower = gr01_symmetry_promotion_lean.lower()
    for token in gr01_symmetry_promotion_forbidden_tokens:
        if token.islower():
            assert token not in gr01_symmetry_promotion_lean_lower, (
                f"GR01 symmetry-promotion Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in gr01_symmetry_promotion_lean, (
                f"GR01 symmetry-promotion Lean surface contains forbidden vacuous token: {token}"
            )
    gr01_end2end_closure_forbidden_tokens = [
        ": Prop :=\n  True",
        "theorem gr01_end_to_end_chain_bundle_under_promoted_assumptions :\n    ∃",
        "theorem gr01_end_to_end_poisson_equation_under_promoted_assumptions :\n    ∃",
        "(hClosurePostulate : True)",
        "new comparator lane",
        "einstein field equation recovery",
    ]
    gr01_end2end_closure_lean_lower = gr01_end2end_closure_lean.lower()
    for token in gr01_end2end_closure_forbidden_tokens:
        if token.islower():
            assert token not in gr01_end2end_closure_lean_lower, (
                f"GR01 end-to-end Lean surface contains forbidden drift token: {token}"
            )
        else:
            assert token not in gr01_end2end_closure_lean, (
                f"GR01 end-to-end Lean surface contains forbidden vacuous token: {token}"
            )
    assert qm_measurement_lean.count("structure OutcomeSpace") == 1
    assert qm_measurement_lean.count("structure MeasurementContext") == 1
    assert qm_measurement_lean.count("structure ProbabilityMap") == 1
    assert qm_measurement_lean.count("def NormalizedWeights") == 1
    assert qm_measurement_lean.count("def Expectation") == 1
    assert qm_measurement_lean.count("def ExpectedObservable") == 1
    assert qm_evolution_lean.count("structure TimeParameter") == 1
    assert qm_evolution_lean.count("structure EvolutionOperator") == 1
    assert qm_evolution_lean.count("structure EvolutionContext") == 1
    assert qm_evolution_lean.count("def QMStateEvolvesUnderContract") == 1
    assert qm_symmetry_lean.count("structure SymmetryGroup") == 1
    assert qm_symmetry_lean.count("structure SymmetryAction") == 1
    assert qm_symmetry_lean.count("structure SymmetryContext") == 1
    assert qm_symmetry_lean.count("structure QMState") == 1
    assert qm_symmetry_lean.count("def StateFixedUnderSymmetryAction") == 1
    assert qft_evolution_lean.count("structure TimeParameter") == 1
    assert qft_evolution_lean.count("structure FieldState") == 1
    assert qft_evolution_lean.count("structure EvolutionOperator") == 1
    assert qft_evolution_lean.count("structure EvolutionContext") == 1
    assert qft_evolution_lean.count("def EvolvesUnderContract") == 1
    assert qft_gauge_lean.count("structure GaugeGroup") == 1
    assert qft_gauge_lean.count("structure GaugeAction") == 1
    assert qft_gauge_lean.count("structure GaugeContext") == 1
    assert qft_gauge_lean.count("structure GaugeField") == 1
    assert qft_gauge_lean.count("def FieldFixedUnderGaugeAction") == 1
    assert gr_geometry_lean.count("structure SpacetimeChart") == 1
    assert gr_geometry_lean.count("structure DiffeomorphismAction") == 1
    assert gr_geometry_lean.count("structure GeometryContext") == 1
    assert gr_geometry_lean.count("structure MetricField") == 1
    assert gr_geometry_lean.count("def MetricInvarianceUnderAction") == 1
    assert gr_conservation_lean.count("structure FlowContext") == 1
    assert gr_conservation_lean.count("structure DivergenceOperator") == 1
    assert gr_conservation_lean.count("structure ConservedQuantity") == 1
    assert gr_conservation_lean.count("def ConservationLawUnderFlow") == 1
    assert gr01_bridge_promotion_lean.count("def WeakFieldUniformBound") == 1
    assert gr01_bridge_promotion_lean.count("def FirstOrderRemainderSuppressed") == 1
    assert gr01_bridge_promotion_lean.count("def ELImpliesOperatorResidualUnderBound") == 1
    assert gr01_bridge_promotion_lean.count("def WeakFieldRegimePredicate") == 1
    assert gr01_scaling_promotion_lean.count("def WeakFieldScalingHierarchy") == 1
    assert gr01_scaling_promotion_lean.count("def HigherOrderTermsNegligible") == 1
    assert gr01_scaling_promotion_lean.count(
        "theorem gr01_scaling_hierarchy_under_regime_predicate"
    ) == 1
    assert gr01_scaling_promotion_lean.count(
        "theorem gr01_first_order_truncation_sound"
    ) == 1
    assert gr01_symmetry_promotion_lean.count("structure ProjectionCarrierWitness") == 1
    assert gr01_symmetry_promotion_lean.count("def ProjectionMapWellFormedPredicate") == 1
    assert len(re.findall(
        r"(?m)^theorem\s+gr01_projection_map_well_formed_under_regime_predicate\b",
        gr01_symmetry_promotion_lean,
    )) == 1
    assert len(re.findall(
        r"(?m)^theorem\s+gr01_projection_map_well_formed\b",
        gr01_symmetry_promotion_lean,
    )) == 1
    assert gr01_end2end_closure_lean.count("def GR01EndToEndClosureBundle") == 1
    assert len(re.findall(
        r"(?m)^theorem\s+gr01_end_to_end_chain_bundle_under_promoted_assumptions\b",
        gr01_end2end_closure_lean,
    )) == 1
    assert len(re.findall(
        r"(?m)^theorem\s+gr01_end_to_end_poisson_equation_under_promoted_assumptions\b",
        gr01_end2end_closure_lean,
    )) == 1
    assert gr01_bridge_promotion_lean.count(
        "theorem gr01_extraction_agrees_with_suppressed_remainder"
    ) == 1
    assert gr01_bridge_promotion_lean.count(
        "theorem gr01_operator_residual_from_bound_bridge_assumptions"
    ) == 1
    assert gr01_bridge_promotion_lean.count(
        "theorem gr01_regime_predicate_under_uniform_bound"
    ) == 1
    assert gr01_bridge_promotion_lean.count(
        "theorem gr01_discrete_residual_from_bridge_promotion_chain"
    ) == 1
    probability_map_start = qm_measurement_lean.find("structure ProbabilityMap")
    normalized_weights_start = qm_measurement_lean.find("def NormalizedWeights", probability_map_start)
    assert probability_map_start >= 0 and normalized_weights_start > probability_map_start
    probability_map_block = qm_measurement_lean[probability_map_start:normalized_weights_start]
    assert "nonneg_support" in probability_map_block, (
        "ProbabilityMap must expose support-scoped nonnegativity field nonneg_support."
    )
    assert re.search(r"^\s*nonneg\s*:", probability_map_block, re.MULTILINE) is None, (
        "ProbabilityMap must not expose legacy global nonneg field."
    )
    expectation_start = qm_measurement_lean.find("def Expectation", normalized_weights_start)
    assert normalized_weights_start >= 0 and expectation_start > normalized_weights_start
    normalized_weights_block = qm_measurement_lean[normalized_weights_start:expectation_start]
    assert "(∀ o : Outcome, o ∈ outcomeSpace.support → 0 ≤ w o)" in normalized_weights_block, (
        "NormalizedWeights must enforce support-scoped nonnegativity."
    )
    assert "(∀ o : Outcome, 0 ≤ w o)" not in normalized_weights_block, (
        "NormalizedWeights must not use global nonnegativity in v0 contract."
    )
    qm_theorem_sig_start = qm_measurement_lean.find(
        "theorem qm_measurement_weights_normalized_under_assumptions"
    )
    assert qm_theorem_sig_start >= 0, "Missing QM measurement theorem signature."
    qm_theorem_sig_end = qm_measurement_lean.find(
        "NormalizedWeights ctx.outcomeSpace (probabilityMap.weights s) := by",
        qm_theorem_sig_start,
    )
    assert qm_theorem_sig_end > qm_theorem_sig_start, (
        "Could not isolate QM measurement theorem signature."
    )
    qm_theorem_sig = qm_measurement_lean[qm_theorem_sig_start:qm_theorem_sig_end]
    for token in [
        "(ctx : MeasurementContext State Outcome)",
        "(probabilityMap : ProbabilityMap State Outcome ctx)",
        "(h_context_consistency :",
        "(h_normalization :",
    ]:
        assert token in qm_theorem_sig, (
            f"QM measurement theorem signature missing explicit assumption token: {token}"
        )
    assert "(probabilityMap : ProbabilityMap State Outcome)" not in qm_theorem_sig, (
        "QM measurement theorem signature must not use legacy ProbabilityMap binder without context."
    )
    assert re.search(r"\(h_context_consistency\s*:\s*", qm_theorem_sig) is not None, (
        "QM measurement theorem signature must keep explicit h_context_consistency boundary assumption."
    )
    assert "(h_context_consistency : True)" not in qm_theorem_sig, (
        "QM measurement theorem signature must not weaken h_context_consistency to a vacuous assumption."
    )
    assert "∃ _" not in qm_theorem_sig and "True" not in qm_theorem_sig, (
        "QM measurement theorem signature must be non-vacuous."
    )
    qm_theorem_body_start = qm_theorem_sig_end
    qm_theorem_body = _slice_lean_decl_body(qm_measurement_lean, qm_theorem_body_start)
    assert qm_theorem_body.strip(), "Could not isolate QM measurement theorem body."
    assert (
        "expectation_eq_of_context_consistency_with_zero_extension" in qm_theorem_body
        or "weights_eq_zero_extension_of_context_consistency" in qm_theorem_body
    ), (
        "QM measurement theorem body must reference a zero-extension boundary lemma."
    )
    qm_lean_lower = qm_measurement_lean.lower()
    for token in [
        "probability = |psi|^2",
        "born rule derivation",
        "born-rule derivation",
    ]:
        assert token not in qm_lean_lower, (
            f"QM measurement Lean surface must not contain Born-rule claim token: {token}"
        )
    qm_evolution_theorem_sig_start = qm_evolution_lean.find(
        "theorem qm_evolution_under_contract_assumptions"
    )
    assert qm_evolution_theorem_sig_start >= 0, "Missing QM evolution theorem signature."
    qm_evolution_theorem_sig_end = qm_evolution_lean.find(
        "QMStateEvolvesUnderContract ctx t initialState finalState :=",
        qm_evolution_theorem_sig_start,
    )
    assert qm_evolution_theorem_sig_end > qm_evolution_theorem_sig_start, (
        "Could not isolate QM evolution theorem signature."
    )
    qm_evolution_theorem_sig = qm_evolution_lean[
        qm_evolution_theorem_sig_start:qm_evolution_theorem_sig_end
    ]
    for token in [
        "(ctx : EvolutionContext Time State)",
        "(t : Time)",
        "(initialState finalState : QMState State)",
        "(h_evolves_under_contract : QMStateEvolvesUnderContract ctx t initialState finalState)",
    ]:
        assert token in qm_evolution_theorem_sig, (
            f"QM evolution theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in qm_evolution_theorem_sig and "True" not in qm_evolution_theorem_sig, (
        "QM evolution theorem signature must be non-vacuous."
    )
    qm_symmetry_theorem_sig_start = qm_symmetry_lean.find(
        "theorem qm_state_fixed_under_symmetry_contract_assumptions"
    )
    assert qm_symmetry_theorem_sig_start >= 0, "Missing QM symmetry theorem signature."
    qm_symmetry_theorem_sig_end = qm_symmetry_lean.find(
        "StateFixedUnderSymmetryAction ctx state :=",
        qm_symmetry_theorem_sig_start,
    )
    assert qm_symmetry_theorem_sig_end > qm_symmetry_theorem_sig_start, (
        "Could not isolate QM symmetry theorem signature."
    )
    qm_symmetry_theorem_sig = qm_symmetry_lean[qm_symmetry_theorem_sig_start:qm_symmetry_theorem_sig_end]
    for token in [
        "(ctx : SymmetryContext SymElem State)",
        "(state : QMState State)",
        "(h_state_fixed_under_action : StateFixedUnderSymmetryAction ctx state)",
    ]:
        assert token in qm_symmetry_theorem_sig, (
            f"QM symmetry theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in qm_symmetry_theorem_sig and "True" not in qm_symmetry_theorem_sig, (
        "QM symmetry theorem signature must be non-vacuous."
    )
    qft_evolution_theorem_sig_start = qft_evolution_lean.find(
        "theorem qft_evolution_under_contract_assumptions"
    )
    assert qft_evolution_theorem_sig_start >= 0, "Missing QFT evolution theorem signature."
    qft_evolution_theorem_sig_end = qft_evolution_lean.find(
        "EvolvesUnderContract ctx initialState finalState :=",
        qft_evolution_theorem_sig_start,
    )
    assert qft_evolution_theorem_sig_end > qft_evolution_theorem_sig_start, (
        "Could not isolate QFT evolution theorem signature."
    )
    qft_evolution_theorem_sig = qft_evolution_lean[
        qft_evolution_theorem_sig_start:qft_evolution_theorem_sig_end
    ]
    for token in [
        "(ctx : EvolutionContext Time State)",
        "(initialState finalState : FieldState State)",
        "(h_evolves_under_contract : EvolvesUnderContract ctx initialState finalState)",
    ]:
        assert token in qft_evolution_theorem_sig, (
            f"QFT evolution theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in qft_evolution_theorem_sig and "True" not in qft_evolution_theorem_sig, (
        "QFT evolution theorem signature must be non-vacuous."
    )
    qft_theorem_sig_start = qft_gauge_lean.find(
        "theorem qft_gauge_invariance_under_contract_assumptions"
    )
    assert qft_theorem_sig_start >= 0, "Missing QFT gauge theorem signature."
    qft_theorem_sig_end = qft_gauge_lean.find(
        "FieldFixedUnderGaugeAction ctx field :=",
        qft_theorem_sig_start,
    )
    assert qft_theorem_sig_end > qft_theorem_sig_start, (
        "Could not isolate QFT gauge theorem signature."
    )
    qft_theorem_sig = qft_gauge_lean[qft_theorem_sig_start:qft_theorem_sig_end]
    for token in [
        "(ctx : GaugeContext GaugeElem FieldValue)",
        "(field : GaugeField FieldValue)",
        "(h_field_fixed_under_action : FieldFixedUnderGaugeAction ctx field)",
    ]:
        assert token in qft_theorem_sig, (
            f"QFT gauge theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in qft_theorem_sig and "True" not in qft_theorem_sig, (
        "QFT gauge theorem signature must be non-vacuous."
    )
    gr_theorem_sig_start = gr_geometry_lean.find(
        "theorem gr_metric_invariance_under_contract_assumptions"
    )
    assert gr_theorem_sig_start >= 0, "Missing GR geometry theorem signature."
    gr_theorem_sig_end = gr_geometry_lean.find(
        "MetricInvarianceUnderAction ctx metric :=",
        gr_theorem_sig_start,
    )
    assert gr_theorem_sig_end > gr_theorem_sig_start, (
        "Could not isolate GR geometry theorem signature."
    )
    gr_theorem_sig = gr_geometry_lean[gr_theorem_sig_start:gr_theorem_sig_end]
    for token in [
        "(ctx : GeometryContext Point)",
        "(metric : MetricField Point)",
        "(h_metric_invariant_under_action : MetricInvarianceUnderAction ctx metric)",
    ]:
        assert token in gr_theorem_sig, (
            f"GR geometry theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in gr_theorem_sig and "True" not in gr_theorem_sig, (
        "GR geometry theorem signature must be non-vacuous."
    )
    gr_conservation_theorem_sig_start = gr_conservation_lean.find(
        "theorem gr_conservation_under_contract_assumptions"
    )
    assert gr_conservation_theorem_sig_start >= 0, "Missing GR conservation theorem signature."
    gr_conservation_theorem_sig_end = gr_conservation_lean.find(
        "ConservationLawUnderFlow ctx divergenceOp quantity :=",
        gr_conservation_theorem_sig_start,
    )
    assert gr_conservation_theorem_sig_end > gr_conservation_theorem_sig_start, (
        "Could not isolate GR conservation theorem signature."
    )
    gr_conservation_theorem_sig = gr_conservation_lean[
        gr_conservation_theorem_sig_start:gr_conservation_theorem_sig_end
    ]
    for token in [
        "(ctx : FlowContext Point)",
        "(divergenceOp : DivergenceOperator Point)",
        "(quantity : ConservedQuantity Point)",
        "(h_conservation_under_flow : ConservationLawUnderFlow ctx divergenceOp quantity)",
    ]:
        assert token in gr_conservation_theorem_sig, (
            f"GR conservation theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in gr_conservation_theorem_sig and "True" not in gr_conservation_theorem_sig, (
        "GR conservation theorem signature must be non-vacuous."
    )
    gr01_bridge_theorem_sig_start = gr01_bridge_promotion_lean.find(
        "theorem gr01_discrete_residual_from_bridge_promotion_chain"
    )
    assert gr01_bridge_theorem_sig_start >= 0, "Missing GR01 bridge-promotion theorem signature."
    gr01_bridge_theorem_sig_end = gr01_bridge_promotion_lean.find(
        ":= by",
        gr01_bridge_theorem_sig_start,
    )
    assert gr01_bridge_theorem_sig_end > gr01_bridge_theorem_sig_start, (
        "Could not isolate GR01 bridge-promotion theorem signature."
    )
    gr01_bridge_theorem_sig = gr01_bridge_promotion_lean[
        gr01_bridge_theorem_sig_start:gr01_bridge_theorem_sig_end
    ]
    for token in [
        "(ε : Real) (hε : ε ≠ 0)",
        "(hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)",
        "(hRAC : RACRep32CubicObligationSet declared_g_rep32)",
        "(phiBound rhoBound : Real)",
        "(hWeakFieldUniformBound :",
        "(hFirstOrderRemainderSuppressed :",
        "(hELImpliesOperatorResidualUnderBound :",
        "DiscretePoissonResidual1D",
    ]:
        assert token in gr01_bridge_theorem_sig, (
            f"GR01 bridge-promotion theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in gr01_bridge_theorem_sig and "True" not in gr01_bridge_theorem_sig, (
        "GR01 bridge-promotion theorem signature must be non-vacuous."
    )
    gr01_scaling_theorem_sig_start = gr01_scaling_promotion_lean.find(
        "theorem gr01_first_order_truncation_sound"
    )
    assert gr01_scaling_theorem_sig_start >= 0, "Missing GR01 scaling-promotion theorem signature."
    gr01_scaling_theorem_sig_end = gr01_scaling_promotion_lean.find(
        ":=",
        gr01_scaling_theorem_sig_start,
    )
    assert gr01_scaling_theorem_sig_end > gr01_scaling_theorem_sig_start, (
        "Could not isolate GR01 scaling-promotion theorem signature."
    )
    gr01_scaling_theorem_sig = gr01_scaling_promotion_lean[
        gr01_scaling_theorem_sig_start:gr01_scaling_theorem_sig_end
    ]
    for token in [
        "(hPotentialIdentification : PotentialIdentification)",
        "(hSourceIdentification : SourceIdentification)",
        "(hLaplacianExtraction : LaplacianExtraction)",
        "(ε phiScale rhoScale remainderScale : Real)",
        "(hScalingHierarchy :",
        "(hHigherOrderTermsNegligible :",
        "(hRemainderScaleZero : remainderScale = 0)",
        "FirstOrderRemainderSuppressed",
    ]:
        assert token in gr01_scaling_theorem_sig, (
            f"GR01 scaling-promotion theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in gr01_scaling_theorem_sig and "True" not in gr01_scaling_theorem_sig, (
        "GR01 scaling-promotion theorem signature must be non-vacuous."
    )
    gr01_symmetry_theorem_sig_start = gr01_symmetry_promotion_lean.find(
        "theorem gr01_projection_map_well_formed\n"
    )
    assert gr01_symmetry_theorem_sig_start >= 0, "Missing GR01 symmetry-promotion theorem signature."
    gr01_symmetry_theorem_sig_end = gr01_symmetry_promotion_lean.find(
        ":=",
        gr01_symmetry_theorem_sig_start,
    )
    assert gr01_symmetry_theorem_sig_end > gr01_symmetry_theorem_sig_start, (
        "Could not isolate GR01 symmetry-promotion theorem signature."
    )
    gr01_symmetry_theorem_sig = gr01_symmetry_promotion_lean[
        gr01_symmetry_theorem_sig_start:gr01_symmetry_theorem_sig_end
    ]
    for token in [
        "(hPotentialIdentification : PotentialIdentification)",
        "(hSourceIdentification : SourceIdentification)",
        "(carrierWitness : ProjectionCarrierWitness)",
        "(regimeBound : Real)",
        "(hProjectionMapWellFormedPredicate :",
        "ProjectionMapWellFormed",
    ]:
        assert token in gr01_symmetry_theorem_sig, (
            f"GR01 symmetry-promotion theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in gr01_symmetry_theorem_sig and "True" not in gr01_symmetry_theorem_sig, (
        "GR01 symmetry-promotion theorem signature must be non-vacuous."
    )
    gr01_symmetry_theorem_body_start = gr01_symmetry_promotion_lean.find(
        ":= by",
        gr01_symmetry_theorem_sig_start,
    )
    assert gr01_symmetry_theorem_body_start > gr01_symmetry_theorem_sig_start, (
        "Could not isolate GR01 symmetry-promotion theorem body."
    )
    gr01_symmetry_theorem_body = _slice_lean_decl_body(
        gr01_symmetry_promotion_lean, gr01_symmetry_theorem_body_start
    )
    for token in [
        "carrierWitness.potentialCarrier",
        "carrierWitness.sourceCarrier",
        "⟨regimeBound, hRegimePredicate⟩",
    ]:
        assert token in gr01_symmetry_theorem_body, (
            "GR01 symmetry-promotion theorem body must construct "
            "ProjectionMapWellFormed using witness/regime obligations."
        )
    assert "trivial" not in gr01_symmetry_theorem_body, (
        "GR01 symmetry-promotion theorem body must not use trivial placeholders "
        "after ASM-GR01-SYM-01 promotion."
    )
    gr01_end2end_theorem_sig_start = gr01_end2end_closure_lean.find(
        "theorem gr01_end_to_end_chain_bundle_under_promoted_assumptions"
    )
    assert gr01_end2end_theorem_sig_start >= 0, "Missing GR01 end-to-end chain theorem signature."
    gr01_end2end_theorem_sig_end = gr01_end2end_closure_lean.find(
        ":=",
        gr01_end2end_theorem_sig_start,
    )
    assert gr01_end2end_theorem_sig_end > gr01_end2end_theorem_sig_start, (
        "Could not isolate GR01 end-to-end chain theorem signature."
    )
    gr01_end2end_theorem_sig = gr01_end2end_closure_lean[
        gr01_end2end_theorem_sig_start:gr01_end2end_theorem_sig_end
    ]
    for token in [
        "(ε : Real) (hε : ε ≠ 0)",
        "(hAction : actionRep32.action = actionRep32Cubic declared_g_rep32)",
        "(hRAC : RACRep32CubicObligationSet declared_g_rep32)",
        "(carrierWitness : ProjectionCarrierWitness)",
        "(phiBound rhoBound regimeBound phiScale rhoScale remainderScale : Real)",
        "(hWeakFieldUniformBound :",
        "(hHigherOrderTermsNegligible :",
        "(hELImpliesOperatorResidualUnderBound :",
        "GR01EndToEndClosureBundle",
    ]:
        assert token in gr01_end2end_theorem_sig, (
            f"GR01 end-to-end chain theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in gr01_end2end_theorem_sig and "True" not in gr01_end2end_theorem_sig, (
        "GR01 end-to-end chain theorem signature must be non-vacuous."
    )
    gr01_end2end_poisson_sig_start = gr01_end2end_closure_lean.find(
        "theorem gr01_end_to_end_poisson_equation_under_promoted_assumptions"
    )
    assert gr01_end2end_poisson_sig_start >= 0, "Missing GR01 end-to-end Poisson theorem signature."
    gr01_end2end_poisson_sig_end = gr01_end2end_closure_lean.find(
        ":=",
        gr01_end2end_poisson_sig_start,
    )
    assert gr01_end2end_poisson_sig_end > gr01_end2end_poisson_sig_start, (
        "Could not isolate GR01 end-to-end Poisson theorem signature."
    )
    gr01_end2end_poisson_sig = gr01_end2end_closure_lean[
        gr01_end2end_poisson_sig_start:gr01_end2end_poisson_sig_end
    ]
    for token in [
        "(carrierWitness : ProjectionCarrierWitness)",
        "(phiBound rhoBound regimeBound phiScale rhoScale remainderScale : Real)",
        "PoissonEquation1D",
    ]:
        assert token in gr01_end2end_poisson_sig, (
            f"GR01 end-to-end Poisson theorem signature missing explicit assumption token: {token}"
        )
    assert "∃ _" not in gr01_end2end_poisson_sig and "True" not in gr01_end2end_poisson_sig, (
        "GR01 end-to-end Poisson theorem signature must be non-vacuous."
    )
    weak_field_projection_start = theorem_lean.find("structure WeakFieldProjectionFromCore")
    projection_map_start = theorem_lean.find("structure ProjectionMapWellFormed", weak_field_projection_start)
    assert weak_field_projection_start >= 0 and projection_map_start > weak_field_projection_start
    weak_field_projection_block = theorem_lean[weak_field_projection_start:projection_map_start]
    assert re.search(r"^\s*discrete_residual_zero_from_core\s*:", weak_field_projection_block, re.MULTILINE), (
        "WeakFieldProjectionFromCore must expose discrete_residual_zero_from_core."
    )
    assert re.search(r"^\s*residual_zero_from_core\s*:", weak_field_projection_block, re.MULTILINE) is None, (
        "WeakFieldProjectionFromCore must not expose legacy residual_zero_from_core."
    )
    projection_map_end = theorem_lean.find("structure WeakFieldTruncationSound", projection_map_start)
    assert projection_map_end > projection_map_start, (
        "Could not isolate ProjectionMapWellFormed structure block."
    )
    projection_map_block = theorem_lean[projection_map_start:projection_map_end]
    for token in [
        "potential_carrier_defined",
        "source_carrier_defined",
        "weak_field_regime_exists",
        "∃ potentialCarrier",
        "∃ sourceCarrier",
        "∃ regimeBound",
    ]:
        assert token in projection_map_block, (
            f"ProjectionMapWellFormed must expose nontrivial obligation field: {token}"
        )
    assert re.search(r":\s*True\b", projection_map_block) is None, (
        "ProjectionMapWellFormed must not use True-placeholder obligation fields."
    )
    assert re.search(r":=\s*True\b", projection_map_block) is None, (
        "ProjectionMapWellFormed must not assign True placeholders in obligation fields."
    )

    assert theorem_lean.count("def PoissonEquation1D") == 1, (
        "WeakFieldPoissonLimit.lean must contain exactly one PoissonEquation1D definition."
    )
    assert theorem_lean.count("structure WeakFieldAnsatz where") == 1
    assert theorem_lean.count("structure SmallPerturbationExpansion where") == 1
    assert theorem_lean.count("structure PotentialIdentification where") == 1
    assert theorem_lean.count("structure SourceIdentification where") == 1
    assert theorem_lean.count("structure LaplacianExtraction where") == 1
    assert theorem_lean.count("structure UnitsAndCalibration where") == 1

    theorem_sig_start = theorem_lean.find(
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions"
    )
    assert theorem_sig_start >= 0, "Missing TOE_GR01 theorem signature."
    theorem_sig_end = theorem_lean.find("WeakFieldPoissonLimitStatement := by", theorem_sig_start)
    assert theorem_sig_end > theorem_sig_start, "Could not isolate TOE_GR01 theorem signature."
    theorem_sig = theorem_lean[theorem_sig_start:theorem_sig_end]
    for token in [
        "(hProjectionMapWellFormed :",
        "(hWeakFieldTruncationSound :",
        "(hELImpliesDiscretePoissonResidual :",
    ]:
        assert token in theorem_sig, f"TOE_GR01 theorem signature missing bridge component: {token}"
    assert "(hProjectionFromCore :" not in theorem_sig, (
        "TOE_GR01 theorem signature still accepts monolithic hProjectionFromCore input."
    )
    assert "ELImpliesProjectedResidual" not in theorem_sig, (
        "TOE_GR01 theorem signature must not accept legacy ELImpliesProjectedResidual."
    )
    constructor_start = theorem_lean.find("def mkWeakFieldProjectionFromCore")
    constructor_end = theorem_lean.find("def WeakFieldPoissonLimitStatement", constructor_start)
    assert constructor_start >= 0 and constructor_end > constructor_start
    constructor_block = theorem_lean[constructor_start:constructor_end]
    assert constructor_block.count("discrete_residual_zero_from_core :=") == 1, (
        "mkWeakFieldProjectionFromCore must construct exactly one discrete residual output field."
    )
    assert re.search(r"^\s*residual_zero_from_core\s*:=", constructor_block, re.MULTILINE) is None, (
        "mkWeakFieldProjectionFromCore must not construct legacy residual_zero_from_core."
    )

    assert calibration_record.get("schema") == "TOE-GR-01/kappa_calibration_record/v0"
    assert isinstance(calibration_record.get("fingerprint"), str) and len(calibration_record["fingerprint"]) == 64
    record_without_fp = dict(calibration_record)
    fp = str(record_without_fp.pop("fingerprint"))
    recomputed = hashlib.sha256(
        json.dumps(record_without_fp, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    ).hexdigest()
    assert fp == recomputed, "TOE-GR-01 calibration record fingerprint mismatch."
    for token in [
        "TOE-GR-01_kappa_calibration_v0.md",
        fp,
    ]:
        assert token in calibration_lock, f"Calibration lock missing token: {token}"
