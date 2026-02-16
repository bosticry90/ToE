from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RESULTS_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
ASSUMPTION_REGISTRY_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
STRUCTURAL_CLOSENESS_MAP_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "STRUCTURAL_CLOSENESS_MAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def test_results_table_has_expected_columns_and_labels() -> None:
    text = _read(RESULTS_DOC)
    required_tokens = [
        "Results Table v0",
        "Result ID",
        "Claim label",
        "Statement",
        "Evidence pointer",
        "Scope limits",
        "Non-claims",
        "`T-PROVED`",
        "`T-CONDITIONAL`",
        "`E-REPRO`",
        "`P-POLICY`",
        "`B-BLOCKED`",
        "TOE-MAP-01",
        "STRUCTURAL_CLOSENESS_MAP_v0.md",
        "TOE-ASM-01",
        "ASSUMPTION_REGISTRY_v1.md",
        "TOE-QM-PLAN-01",
        "DERIVATION_TARGET_QM_MEASUREMENT_SEMANTICS_v0.md",
        "TOE-QM-PLAN-03",
        "DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md",
        "TOE-QM-THM-01",
        "QM/EvolutionContract.lean",
        "TOE-QM-PLAN-02",
        "DERIVATION_TARGET_QM_SYMMETRY_OBJECT_v0.md",
        "TOE-QFT-PLAN-01",
        "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md",
        "TOE-QFT-PLAN-02",
        "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
        "TOE-GR-PLAN-02",
        "DERIVATION_TARGET_GR_GEOMETRY_OBJECT_v0.md",
        "TOE-GR-PLAN-03",
        "DERIVATION_TARGET_GR_CONSERVATION_OBJECT_v0.md",
        "TOE-GR-PLAN-04",
        "DERIVATION_TARGET_GR01_BRIDGE_PROMOTION_v0.md",
        "TOE-GR-PLAN-05",
        "DERIVATION_TARGET_GR01_REGIME_PROMOTION_v0.md",
        "TOE-GR-PLAN-06",
        "DERIVATION_TARGET_GR01_SCALING_PROMOTION_v0.md",
        "TOE-GR-PLAN-07",
        "DERIVATION_TARGET_GR01_SYMMETRY_PROMOTION_v0.md",
        "TOE-GR-PLAN-08",
        "DERIVATION_TARGET_GR01_END_TO_END_CLOSURE_v0.md",
        "GR01BridgePromotion.lean",
        "GR01ScalingPromotion.lean",
        "GR01SymmetryPromotion.lean",
        "GR01EndToEndClosure.lean",
        "TOE-GR-REG-01",
        "gr01_regime_predicate_under_uniform_bound",
        "TOE-GR-APP-01",
        "gr01_first_order_truncation_sound",
        "TOE-GR-SYM-01",
        "gr01_projection_map_well_formed",
        "TOE-GR-CLS-01",
        "gr01_end_to_end_chain_bundle_under_promoted_assumptions",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
        "TOE-GR-3D-01",
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TOE-GR-3D-PS-01",
        "TOE-GR-3D-PS-02",
        "TOE-GR-3D-PS-03",
        "TOE-GR-3D-PS-04",
        "TOE-GR-3D-PS-05",
        "TOE-GR-3D-PS-06",
        "TOE-GR-3D-PS-07",
        "TOE-GR-3D-PS-08",
        "TOE-GR-3D-PS-09",
        "TOE-GR-3D-PS-10",
        "TOE-GR-3D-PS-11",
        "TOE-GR-3D-PS-12",
        "TOE-GR-CONS-01",
        "poissonEquation3D_of_poissonEquation1D_under_lift_x_only",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md",
        "TARGET-GR01-3D-03-PLAN",
        "TARGET-GR01-3D-POINT-SOURCE-PLAN",
        "gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry",
        "gr01_mainstream3d_point_source_partial_surface_token",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system",
        "gr01_mainstream3d_point_source_system_satisfaction_from_linear_system",
        "gr01_mainstream3d_point_source_candidate_exists_from_linear_system",
        "gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation",
        "gr01_mainstream3d_point_source_candidate_exists_from_operator_equation",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation",
        "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
        "SatisfiesFiniteLinearOperatorEquationOnDomain",
        "OperatorEncodesDiscreteLaplacianOnInterior",
        "OperatorHasDirichletRightInverseOnDomain",
        "DirichletLinearOperator3D",
        "DirichletRHS3D",
        "SatisfiesDirichletLinearSystemOnDomain",
        "IsInteriorPoint",
        "SatisfiesDirichletPoissonSystemOnDomain",
        "PointSourceDirichletCandidateSolution",
        "DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md",
        "GR01Mainstream3DPointSource.lean",
        "TOE-GR-DER-02",
        "TOE_GR01_ANALYTIC_DISCHARGE_v0.md",
    ]
    for token in required_tokens:
        assert token in text, f"Results table missing token: {token}"


def test_results_table_evidence_pointers_exist() -> None:
    text = _read(RESULTS_DOC)
    pointers = re.findall(r"`(formal/[A-Za-z0-9_./-]+(?:\.(?:lean|md|json|txt)))`", text)
    assert pointers, "No evidence pointers detected in results table."

    missing: list[str] = []
    for rel in sorted(set(pointers)):
        if not (REPO_ROOT / rel).exists():
            missing.append(rel)
    assert missing == [], "Results table references missing evidence pointers:\n" + "\n".join(missing)


def test_results_table_result_ids_are_unique() -> None:
    text = _read(RESULTS_DOC)
    ids = re.findall(r"^\|\s*([A-Z0-9-]+)\s*\|", text, flags=re.MULTILINE)
    counts: dict[str, int] = {}
    for result_id in ids:
        counts[result_id] = counts.get(result_id, 0) + 1
    duplicates = sorted([result_id for result_id, count in counts.items() if count > 1])
    assert duplicates == [], "Results table has duplicate Result IDs:\n" + "\n".join(duplicates)


def test_gr01_bridge_row_matches_assumption_registry_status() -> None:
    results = _read(RESULTS_DOC)
    registry = _read(ASSUMPTION_REGISTRY_DOC)
    status_match = re.search(
        r"^\|\s*`ASM-GR01-APP-02`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        registry,
        flags=re.MULTILINE,
    )
    assert status_match is not None, "Assumption registry must define ASM-GR01-APP-02 status."
    asm_status = status_match.group(1)
    row_match = re.search(
        r"^\|\s*TOE-GR-BRG-02\s*\|\s*`([^`]+)`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-BRG-02."
    row_label = row_match.group(1)
    row_statement = row_match.group(2).lower()
    assert row_label == asm_status, (
        "TOE-GR-BRG-02 claim label must match ASM-GR01-APP-02 status in assumption registry."
    )
    if asm_status == "T-CONDITIONAL":
        assert "policy-scoped" not in row_statement, (
            "TOE-GR-BRG-02 statement cannot call the bridge policy-scoped after promotion."
        )


def test_gr01_regime_row_matches_assumption_registry_status() -> None:
    results = _read(RESULTS_DOC)
    registry = _read(ASSUMPTION_REGISTRY_DOC)
    status_match = re.search(
        r"^\|\s*`ASM-GR01-REG-01`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        registry,
        flags=re.MULTILINE,
    )
    assert status_match is not None, "Assumption registry must define ASM-GR01-REG-01 status."
    asm_status = status_match.group(1)
    row_match = re.search(
        r"^\|\s*TOE-GR-REG-01\s*\|\s*`([^`]+)`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-REG-01."
    row_label = row_match.group(1)
    row_statement = row_match.group(2).lower()
    assert row_label == asm_status, (
        "TOE-GR-REG-01 claim label must match ASM-GR01-REG-01 status in assumption registry."
    )
    if asm_status == "T-CONDITIONAL":
        assert "policy-level" not in row_statement, (
            "TOE-GR-REG-01 statement cannot describe the regime assumption as policy-level "
            "after promotion."
        )


def test_gr01_scaling_row_matches_assumption_registry_status() -> None:
    results = _read(RESULTS_DOC)
    registry = _read(ASSUMPTION_REGISTRY_DOC)
    status_match = re.search(
        r"^\|\s*`ASM-GR01-APP-01`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        registry,
        flags=re.MULTILINE,
    )
    assert status_match is not None, "Assumption registry must define ASM-GR01-APP-01 status."
    asm_status = status_match.group(1)
    row_match = re.search(
        r"^\|\s*TOE-GR-APP-01\s*\|\s*`([^`]+)`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-APP-01."
    row_label = row_match.group(1)
    row_statement = row_match.group(2).lower()
    assert row_label == asm_status, (
        "TOE-GR-APP-01 claim label must match ASM-GR01-APP-01 status in assumption registry."
    )
    if asm_status == "T-CONDITIONAL":
        assert "policy-level" not in row_statement, (
            "TOE-GR-APP-01 statement cannot describe the scaling assumption as policy-level "
            "after promotion."
        )


def test_gr01_symmetry_row_matches_assumption_registry_status() -> None:
    results = _read(RESULTS_DOC)
    registry = _read(ASSUMPTION_REGISTRY_DOC)
    status_match = re.search(
        r"^\|\s*`ASM-GR01-SYM-01`\s*\|\s*`[^`]+`\s*\|\s*`([^`]+)`\s*\|",
        registry,
        flags=re.MULTILINE,
    )
    assert status_match is not None, "Assumption registry must define ASM-GR01-SYM-01 status."
    asm_status = status_match.group(1)
    row_match = re.search(
        r"^\|\s*TOE-GR-SYM-01\s*\|\s*`([^`]+)`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-SYM-01."
    row_label = row_match.group(1)
    row_statement = row_match.group(2).lower()
    assert row_label == asm_status, (
        "TOE-GR-SYM-01 claim label must match ASM-GR01-SYM-01 status in assumption registry."
    )
    if asm_status == "T-CONDITIONAL":
        assert "policy-level" not in row_statement, (
            "TOE-GR-SYM-01 statement cannot describe the symmetry assumption as policy-level "
            "after promotion."
        )


def test_gr01_key_result_rows_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    for result_id in [
        "TOE-GR-BRG-02",
        "TOE-GR-BRG-03",
        "TOE-GR-DER-02",
        "TOE-GR-REG-01",
        "TOE-GR-APP-01",
        "TOE-GR-SYM-01",
        "TOE-GR-3D-01",
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TOE-GR-3D-PS-01",
        "TOE-GR-3D-PS-02",
        "TOE-GR-3D-PS-03",
        "TOE-GR-3D-PS-04",
        "TOE-GR-3D-PS-05",
        "TOE-GR-3D-PS-06",
        "TOE-GR-3D-PS-07",
        "TOE-GR-3D-PS-08",
        "TOE-GR-3D-PS-09",
        "TOE-GR-3D-PS-10",
        "TOE-GR-3D-PS-11",
        "TOE-GR-3D-PS-12",
        "TOE-GR-CONS-01",
        "TOE-GR-PLAN-08",
        "TOE-GR-CLS-01",
    ]:
        count = len(re.findall(rf"^\|\s*{re.escape(result_id)}\s*\|", results, flags=re.MULTILINE))
        assert count == 1, f"{result_id} must appear exactly once in results table (found {count})."


def test_gr01_plan08_row_uses_post_cls_wording() -> None:
    results = _read(RESULTS_DOC)
    row_match = re.search(
        r"^\|\s*TOE-GR-PLAN-08\s*\|\s*`([^`]+)`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-PLAN-08."
    row_statement = row_match.group(2)
    assert "theorem-chain closure audit" in row_statement, (
        "TOE-GR-PLAN-08 must use post-CLS theorem-chain closure audit wording."
    )
    assert "theorem-chain composition + analytic alignment" not in row_statement, (
        "TOE-GR-PLAN-08 must not use stale pre-CLS composition/alignment wording."
    )


def test_results_table_track_a_residual_reduction_token_is_singleton() -> None:
    results = _read(RESULTS_DOC)
    token = "gr01_mainstream3d_discrete_residual_reduces_to_radial_under_spherical_symmetry"
    row_count = len(
        re.findall(
            r"^\|\s*TOE-GR-3D-03\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        "Results table must contain exactly one TOE-GR-3D-03 row."
    )
    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track A residual-reduction token occurrence "
        f"(found {token_count})."
    )
    row_match = re.search(
        r"^\|\s*TOE-GR-3D-03\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-03 row."
    row_statement = row_match.group(1)
    assert token in row_statement, (
        "Track A residual-reduction token must appear in the TOE-GR-3D-03 statement cell."
    )


def test_results_table_track_b_point_source_token_is_singleton() -> None:
    results = _read(RESULTS_DOC)
    token = "gr01_mainstream3d_point_source_partial_surface_token"
    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B point-source partial-surface token occurrence "
        f"(found {token_count})."
    )
    row_match = re.search(
        r"^\|\s*TOE-GR-3D-03\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-03 row."
    row_statement = row_match.group(1)
    assert token in row_statement, (
        "Track B point-source token must appear in the TOE-GR-3D-03 statement cell."
    )


def test_results_table_track_b_away_from_source_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-01"
    token = "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_under_dirichlet_boundary"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B away-from-source Poisson token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-01\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-01 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B away-from-source Poisson token must appear in the TOE-GR-3D-PS-01 statement cell."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-01 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-01 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-01 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_domain_characterization_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-02"
    token = "gr01_mainstream3d_point_source_domain_residual_characterization_under_dirichlet_boundary"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B domain-characterization token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-02\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-02 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B domain-characterization token must appear in the TOE-GR-3D-PS-02 statement cell."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-02 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-02 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-02 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_residual_discharge_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-03"
    token = "gr01_mainstream3d_point_source_residual_discharge_under_dirichlet_boundary"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B residual-discharge token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-03\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-03 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B residual-discharge token must appear in the TOE-GR-3D-PS-03 statement cell."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-03 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-03 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-03 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_center_defect_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-04"
    token = "gr01_mainstream3d_point_source_center_residual_defect_is_explicit_under_dirichlet_boundary"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B center-defect token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-04\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-04 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B center-defect token must appear in the TOE-GR-3D-PS-04 statement cell."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-04 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-04 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-04 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_derived_from_dirichlet_system_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-05"
    token = "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_derived_from_dirichlet_system"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B derived-from-system token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-05\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-05 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B derived-from-system token must appear in the TOE-GR-3D-PS-05 statement cell."
    )
    assert "SatisfiesDirichletPoissonSystemOnDomain" in row_statement, (
        "TOE-GR-3D-PS-05 statement must anchor the system-satisfaction predicate."
    )
    assert "PointSourceDirichletCandidateSolution" in row_statement, (
        "TOE-GR-3D-PS-05 statement must anchor the candidate-solution object."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-05 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-05 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-05 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_linear_to_system_bridge_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-06"
    token = "gr01_mainstream3d_point_source_system_satisfaction_from_linear_system"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B linear-to-system bridge token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-06\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-06 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B linear-to-system bridge token must appear in the TOE-GR-3D-PS-06 statement cell."
    )
    assert "SatisfiesDirichletLinearSystemOnDomain" in row_statement, (
        "TOE-GR-3D-PS-06 statement must anchor the linear-system predicate."
    )
    assert "IsInteriorPoint" in row_statement, (
        "TOE-GR-3D-PS-06 statement must anchor the interior-point predicate."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-06 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-06 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-06 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_candidate_exists_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-07"
    token = "gr01_mainstream3d_point_source_candidate_exists_from_linear_system"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B candidate-exists token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-07\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-07 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B candidate-exists token must appear in the TOE-GR-3D-PS-07 statement cell."
    )
    assert "SatisfiesDirichletLinearSystemOnDomain" in row_statement, (
        "TOE-GR-3D-PS-07 statement must anchor the linear-system predicate."
    )
    assert "PointSourceDirichletCandidateSolution" in row_statement, (
        "TOE-GR-3D-PS-07 statement must anchor the candidate packaging object."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-07 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-07 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-07 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_operator_equation_bridge_promotion_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-08"
    token = "gr01_mainstream3d_point_source_linear_system_satisfaction_from_operator_equation"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B operator-equation bridge token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-08\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-08 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B operator-equation bridge token must appear in the TOE-GR-3D-PS-08 statement cell."
    )
    assert "SatisfiesFiniteLinearOperatorEquationOnDomain" in row_statement, (
        "TOE-GR-3D-PS-08 statement must anchor the operator-equation predicate."
    )
    assert "DirichletLinearOperator3D" in row_statement, (
        "TOE-GR-3D-PS-08 statement must anchor the operator object."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-08 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-08 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-08 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_candidate_exists_from_operator_equation_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-09"
    token = "gr01_mainstream3d_point_source_candidate_exists_from_operator_equation"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B operator-to-candidate token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-09\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-09 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B operator-to-candidate token must appear in the TOE-GR-3D-PS-09 statement cell."
    )
    assert "SatisfiesFiniteLinearOperatorEquationOnDomain" in row_statement, (
        "TOE-GR-3D-PS-09 statement must anchor the operator-equation predicate."
    )
    assert "PointSourceDirichletCandidateSolution" in row_statement, (
        "TOE-GR-3D-PS-09 statement must anchor the candidate packaging object."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-09 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-09 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-09 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_operator_to_poisson_away_from_source_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-10"
    token = "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_from_operator_equation"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 1, (
        "Results table must contain exactly one Track B operator-to-away-from-source token occurrence "
        f"(found {token_count})."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-10\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-10 T-CONDITIONAL row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B operator-to-away-from-source token must appear in the TOE-GR-3D-PS-10 statement cell."
    )
    assert "SatisfiesFiniteLinearOperatorEquationOnDomain" in row_statement, (
        "TOE-GR-3D-PS-10 statement must anchor the operator-equation predicate."
    )
    assert "PoissonEquation3DAwayFromSourceOnDomain" in row_statement, (
        "TOE-GR-3D-PS-10 statement must anchor the away-from-source closure object."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-10 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-10 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-10 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_solver_existence_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-11"
    token = "gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 2, (
        "Results table must contain exactly two Track B solver-existence token occurrences "
        "(TOE-GR-3D-03 closure row + TOE-GR-3D-PS-11 row). "
        f"Found {token_count}."
    )

    gate_row_match = re.search(
        r"^\|\s*TOE-GR-3D-03\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert gate_row_match is not None, "Results table must include TOE-GR-3D-03 T-CONDITIONAL row."
    assert token in gate_row_match.group(1), (
        "TOE-GR-3D-03 closure statement must include the Track B solver-existence token."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-11\s*\|\s*`T-PROVED`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-11 T-PROVED row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B solver-existence token must appear in the TOE-GR-3D-PS-11 statement cell."
    )
    assert "OperatorHasDirichletRightInverseOnDomain" in row_statement, (
        "TOE-GR-3D-PS-11 statement must anchor the solver-grade invertibility posture."
    )
    assert "∃ Φ" in row_statement, (
        "TOE-GR-3D-PS-11 statement must explicitly anchor existential candidate posture."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-11 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-11 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-11 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_solver_existential_closure_row_and_token_are_singletons() -> None:
    results = _read(RESULTS_DOC)
    result_id = "TOE-GR-3D-PS-12"
    token = "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility"
    lean_pointer = "formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean"

    row_count = len(
        re.findall(
            rf"^\|\s*{re.escape(result_id)}\s*\|",
            results,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        f"Results table must contain exactly one {result_id} row (found {row_count})."
    )

    token_count = results.count(token)
    assert token_count == 2, (
        "Results table must contain exactly two Track B solver existential-closure token occurrences "
        "(TOE-GR-3D-03 closure row + TOE-GR-3D-PS-12 row). "
        f"Found {token_count}."
    )

    gate_row_match = re.search(
        r"^\|\s*TOE-GR-3D-03\s*\|\s*`T-CONDITIONAL`\s*\|\s*(.+?)\s*\|\s*$",
        results,
        flags=re.MULTILINE,
    )
    assert gate_row_match is not None, "Results table must include TOE-GR-3D-03 T-CONDITIONAL row."
    assert token in gate_row_match.group(1), (
        "TOE-GR-3D-03 closure statement must include the Track B solver existential-closure token."
    )

    row_match = re.search(
        r"^\|\s*TOE-GR-3D-PS-12\s*\|\s*`T-PROVED`\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$",
        results,
        flags=re.MULTILINE,
    )
    assert row_match is not None, "Results table must include TOE-GR-3D-PS-12 T-PROVED row."
    row_statement = row_match.group(1)
    row_evidence = row_match.group(2)
    row_non_claims = row_match.group(4)

    assert token in row_statement, (
        "Track B solver existential-closure token must appear in the TOE-GR-3D-PS-12 statement cell."
    )
    assert "PoissonEquation3DAwayFromSourceOnDomain" in row_statement, (
        "TOE-GR-3D-PS-12 statement must anchor away-from-source closure object."
    )
    assert "∃ Φ" in row_statement, (
        "TOE-GR-3D-PS-12 statement must explicitly anchor existential closure posture."
    )
    assert lean_pointer in row_evidence, (
        "TOE-GR-3D-PS-12 evidence cell must reference the Track B Lean scaffold module."
    )
    assert "no continuum-limit claim" in row_non_claims.lower(), (
        "TOE-GR-3D-PS-12 non-claims cell must preserve no-continuum-limit boundary wording."
    )
    assert "does not promote `TOE-GR-3D-03`" in row_non_claims, (
        "TOE-GR-3D-PS-12 non-claims cell must state that it does not promote TOE-GR-3D-03."
    )


def test_results_table_track_b_solver_elimination_promotion_boundary_is_enforced() -> None:
    results = _read(RESULTS_DOC)
    assert re.search(
        r"^\|\s*TOE-GR-3D-PS-10\s*\|\s*`T-CONDITIONAL`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "TOE-GR-3D-PS-10 must remain T-CONDITIONAL (pre-existential composition rung)."
    assert re.search(
        r"^\|\s*TOE-GR-3D-PS-11\s*\|\s*`T-PROVED`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "TOE-GR-3D-PS-11 must be T-PROVED after solver-elimination existential discharge."
    assert re.search(
        r"^\|\s*TOE-GR-3D-PS-12\s*\|\s*`T-PROVED`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "TOE-GR-3D-PS-12 must be T-PROVED after existential away-from-source closure discharge."
    assert not re.search(
        r"^\|\s*TOE-GR-3D-PS-11\s*\|\s*`T-CONDITIONAL`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "Legacy TOE-GR-3D-PS-11 T-CONDITIONAL row must not be present once promoted."
    assert not re.search(
        r"^\|\s*TOE-GR-3D-PS-12\s*\|\s*`T-CONDITIONAL`\s*\|",
        results,
        flags=re.MULTILINE,
    ), "Legacy TOE-GR-3D-PS-12 T-CONDITIONAL row must not be present once promoted."


def test_structural_map_gr01_rows_are_singletons() -> None:
    structural_map = _read(STRUCTURAL_CLOSENESS_MAP_DOC)
    gr_der02_row_count = len(
        re.findall(
            r"^\|\s*`PILLAR-GR`\s*\|\s*limit recoveries\s*\|\s*`B-BLOCKED`\s*\|\s*`TOE-GR-DER-02`\s*\|",
            structural_map,
            flags=re.MULTILINE,
        )
    )
    assert gr_der02_row_count == 1, (
        "Structural closeness map must contain exactly one PILLAR-GR limit-recoveries row for TOE-GR-DER-02."
    )
    end2end_row_count = len(
        re.findall(
            r"^\|\s*`PILLAR-GR`\s*\|\s*end-to-end closure criteria \(planning-pointer\)\s*\|\s*`P-POLICY`\s*\|\s*`TARGET-GR01-END2END-CLOSURE-PLAN`\s*\|",
            structural_map,
            flags=re.MULTILINE,
        )
    )
    assert end2end_row_count == 1, (
        "Structural closeness map must contain exactly one end-to-end closure planning-pointer row."
    )
    mainstream_3d_row_count = len(
        re.findall(
            r"^\|\s*`PILLAR-GR`\s*\|\s*3D weak-field mapping \(mainstream-class gate\)\s*\|\s*`T-CONDITIONAL`\s*\|\s*`TOE-GR-3D-03`\s*\|",
            structural_map,
            flags=re.MULTILINE,
        )
    )
    assert mainstream_3d_row_count == 1, (
        "Structural closeness map must contain exactly one mainstream-class 3D gate row for TOE-GR-3D-03."
    )


def test_structural_map_toe_gr_3d_03_claim_id_is_singleton_by_prefix() -> None:
    structural_map = _read(STRUCTURAL_CLOSENESS_MAP_DOC)
    row_count = len(
        re.findall(
            r"^\|\s*`PILLAR-GR`\s*\|.*?\|\s*`TOE-GR-3D-03`\s*\|",
            structural_map,
            flags=re.MULTILINE,
        )
    )
    assert row_count == 1, (
        "Structural closeness map must include exactly one PILLAR-GR table row carrying claim ID TOE-GR-3D-03."
    )


def test_structural_map_end2end_target_bullet_is_singleton() -> None:
    structural_map = _read(STRUCTURAL_CLOSENESS_MAP_DOC)
    bullet_count = len(
        re.findall(
            r"^- `TARGET-GR01-END2END-CLOSURE-PLAN`:",
            structural_map,
            flags=re.MULTILINE,
        )
    )
    assert bullet_count == 1, (
        "Structural closeness map must include exactly one TARGET-GR01-END2END-CLOSURE-PLAN frozen-target bullet."
    )


def test_structural_map_mainstream_3d_target_bullet_is_singleton() -> None:
    structural_map = _read(STRUCTURAL_CLOSENESS_MAP_DOC)
    bullet_count = len(
        re.findall(
            r"^- `TARGET-GR01-3D-03-PLAN`:",
            structural_map,
            flags=re.MULTILINE,
        )
    )
    assert bullet_count == 1, (
        "Structural closeness map must include exactly one TARGET-GR01-3D-03-PLAN frozen-target bullet."
    )


def test_structural_map_track_b_point_source_target_bullet_is_singleton() -> None:
    structural_map = _read(STRUCTURAL_CLOSENESS_MAP_DOC)
    bullet_count = len(
        re.findall(
            r"^- `TARGET-GR01-3D-POINT-SOURCE-PLAN`:",
            structural_map,
            flags=re.MULTILINE,
        )
    )
    assert bullet_count == 1, (
        "Structural closeness map must include exactly one TARGET-GR01-3D-POINT-SOURCE-PLAN frozen-target bullet."
    )
