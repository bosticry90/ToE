from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.claim_label_policy import (
    CURRENT_RELEASE_LABELS,
    validate_release_claim_row,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"

STANDARD_JSON = RELEASE_DIR / "TOE_V01_ALPHA_RELEASE_STANDARD_20260513_v0.json"
LANE_SELECTION_JSON = RELEASE_DIR / "TOE_V01_ALPHA_RELEASE_STANDARD_LANE_SELECTION_20260513_v0.json"
COVERAGE_JSON = RELEASE_DIR / "TOE_V01_ALPHA_PILLAR_SEAM_COVERAGE_LEDGER_v0.json"
CLAIM_JSON = RELEASE_DIR / "TOE_V01_ALPHA_CLAIM_EVIDENCE_LEDGER_v0.json"
EQUATION_JSON = RELEASE_DIR / "TOE_V01_ALPHA_EQUATION_LEDGER_v0.json"
BLOCKER_JSON = RELEASE_DIR / "TOE_V01_ALPHA_BLOCKER_LEDGER_v0.json"
LEAN_AUDIT_MD = RELEASE_DIR / "TOE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_v0.md"
LEAN_INDEX = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
TAXONOMY_V1 = PAPER_DIR / "CLAIM_TAXONOMY_v1.md"

REQUIRED_DOMAINS = {
    "GR",
    "QM",
    "EM",
    "SR",
    "SCALAR_QFT",
    "STAT",
    "COSMO",
    "QFT_GR",
    "QM_STAT",
    "EM_QFT",
    "SR_COSMO",
    "GR_QM",
    "MASTER_ACTION",
}

STABLE_NONCLAIM_IDS = {
    "NC-NO-MASTER-ACTION-PROMOTION",
    "NC-NO-PILLAR-COMPLETION",
    "NC-NO-SEAM-CLOSURE",
    "NC-NO-PHASE2",
    "NC-NO-EMPIRICAL-ADEQUACY",
    "NC-NO-CANONICAL-TOE",
    "NC-NO-QFT-GR-SOURCE-MAP-CLOSURE",
}

REQUIRED_ROW_FIELDS = {
    "row_id",
    "domain",
    "domain_type",
    "claim",
    "primary_label",
    "supporting_labels",
    "release_status",
    "release_row_status",
    "evidence",
    "evidence_type",
    "row_source",
    "source_freshness",
    "assumptions",
    "blockers",
    "nonclaim_ids",
    "not_authorized_claims",
    "dependency_audit",
    "closure_authorized",
    "next_work",
    "release_interpretation",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required v0.1-alpha artifact: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _evidence_path_exists(pointer: str) -> bool:
    rel = pointer.split("::", 1)[0].split("#", 1)[0]
    return (REPO_ROOT / rel).exists()


def test_v01_alpha_foundational_artifacts_exist() -> None:
    for path in (
        TAXONOMY_V1,
        STANDARD_JSON,
        LANE_SELECTION_JSON,
        COVERAGE_JSON,
        CLAIM_JSON,
        EQUATION_JSON,
        BLOCKER_JSON,
        LEAN_AUDIT_MD,
        LEAN_INDEX,
        RELEASE_DIR / "TOE_V01_ALPHA_RELEASE_STANDARD_v0.md",
        RELEASE_DIR / "TOE_V01_ALPHA_PILLAR_SEAM_COVERAGE_LEDGER_v0.md",
        RELEASE_DIR / "TOE_V01_ALPHA_CLAIM_EVIDENCE_LEDGER_v0.md",
        RELEASE_DIR / "TOE_V01_ALPHA_EQUATION_LEDGER_v0.md",
        RELEASE_DIR / "TOE_V01_ALPHA_BLOCKER_LEDGER_v0.md",
    ):
        assert path.exists(), f"Missing v0.1-alpha artifact: {path}"


def test_release_standard_defines_full_pillar_full_seam_scope() -> None:
    standard = _json(STANDARD_JSON)
    selector = _json(LANE_SELECTION_JSON)

    assert standard["result_token"] == "TOE_V01_ALPHA_RELEASE_STANDARD_PREPARED_FULL_PILLAR_SEAM_SCOPE"
    assert selector["result_token"] == "TOE_V01_ALPHA_RELEASE_STANDARD_LANE_SELECTED"
    assert selector["selected_scope"] == "FULL_PILLAR_FULL_SEAM_RELEASE_STANDARD"
    assert selector["selected_target"] == "prepare_toe_v01_alpha_release_standard_packet"
    assert selector["governance_manifest_enrollment_authorized"] is False
    assert selector["scientific_status_change_authorized"] is False

    assert set(standard["current_claim_labels"]) == CURRENT_RELEASE_LABELS
    assert set(standard["pillar_seam_row_set"]) == REQUIRED_DOMAINS
    assert set(standard["stable_nonclaim_ids"]) == STABLE_NONCLAIM_IDS
    assert standard["governance_manifest_enrollment_authorized"] is False
    assert standard["release_completion_claim_authorized"] is False


def test_pillar_seam_coverage_ledger_is_structurally_complete() -> None:
    payload = _json(COVERAGE_JSON)
    rows = payload["rows"]
    assert {row["domain"] for row in rows} == REQUIRED_DOMAINS
    assert len({row["row_id"] for row in rows}) == len(rows)

    violations: list[str] = []
    for row in rows:
        missing = sorted(REQUIRED_ROW_FIELDS - set(row))
        if missing:
            violations.append(f"{row.get('row_id', '<unknown>')}: missing {missing}")
            continue

        errors = validate_release_claim_row({**row, "context_type": "v01_alpha_ledger"})
        if errors:
            violations.append(f"{row['row_id']}: " + "; ".join(errors))
        if row["closure_authorized"] is not False:
            violations.append(f"{row['row_id']}: closure_authorized must be false in seed ledger")
        if row["source_freshness"] != "current":
            violations.append(f"{row['row_id']}: source_freshness must be current")
        if row["release_row_status"] != "seeded":
            violations.append(f"{row['row_id']}: release_row_status must be seeded")
        if not row["evidence"] or not row["evidence_type"]:
            violations.append(f"{row['row_id']}: evidence and evidence_type are required")
        if not row["not_authorized_claims"]:
            violations.append(f"{row['row_id']}: not_authorized_claims must be non-empty")
        if not set(row["nonclaim_ids"]).issubset(STABLE_NONCLAIM_IDS):
            violations.append(f"{row['row_id']}: unknown nonclaim id")
        missing_evidence = [ptr for ptr in row["evidence"] if not _evidence_path_exists(ptr)]
        if missing_evidence:
            violations.append(f"{row['row_id']}: missing evidence pointers {missing_evidence}")

    assert not violations, "Coverage ledger violations:\n- " + "\n- ".join(violations)


def test_claim_equation_and_blocker_ledgers_use_current_labels_and_existing_evidence() -> None:
    violations: list[str] = []
    for path in (CLAIM_JSON, BLOCKER_JSON):
        for row in _json(path)["rows"]:
            errors = validate_release_claim_row({**row, "context_type": "v01_alpha_ledger"})
            if errors:
                violations.append(f"{path.name}:{row.get('row_id') or row.get('blocker_id')}: " + "; ".join(errors))
            if row.get("closure_authorized") not in (False, None):
                violations.append(f"{path.name}:{row.get('row_id')}: closure_authorized must not be true")
            for ptr in row.get("evidence", []) + row.get("current_evidence", []):
                if not _evidence_path_exists(ptr):
                    violations.append(f"{path.name}:{row.get('row_id') or row.get('blocker_id')}: missing {ptr}")

    for row in _json(EQUATION_JSON)["rows"]:
        errors = validate_release_claim_row({**row, "context_type": "v01_alpha_ledger"})
        if errors:
            violations.append(f"{EQUATION_JSON.name}:{row['equation_id']}: " + "; ".join(errors))
        assert row["closure_authorized"] is False
        assert row["failure_condition"]
        for ptr in row["evidence"]:
            if not _evidence_path_exists(ptr):
                violations.append(f"{EQUATION_JSON.name}:{row['equation_id']}: missing {ptr}")

    assert not violations, "Release ledger violations:\n- " + "\n- ".join(violations)


def test_lean_dependency_audit_covers_release_index_theorems() -> None:
    audit_text = _read(LEAN_AUDIT_MD)
    index_text = _read(LEAN_INDEX)
    required_theorems = [
        "master_action_stationary_implies_free_scalar_kg",
        "stationary_implies_operator_zero",
        "finite_transport_theorems_construct_residual_package_v0",
        "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0",
        "supplied_interface_alignment_semantics_construct_bridge_package_v0",
        "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0",
    ]
    for theorem in required_theorems:
        assert theorem in audit_text, f"Lean dependency audit missing theorem row: {theorem}"
        assert theorem in index_text, f"Lean release index missing theorem check: {theorem}"


def test_public_nonclaim_boundaries_are_stable() -> None:
    all_text = "\n".join(
        _read(path)
        for path in (
            RELEASE_DIR / "TOE_V01_ALPHA_RELEASE_STANDARD_v0.md",
            RELEASE_DIR / "TOE_V01_ALPHA_PILLAR_SEAM_COVERAGE_LEDGER_v0.md",
            LEAN_AUDIT_MD,
        )
    )
    for nonclaim in (
        "master-action promotion",
        "pillar completion",
        "seam closure",
        "Phase 2",
        "empirical adequacy",
        "canonical ToE",
        "QFT-GR source-map closure",
    ):
        assert nonclaim in all_text, f"Missing stable nonclaim phrase: {nonclaim}"
