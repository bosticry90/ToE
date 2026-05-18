from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.vvuq_credibility_ledger_report import (
    DEFAULT_CAPTURED_AT_UTC,
    LEDGER_ID,
    PREPARATION_RESULT,
    build_ledger,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0.json"
)
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "VVUQ_CREDIBILITY_LEDGER_REPORT_v0.md"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "vvuq_credibility_ledger_report.py"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


EXPECTED_ROWS = [
    "C6_CP_NLSE_2D_LANE",
    "C7_MT01A_ACOUSTIC_METRIC_LANE",
    "UCFF_SPECTRAL_AUDIT_LINEAGE",
    "BRAGG_DISPERSION_ELIMINATIVE_LANE",
    "RL01_RELATIVISTIC_DISPERSION_LIMIT",
    "RL02_NONRELATIVISTIC_NLSE_LIMIT",
    "GR01_DERIVATION_COMPLETENESS_GATE",
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS",
]

REQUIRED_ROW_FIELDS = [
    "artifact_id",
    "source_audit_id",
    "model_family",
    "verification_status",
    "validation_status",
    "input_pedigree",
    "results_uncertainty",
    "results_robustness",
    "use_history",
    "management_status",
    "claim_status",
    "claim_ceiling",
    "credibility_readout",
    "upgrade_requirements",
    "promotion_allowed",
]

PROHIBITED_PHRASES = [
    "Phase 2 authorized",
    "seam closure authorized",
    "empirical validation complete",
    "theorem discharged by computation",
    "master action promoted",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_vvuq_credibility_ledger_files_exist() -> None:
    assert LEDGER_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()


def test_vvuq_credibility_ledger_top_level_contract() -> None:
    ledger = _json(LEDGER_PATH)
    assert ledger["schema_id"] == "VVUQ_CREDIBILITY_LEDGER_20260515_v0"
    assert ledger["ledger_id"] == LEDGER_ID
    assert ledger["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert ledger["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert ledger["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert ledger["preparation_result"] == PREPARATION_RESULT
    assert ledger["consumes_result_review"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_v0"
    assert ledger["source_audit"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
    assert ledger["source_audit_row_count"] == 8
    assert ledger["primary_gap_pattern"] == "UQ_DEPTH_AND_VALIDATION_DEPTH_ARE_PRIMARY_NEXT_CREDIBILITY_GAPS"
    assert ledger["scoring_policy"] == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0"


def test_vvuq_credibility_ledger_rows_match_audit_exactly_without_promotion() -> None:
    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    assert [row["artifact_id"] for row in ledger["ledger_rows"]] == EXPECTED_ROWS
    assert [row["artifact_id"] for row in audit["audit_rows"]] == EXPECTED_ROWS
    assert ledger["promotion_allowed_count"] == 0
    assert ledger["all_promotion_allowed_false"] is True
    for row in ledger["ledger_rows"]:
        assert row["promotion_allowed"] is False
        assert "credibility_score" not in row
    assert "credibility_score" not in json.dumps(ledger, sort_keys=True)


def test_vvuq_credibility_ledger_rows_have_required_credibility_fields() -> None:
    ledger = _json(LEDGER_PATH)
    for row in ledger["ledger_rows"]:
        for field in REQUIRED_ROW_FIELDS:
            assert field in row, f"Missing field {field} in {row.get('artifact_id')}"
        assert row["source_audit_id"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
        assert isinstance(row["upgrade_requirements"], list) and row["upgrade_requirements"]
        assert row["management_status"] == "roadmap_pinned_gated"
        assert row["claim_ceiling"] in {
            "nonclaim_computational_support_only",
            "internal_consequence_only",
            "known_limit_relevance_only",
            "validation_candidate_only",
            "blocked_no_upgrade",
        }


def test_vvuq_credibility_ledger_does_not_upgrade_validation_beyond_source_audit() -> None:
    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    audit_by_id = {row["artifact_id"]: row for row in audit["audit_rows"]}
    for row in ledger["ledger_rows"]:
        source = audit_by_id[row["artifact_id"]]
        assert row["validation_status"] == source["validation_status"]
        assert row["verification_status"] == source["verification_status"]
        assert row["results_robustness"] == source["robustness_status"]
        assert row["claim_status"] == source["claim_boundary"]


def test_vvuq_credibility_ledger_is_deterministic() -> None:
    generated_1 = build_ledger(
        audit_path=AUDIT_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_ledger(
        audit_path=AUDIT_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(LEDGER_PATH) == generated_1


def test_vvuq_credibility_ledger_report_and_roadmaps_preserve_nonclaim_boundary() -> None:
    combined = "\n".join([_read(REPORT_PATH), _read(ROADMAP_PATH), _read(PHYSICS_ROADMAP_PATH)])
    assert "Credibility bookkeeping only" in combined
    assert PREPARATION_RESULT in combined
    assert "VVUQ_CREDIBILITY_LEDGER_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in combined
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in combined
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_vvuq_credibility_ledger_is_pinned_in_both_roadmaps() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)
    for ref in (
        "VVUQ_CREDIBILITY_LEDGER_v0",
        "formal/docs/release/VVUQ_CREDIBILITY_LEDGER_20260515_v0.json",
        "formal/docs/paper/VVUQ_CREDIBILITY_LEDGER_REPORT_v0.md",
        "formal/python/tools/vvuq_credibility_ledger_report.py",
        "formal/python/tests/test_vvuq_credibility_ledger_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
