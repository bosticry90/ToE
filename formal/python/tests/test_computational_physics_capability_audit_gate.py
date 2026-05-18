from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.computational_physics_capability_audit_report import (
    ALLOWED_ROLES,
    AUDIT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    build_audit_payload,
)


REPO_ROOT = find_repo_root(Path(__file__))
JSON_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
MD_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_REPORT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INTEGRATION_ROADMAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
)
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "computational_physics_capability_audit_report.py"

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
    "artifact_path",
    "computational_physics_role",
    "physics_domain",
    "claim_boundary",
    "verification_status",
    "validation_status",
    "uq_status",
    "robustness_status",
    "known_limit_status",
    "falsifier_status",
    "promotion_allowed",
    "evidence_paths",
    "notes",
]

REQUIRED_CATEGORIES = [
    "simulation",
    "verification",
    "validation_relevant",
    "uq_relevant",
    "robustness",
    "regime_recovery",
    "falsifier",
    "model_comparison",
    "governance_only",
]

PROHIBITED_PHRASES = [
    "proves the ToE",
    "confirms the ToE",
    "Phase 2 authorized",
    "seam closure authorized",
    "empirical validation complete",
    "master action promoted",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _payload() -> dict:
    return json.loads(_read(JSON_PATH))


def test_capability_audit_files_exist() -> None:
    assert JSON_PATH.exists()
    assert MD_PATH.exists()
    assert TOOL_PATH.exists()


def test_capability_audit_payload_schema_and_authority_binding() -> None:
    payload = _payload()

    assert payload["schema_id"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0"
    assert payload["audit_id"] == AUDIT_ID
    assert payload["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert payload["roadmap_pointer"] == "formal/docs/paper/COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
    assert payload["classification_outcome"] == (
        "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_CLASSIFIES_EXISTING_NONCLAIM_ANALYSIS_SURFACES_WITHOUT_PROMOTION"
    )
    assert payload["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert payload["scope"]["scope_rule"] == "BOUNDED_MAJOR_EXISTING_COMPUTATIONAL_LANES_ONLY"
    assert "ARCHIVE_AND_QUARANTINE_PATHS" in payload["scope"]["excluded_scope"]


def test_capability_audit_has_exact_bounded_scope_rows() -> None:
    payload = _payload()
    rows = payload["audit_rows"]
    assert [row["artifact_id"] for row in rows] == EXPECTED_ROWS
    assert payload["summary"]["row_count"] == len(EXPECTED_ROWS)


def test_capability_audit_rows_have_required_fields_and_categories() -> None:
    payload = _payload()
    roles_present: set[str] = set()
    for row in payload["audit_rows"]:
        for field in REQUIRED_ROW_FIELDS:
            assert field in row, f"Missing field {field} in {row.get('artifact_id')}"
        assert row["computational_physics_role"], f"Missing roles for {row['artifact_id']}"
        for role in row["computational_physics_role"]:
            assert role in ALLOWED_ROLES
            roles_present.add(role)
        assert row["evidence_paths"], f"Missing evidence paths for {row['artifact_id']}"
        for evidence in row["evidence_paths"]:
            assert evidence["exists"] is True, f"Missing evidence path: {evidence['path']}"

    for category in REQUIRED_CATEGORIES:
        assert category in roles_present, f"Missing classification category: {category}"


def test_capability_audit_forbids_promotion_and_archive_quarantine_paths() -> None:
    payload = _payload()
    assert payload["summary"]["promotion_allowed_count"] == 0
    assert payload["summary"]["all_promotion_allowed_false"] is True
    assert payload["summary"]["missing_evidence_count"] == 0

    for row in payload["audit_rows"]:
        assert row["promotion_allowed"] is False
        for evidence in row["evidence_paths"]:
            path = evidence["path"]
            assert not path.startswith("archive/")
            assert not path.startswith("quarantine/")
            assert "/quarantine/" not in path


def test_capability_audit_report_is_deterministic() -> None:
    generated_1 = build_audit_payload(captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    generated_2 = build_audit_payload(captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    assert generated_1 == generated_2
    assert _payload() == generated_1


def test_capability_audit_markdown_report_has_nonclaim_boundary() -> None:
    text = _read(MD_PATH)
    assert "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_REPORT_v0" in text
    assert "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json" in text
    assert "no theorem discharge" in text
    assert "It does not say that those artifacts validate the ToE." in text
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in text


def test_capability_audit_is_pinned_to_roadmaps() -> None:
    physics_text = _read(ROADMAP_PATH)
    integration_text = _read(INTEGRATION_ROADMAP_PATH)
    required_refs = [
        "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
        "formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json",
        "formal/docs/paper/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_REPORT_v0.md",
        "formal/python/tools/computational_physics_capability_audit_report.py",
        "formal/python/tests/test_computational_physics_capability_audit_gate.py",
    ]
    for ref in required_refs:
        assert ref in physics_text, f"Missing PHYSICS_ROADMAP ref: {ref}"

    assert "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_STATUS_v0: IMPLEMENTED_BOUNDED_NONCLAIM" in integration_text
