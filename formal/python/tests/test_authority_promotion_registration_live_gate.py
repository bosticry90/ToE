from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "coupling_refinement_ruling_20260411_v0.json"
)
PROMOTION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json"
)
AUTHORITY_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "output" / "authority" / "authoritative_blocker_definitions.json"
)
LINEAGE_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "output" / "authority" / "blocker_definition_lineage.json"
)
QM_RECOMPUTE_PATH = (
    REPO_ROOT / "formal" / "output" / "recompute" / "qm_seam_coherence_under_revised_blocker.json"
)
LEDGER_RECOMPUTE_PATH = (
    REPO_ROOT / "formal" / "output" / "recompute" / "ledger_artifact_transport_under_revised_blocker.json"
)
TRANSPORT_RECOMPUTE_PATH = (
    REPO_ROOT / "formal" / "output" / "recompute" / "blocker_authority_transport_surface.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

PROMOTION_REFS = (
    "formal/docs/release/AUTHORITY_PROMOTION_REGISTRATION_20260411_v0.json",
    "formal/output/reports/authority_promotion_registration_20260411_v0.json",
    "formal/python/tests/test_authority_promotion_registration_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _matching_entry(entries: list[dict], predicate) -> dict:
    matches = [entry for entry in entries if predicate(entry)]
    assert matches, "Expected matching live authority-promotion artifact."
    return matches[-1]


def test_authority_promotion_registration_live_route_is_consistent() -> None:
    ruling_report = _read_json(RULING_REPORT_PATH)
    promotion_report = _read_json(PROMOTION_REPORT_PATH)
    authority_registry = _read_json(AUTHORITY_REGISTRY_PATH)
    lineage_registry = _read_json(LINEAGE_REGISTRY_PATH)
    qm_recompute = _read_json(QM_RECOMPUTE_PATH)
    ledger_recompute = _read_json(LEDGER_RECOMPUTE_PATH)
    transport_recompute = _read_json(TRANSPORT_RECOMPUTE_PATH)

    ruling = ruling_report.get("ruling", {})
    prereq = promotion_report.get("prerequisite", {})
    registration = promotion_report.get("promotion_registration", {})
    summary = promotion_report.get("summary", {})
    supersession = promotion_report.get("supersession_relationship", {})
    recompute = promotion_report.get("recompute_triggers", {})

    assert ruling.get("ruling_id") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION"
    assert ruling.get("promotion_gate_opens") is True
    assert ruling.get("next_action") == "PROMOTE_REVISED_BLOCKER_DEFINITION_TO_AUTHORITATIVE"

    assert prereq.get("prerequisite_satisfied") is True
    assert prereq.get("ruling_id") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION"
    assert prereq.get("promotion_gate_opens") is True

    registration_entry = registration.get("registration_entry", {})
    assert registration.get("revised_definition_id") == "REVISED_BLOCKER_DEFINITION_20260411_v0"
    assert registration.get("registered_as") == "AUTHORITATIVE_BLOCKER_DEFINITION"
    assert registration_entry.get("promotion_ruling") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION"
    assert registration_entry.get("coupling_state") == "TIGHTENED"
    assert registration_entry.get("target_row_id") == "ROW-SEAM-QM-STAT-001"
    assert registration_entry.get("criteria_met") == "5/5"
    assert registration_entry.get("status") == "ACTIVE"

    authoritative_entry = _matching_entry(
        authority_registry.get("entries", []),
        lambda entry: entry.get("definition_id") == "REVISED_BLOCKER_DEFINITION_20260411_v0"
        and entry.get("promotion_ruling") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
    )
    assert authoritative_entry.get("authority_category") == "AUTHORITATIVE_BLOCKER_DEFINITION"
    assert authoritative_entry.get("coupling_state") == "TIGHTENED"
    assert authoritative_entry.get("target_row_id") == "ROW-SEAM-QM-STAT-001"

    lineage_entry = supersession.get("lineage_entry", {})
    assert supersession.get("prior_authoritative_token") == "PRIOR_AUTHORITATIVE_BLOCKER_DEFINITION"
    assert supersession.get("new_authoritative_token") == "REVISED_BLOCKER_DEFINITION_20260411_v0"
    assert lineage_entry.get("supersession_justified_by") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION"
    assert lineage_entry.get("coupling_evidence", {}).get("coupling_state") == "TIGHTENED"

    matching_lineage = _matching_entry(
        lineage_registry.get("entries", []),
        lambda entry: entry.get("new_authoritative_token") == "REVISED_BLOCKER_DEFINITION_20260411_v0"
        and entry.get("supersession_justified_by") == "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
    )
    assert matching_lineage.get("prior_authoritative_token") == "PRIOR_AUTHORITATIVE_BLOCKER_DEFINITION"

    assert recompute.get("surfaces_triggered") == 3
    triggered_surfaces = recompute.get("triggered_surfaces", [])
    assert len(triggered_surfaces) == 3

    recompute_docs = {
        "qm_seam_coherence_under_revised_blocker": qm_recompute,
        "ledger_artifact_transport_under_revised_blocker": ledger_recompute,
        "blocker_authority_transport_surface": transport_recompute,
    }
    for surface_name, doc in recompute_docs.items():
        trigger = _matching_entry(
            doc.get("triggers", []),
            lambda entry: entry.get("surface_name") == surface_name
            and entry.get("triggered_by") == "AUTHORITY_PROMOTION_REGISTRATION_20260411_v0",
        )
        assert trigger.get("revised_blocker_definition") == "REVISED_BLOCKER_DEFINITION_20260411_v0"
        assert trigger.get("status") == "PENDING_RECOMPUTE"

    assert summary.get("registration_completed") is True
    assert summary.get("revised_definition_is_now_authoritative") is True
    assert summary.get("supersession_recorded") is True
    assert summary.get("recompute_surfaces_triggered") == 3
    assert summary.get("next_action") == "MONITOR_RECOMPUTE_SURFACES"


def test_authority_promotion_registration_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in PROMOTION_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )