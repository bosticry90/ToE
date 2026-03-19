from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]

DOC = (
    ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_33_DRYRUN_NONFLIP_BOUNDARY_CUSTODY_EXECUTION_CONTINUITY_RECERTIFICATION_AUDIT_v0.md"
)

ARTIFACT = (
    ROOT
    / "formal"
    / "output"
    / "cosmo_bg_micro33_dryrun_nonflip_boundary_custody_execution_continuity_recertification_audit_cycle01_v0.json"
)


def test_cycle33_doc_tokens_present() -> None:
    text = DOC.read_text(encoding="utf-8")
    assert "COSMO_BG_MICRO33_DRYRUN_NONFLIP_BOUNDARY_CUSTODY_EXECUTION_CONTINUITY_RECERTIFICATION_AUDIT_ADJUDICATION: NOT_YET_DISCHARGED" in text
    assert "COSMO_BG_MICRO33_SCOPE_BOUNDARY_v0: DRYRUN_NONFLIP_BOUNDARY_CUSTODY_EXECUTION_CONTINUITY_RECERTIFICATION_AUDIT_ONLY_NONCLAIM" in text
    assert "COSMO_BG_MICRO33_PROGRESS_v0: DRYRUN_NONFLIP_BOUNDARY_CUSTODY_EXECUTION_CONTINUITY_RECERTIFICATION_AUDIT_TOKEN_PINNED" in text
    assert "dryrun_nonflip_boundary_custody_execution_continuity_recertification_audit_policy" in text
    assert "no comparator-lane authorization." in text


def test_cycle33_artifact_payload_consistency() -> None:
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert payload["pillar"] == "PILLAR-COSMO"
    assert payload["cycle"] == "Cycle-033"
    assert payload["classification"] == "P-POLICY"
    assert payload["status"] == "LOCKED"
    assert payload["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert payload["scope_boundary"]["value"] == "DRYRUN_NONFLIP_BOUNDARY_CUSTODY_EXECUTION_CONTINUITY_RECERTIFICATION_AUDIT_ONLY_NONCLAIM"
    assert payload["progress"]["value"] == "DRYRUN_NONFLIP_BOUNDARY_CUSTODY_EXECUTION_CONTINUITY_RECERTIFICATION_AUDIT_TOKEN_PINNED"
    assert payload["policy_tokens"]["dryrun_nonflip_boundary_custody_execution_continuity_recertification_audit_policy"] == (
        "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_26_27_28_29_30_31_32_DRYRUN_NONFLIP_BOUNDARY_CUSTODY_EXECUTION_CONTINUITY_RECERTIFICATION_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION"
    )


def test_cycle33_forbidden_prefixes_absent() -> None:
    text = DOC.read_text(encoding="utf-8") + "\n" + ARTIFACT.read_text(encoding="utf-8")
    assert "ADJUDICATION_FLIP_GRANTED" not in text
    assert "COMPARATOR_LANE_AUTHORIZATION_GRANTED" not in text