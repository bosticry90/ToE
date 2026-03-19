from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]

DOC = (
    ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_83_DRYRUN_NONFLIP_CUSTODY_BOUNDARY_EXECUTION_RECERTIFICATION_CONTINUITY_AUDIT_v0.md"
)

ARTIFACT = (
    ROOT
    / "formal"
    / "output"
    / "cosmo_bg_micro83_dryrun_nonflip_custody_boundary_execution_recertification_continuity_audit_cycle01_v0.json"
)


def test_cycle83_doc_tokens_present() -> None:
    text = DOC.read_text(encoding="utf-8")
    assert "COSMO_BG_MICRO83_DRYRUN_NONFLIP_CUSTODY_BOUNDARY_EXECUTION_RECERTIFICATION_CONTINUITY_AUDIT_ADJUDICATION: NOT_YET_DISCHARGED" in text
    assert "COSMO_BG_MICRO83_SCOPE_BOUNDARY_v0: DRYRUN_NONFLIP_CUSTODY_BOUNDARY_EXECUTION_RECERTIFICATION_CONTINUITY_AUDIT_ONLY_NONCLAIM" in text
    assert "COSMO_BG_MICRO83_PROGRESS_v0: DRYRUN_NONFLIP_CUSTODY_BOUNDARY_EXECUTION_RECERTIFICATION_CONTINUITY_AUDIT_TOKEN_PINNED" in text
    assert "dryrun_nonflip_custody_boundary_execution_recertification_continuity_audit_policy" in text
    assert "no comparator-lane authorization." in text


def test_cycle83_artifact_payload_consistency() -> None:
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert payload["pillar"] == "PILLAR-COSMO"
    assert payload["cycle"] == "Cycle-083"
    assert payload["classification"] == "P-POLICY"
    assert payload["status"] == "LOCKED"
    assert payload["adjudication"]["value"] == "NOT_YET_DISCHARGED"
    assert payload["scope_boundary"]["value"] == "DRYRUN_NONFLIP_CUSTODY_BOUNDARY_EXECUTION_RECERTIFICATION_CONTINUITY_AUDIT_ONLY_NONCLAIM"
    assert payload["progress"]["value"] == "DRYRUN_NONFLIP_CUSTODY_BOUNDARY_EXECUTION_RECERTIFICATION_CONTINUITY_AUDIT_TOKEN_PINNED"
    assert payload["policy_tokens"]["dryrun_nonflip_custody_boundary_execution_recertification_continuity_audit_policy"] == (
        "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_26_27_28_29_30_31_32_33_34_35_36_37_38_39_40_41_42_43_44_45_46_47_48_49_50_51_52_53_54_55_56_57_58_59_60_61_62_63_64_65_66_67_68_69_70_71_72_73_74_75_76_77_78_79_80_81_82_DRYRUN_NONFLIP_CUSTODY_BOUNDARY_EXECUTION_RECERTIFICATION_CONTINUITY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION"
    )


def test_cycle83_forbidden_prefixes_absent() -> None:
    text = DOC.read_text(encoding="utf-8") + "\n" + ARTIFACT.read_text(encoding="utf-8")
    assert "ADJUDICATION_FLIP_GRANTED" not in text
    assert "COMPARATOR_LANE_AUTHORIZATION_GRANTED" not in text
