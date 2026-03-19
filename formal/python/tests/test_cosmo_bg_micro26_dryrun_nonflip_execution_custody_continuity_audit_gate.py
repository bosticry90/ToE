from __future__ import annotations

import json
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
COSMO_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
COSMO_MICRO26_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_26_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_v0.md"
COSMO_MICRO26_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_cycle01_v0.json"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROLLUP_GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_cosmo_matrix_rollup_crosspin_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cosmo_micro26_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
    assert COSMO_MICRO26_PATH.exists(), "Missing COSMO background Cycle-026 micro document."
    assert COSMO_MICRO26_ARTIFACT_PATH.exists(), "Missing COSMO background Cycle-026 artifact payload."


def test_cosmo_target_references_micro26_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "TARGET-COSMO-BG-MICRO-26-DRYRUN-NONFLIP-EXECUTION-CUSTODY-CONTINUITY-AUDIT-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_26_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_v0.md",
        "formal/output/cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO parent target is missing required micro-26 token(s): " + ", ".join(missing)


def test_cosmo_micro26_doc_contains_required_headers_and_tokens() -> None:
    text = _read(COSMO_MICRO26_PATH)
    required_headers = [
        "Spec ID:",
        "Target ID:",
        "Classification:",
        "Purpose:",
        "Adjudication token:",
        "Scope-boundary token:",
        "Progress token:",
        "Artifact token:",
    ]
    missing_headers = [header for header in required_headers if header not in text]
    assert not missing_headers, "COSMO micro-26 document is missing required header(s): " + ", ".join(missing_headers)

    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_26_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_v0",
        "TARGET-COSMO-BG-MICRO-26-DRYRUN-NONFLIP-EXECUTION-CUSTODY-CONTINUITY-AUDIT-v0",
        "COSMO_BG_MICRO26_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO26_SCOPE_BOUNDARY_v0: DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_ONLY_NONCLAIM",
        "COSMO_BG_MICRO26_PROGRESS_v0: DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_TOKEN_PINNED",
        "COSMO_BG_MICRO26_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_ARTIFACT_v0: cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_cycle01_v0",
        "COSMO_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
        "dryrun_nonflip_execution_custody_continuity_audit_policy: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
        "dryrun_nonflip_execution_custody_continuity_audit_gate: formal/python/tests/test_cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_gate.py",
    ]
    missing_tokens = [token for token in required_tokens if token not in text]
    assert not missing_tokens, "COSMO micro-26 document is missing required token(s): " + ", ".join(missing_tokens)


def test_cosmo_micro26_artifact_schema_and_scope_boundary() -> None:
    payload = _read_json(COSMO_MICRO26_ARTIFACT_PATH)

    assert payload.get("artifact_id") == "cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_cycle01_v0"
    assert payload.get("artifact_version") == "v0"
    assert payload.get("cycle") == "CYCLE-026"

    sha = payload.get("sha256")
    assert isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha) is not None

    body = payload.get("payload")
    assert isinstance(body, dict)
    assert body.get("status") == "placeholder_non_promotional"
    scope = body.get("scope")
    assert isinstance(scope, str)
    assert "dryrun" in scope and "nonflip" in scope and "nonclaim" in scope

    boundary_statement = body.get("boundary_statement")
    assert boundary_statement == "DRYRUN_NONFLIP_LANE_ONLY_EXECUTION_CUSTODY_CONTINUITY_NO_ADJUDICATION_FLIP_NO_COMPARATOR_AUTHORIZATION"


def test_cosmo_micro26_forbidden_tokens_not_present() -> None:
    doc_text = _read(COSMO_MICRO26_PATH)
    artifact_text = _read(COSMO_MICRO26_ARTIFACT_PATH)
    forbidden_tokens = [
        "COMPARATOR_LANE_AUTHORIZATION_GRANTED",
        "COMPARATOR_AUTHORIZATION_GRANTED",
        "ADJUDICATION_FLIP_GRANTED",
    ]
    for token in forbidden_tokens:
        assert token not in doc_text
        assert token not in artifact_text


def test_cosmo_micro26_cross_surface_pointers_are_complete() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO")
    assert isinstance(cosmo, dict), "PILLAR-COSMO matrix row must exist."

    assert cosmo.get("dryrun_nonflip_execution_custody_continuity_audit_doc") == "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_26_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_v0.md"
    assert cosmo.get("dryrun_nonflip_execution_custody_continuity_audit_gate") == "formal/python/tests/test_cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_gate.py"
    assert cosmo.get("dryrun_nonflip_execution_custody_continuity_audit_policy") == "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION"

    state_text = _read(STATE_PATH)
    required_state_tokens = [
        "COSMO_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
        "formal/python/tests/test_cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_gate.py",
    ]
    missing_state = [token for token in required_state_tokens if token not in state_text]
    assert not missing_state, "State missing dryrun nonflip execution custody continuity audit token(s): " + ", ".join(missing_state)

    target_text = _read(COSMO_TARGET_PATH)
    required_target_tokens = [
        "TARGET-COSMO-BG-MICRO-26-DRYRUN-NONFLIP-EXECUTION-CUSTODY-CONTINUITY-AUDIT-v0",
        "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_26_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_v0.md",
        "formal/output/cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_cycle01_v0.json",
        "formal/python/tests/test_cosmo_bg_micro26_dryrun_nonflip_execution_custody_continuity_audit_gate.py",
    ]
    missing_target = [token for token in required_target_tokens if token not in target_text]
    assert not missing_target, "COSMO target missing dryrun nonflip execution custody continuity audit token(s): " + ", ".join(missing_target)

    rollup_gate_text = _read(ROLLUP_GATE_PATH)
    required_rollup_tokens = [
        "dryrun_nonflip_execution_custody_continuity_audit_doc",
        "dryrun_nonflip_execution_custody_continuity_audit_gate",
        "dryrun_nonflip_execution_custody_continuity_audit_policy",
        "COSMO_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_POLICY_v0",
    ]
    missing_rollup = [token for token in required_rollup_tokens if token not in rollup_gate_text]
    assert not missing_rollup, "Rollup gate missing dryrun nonflip execution custody continuity cross-pin token(s): " + ", ".join(missing_rollup)
