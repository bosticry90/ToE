from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class CosmoNonflipGateSpec:
    micro_id: str
    micro_doc_relative_path: str
    artifact_relative_path: str
    gate_relative_path: str
    target_required_tokens: tuple[str, ...]
    doc_required_tokens: tuple[str, ...]
    expected_artifact_id: str
    expected_cycle: str
    expected_boundary_statement: str
    matrix_doc_key: str
    matrix_gate_key: str
    matrix_policy_key: str
    matrix_policy_value: str
    state_required_tokens: tuple[str, ...]
    rollup_required_tokens: tuple[str, ...]


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROLLUP_GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_cosmo_matrix_rollup_crosspin_gate.py"
_REQUIRED_HEADERS = (
    "Spec ID:",
    "Target ID:",
    "Classification:",
    "Purpose:",
    "Adjudication token:",
    "Scope-boundary token:",
    "Progress token:",
    "Artifact token:",
)
_FORBIDDEN_TOKENS = (
    "COMPARATOR_LANE_AUTHORIZATION_GRANTED",
    "COMPARATOR_AUTHORIZATION_GRANTED",
    "ADJUDICATION_FLIP_GRANTED",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _assert_tokens_present(text: str, tokens: tuple[str, ...], error_prefix: str) -> None:
    missing = [token for token in tokens if token not in text]
    assert not missing, f"{error_prefix}: " + ", ".join(missing)


def _assign_test(module_globals: dict[str, object], test_name: str, test_callable: object) -> None:
    test_callable.__name__ = test_name
    module_globals[test_name] = test_callable


def register_cosmo_nonflip_gate_suite(module_globals: dict[str, object], spec: CosmoNonflipGateSpec) -> None:
    micro_doc_path = REPO_ROOT.joinpath(*spec.micro_doc_relative_path.split("/"))
    micro_artifact_path = REPO_ROOT.joinpath(*spec.artifact_relative_path.split("/"))

    def _test_artifacts_exist() -> None:
        assert COSMO_TARGET_PATH.exists(), "Missing COSMO background target document."
        assert micro_doc_path.exists(), f"Missing COSMO background Cycle-{spec.micro_id} micro document."
        assert micro_artifact_path.exists(), f"Missing COSMO background Cycle-{spec.micro_id} artifact payload."

    def _test_target_references_micro_and_gate() -> None:
        text = _read(COSMO_TARGET_PATH)
        _assert_tokens_present(
            text,
            spec.target_required_tokens,
            f"COSMO parent target is missing required micro-{spec.micro_id} token(s)",
        )

    def _test_doc_contains_required_headers_and_tokens() -> None:
        text = _read(micro_doc_path)
        missing_headers = [header for header in _REQUIRED_HEADERS if header not in text]
        assert not missing_headers, (
            f"COSMO micro-{spec.micro_id} document is missing required header(s): " + ", ".join(missing_headers)
        )
        _assert_tokens_present(
            text,
            spec.doc_required_tokens,
            f"COSMO micro-{spec.micro_id} document is missing required token(s)",
        )

    def _test_artifact_schema_and_scope_boundary() -> None:
        payload = _read_json(micro_artifact_path)
        assert payload.get("artifact_id") == spec.expected_artifact_id
        assert payload.get("artifact_version") == "v0"
        assert payload.get("cycle") == spec.expected_cycle

        sha = payload.get("sha256")
        assert isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha) is not None

        body = payload.get("payload")
        assert isinstance(body, dict)
        assert body.get("status") == "placeholder_non_promotional"
        scope = body.get("scope")
        assert isinstance(scope, str)
        assert "dryrun" in scope and "nonflip" in scope and "nonclaim" in scope
        assert body.get("boundary_statement") == spec.expected_boundary_statement

    def _test_forbidden_tokens_not_present() -> None:
        doc_text = _read(micro_doc_path)
        artifact_text = _read(micro_artifact_path)
        for token in _FORBIDDEN_TOKENS:
            assert token not in doc_text
            assert token not in artifact_text

    def _test_cross_surface_pointers_are_complete() -> None:
        matrix = _read_json(MATRIX_PATH)
        cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO")
        assert isinstance(cosmo, dict), "PILLAR-COSMO matrix row must exist."
        assert cosmo.get(spec.matrix_doc_key) == spec.micro_doc_relative_path
        assert cosmo.get(spec.matrix_gate_key) == spec.gate_relative_path
        assert cosmo.get(spec.matrix_policy_key) == spec.matrix_policy_value

        state_text = _read(STATE_PATH)
        _assert_tokens_present(
            state_text,
            spec.state_required_tokens,
            f"State missing dryrun nonflip micro-{spec.micro_id} token(s)",
        )

        target_text = _read(COSMO_TARGET_PATH)
        _assert_tokens_present(
            target_text,
            spec.target_required_tokens,
            f"COSMO target missing dryrun nonflip micro-{spec.micro_id} token(s)",
        )

        rollup_gate_text = _read(ROLLUP_GATE_PATH)
        _assert_tokens_present(
            rollup_gate_text,
            spec.rollup_required_tokens,
            f"Rollup gate missing dryrun nonflip micro-{spec.micro_id} cross-pin token(s)",
        )

    _assign_test(module_globals, f"test_cosmo_micro{spec.micro_id}_artifacts_exist", _test_artifacts_exist)
    _assign_test(module_globals, f"test_cosmo_micro{spec.micro_id}_target_references_micro_and_gate", _test_target_references_micro_and_gate)
    _assign_test(module_globals, f"test_cosmo_micro{spec.micro_id}_doc_contains_required_headers_and_tokens", _test_doc_contains_required_headers_and_tokens)
    _assign_test(module_globals, f"test_cosmo_micro{spec.micro_id}_artifact_schema_and_scope_boundary", _test_artifact_schema_and_scope_boundary)
    _assign_test(module_globals, f"test_cosmo_micro{spec.micro_id}_forbidden_tokens_not_present", _test_forbidden_tokens_not_present)
    _assign_test(module_globals, f"test_cosmo_micro{spec.micro_id}_cross_surface_pointers_are_complete", _test_cross_surface_pointers_are_complete)
