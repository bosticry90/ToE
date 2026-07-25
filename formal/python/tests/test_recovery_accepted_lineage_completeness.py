from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[3]
TOOL = ROOT / "formal" / "python" / "tools" / "recovery_accepted_lineage_completeness.py"
SPEC = importlib.util.spec_from_file_location("recovery_accepted_lineage_completeness", TOOL)
assert SPEC and SPEC.loader
subject = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(subject)


@pytest.fixture(scope="module")
def manifest() -> dict:
    return subject.build_manifest()


def test_proposed_recovery_base_has_complete_linear_accepted_lineage(
    manifest: dict,
) -> None:
    assert manifest["status"] == "RECOVERY_BASE_ACCEPTED_LINEAGE_COMPLETE"
    assert manifest["lineage"]["linear"] is True
    assert manifest["lineage"]["commit_count"] == 80
    assert manifest["external_or_sibling_accepted_commits"] == []
    identity = manifest["proposed_base_identity"]
    assert identity["commit"] == "91f7d3c3c0b1ed0814a95962c2397fd1e9196e85"
    assert identity["tree"] == "a04c1c6dda56b25d3b4308841cf71ea3edf642eb"
    for key in (
        "accepted_result_manifest_root",
        "accepted_review_manifest_root",
        "protected_invariant_manifest_root",
    ):
        assert len(identity[key]) == 64


def test_every_accepted_repair_binds_result_review_and_current_guard(
    manifest: dict,
) -> None:
    assert len(manifest["accepted_repairs"]) == 8
    for cycle in manifest["accepted_repairs"]:
        assert cycle["current_enforcing_guards"]
        assert len(cycle["result"]["sha256"]) == 64
        assert len(cycle["review"]["sha256"]) == 64
        assert cycle["protected_invariant"]


def test_guard_classes_are_explicit_and_supersession_has_evidence(
    manifest: dict,
) -> None:
    classes = {
        guard["class"]
        for cycle in manifest["accepted_repairs"]
        for field in (
            "current_enforcing_guards",
            "historical_snapshot_guards",
            "superseded_guards",
        )
        for guard in cycle[field]
    }
    assert "PROTECTED_INVARIANT_GUARD" in classes
    assert "HISTORICAL_SNAPSHOT_GUARD" in classes
    assert "SUPERSEDED_GUARD_WITH_ACCEPTED_REPLACEMENT" in classes
    for cycle in manifest["accepted_repairs"]:
        for guard in cycle["superseded_guards"]:
            assert guard["accepted_supersession_evidence"]
            assert guard["replacement"]


def test_tampered_expected_implementation_tree_fails_closed(tmp_path: Path) -> None:
    contract = copy.deepcopy(subject.load_contract())
    contract["accepted_repairs"][0]["implementation_commits"][0]["tree"] = "0" * 40
    path = tmp_path / "tampered-contract.json"
    path.write_text(json.dumps(contract), encoding="utf-8")
    with pytest.raises(subject.LineageError, match="tree mismatch"):
        subject.build_manifest(contract_path=path)


def test_unknown_accepted_commit_outside_base_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = subject._git

    def fake_git(*args: str, **kwargs: object) -> str:
        if "--not" in args and "--grep=^Accept" in args:
            return "0" * 40 + "\x1fAccept orphaned repair"
        return original(*args, **kwargs)

    monkeypatch.setattr(subject, "_git", fake_git)
    with pytest.raises(subject.LineageError, match="outside the proposed base"):
        subject.build_manifest()
