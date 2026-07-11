from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.generate_lean_all_modules_aggregate import tracked_module_names


REPO_ROOT = find_repo_root(Path(__file__))
AUTHORITY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
CURRENT_SURFACES = [
    REPO_ROOT / "README.md",
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md",
    AUTHORITY_PATH,
]


def test_current_authority_has_no_bom_mojibake_prefix() -> None:
    raw = AUTHORITY_PATH.read_bytes()
    assert not raw.startswith(b"\xef\xbb\xbf")
    assert not raw.startswith("ï»¿".encode("utf-8"))
    assert raw.startswith(b"# Current Authoritative Surfaces v0")


def test_historical_target_prose_is_explicitly_historical() -> None:
    stale = "The current target is `prepare_pillar_seam_unit_mapping_ledger_guardrail_packet`"
    historical = (
        "At that review boundary, the selected next target was "
        "`prepare_pillar_seam_unit_mapping_ledger_guardrail_packet`"
    )
    for path in CURRENT_SURFACES:
        text = path.read_text(encoding="utf-8")
        assert stale not in text
    assert historical in AUTHORITY_PATH.read_text(encoding="utf-8")


def test_tracked_lean_sources_do_not_contain_rtf_markers() -> None:
    lean_root = REPO_ROOT / "formal" / "toe_formal"
    malformed = [
        lean_root / Path(*module.split(".")).with_suffix(".lean")
        for module in tracked_module_names()
        if (
            lean_root / Path(*module.split(".")).with_suffix(".lean")
        ).read_bytes().lstrip().startswith(b"{\\rtf")
    ]
    assert malformed == []


def test_current_canonical_json_surfaces_parse_strictly() -> None:
    paths = [
        REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json",
        REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / "SCALAR_ROUTE_SUBMISSION_CHECKPOINT_REFERENTIAL_INTEGRITY_CORRECTION_20260711_v0.json",
        REPO_ROOT
        / "formal"
        / "docs"
        / "release"
        / "DORMANT_SOURCE_SANITATION_20260711_v0.json",
        REPO_ROOT / ".vscode" / "settings.json",
    ]
    for path in paths:
        raw = path.read_bytes()
        assert not raw.startswith(b"\xef\xbb\xbf")
        json.loads(raw)


def test_canonical_maintenance_zones_are_pinned_to_lf() -> None:
    paths = [
        ".github/workflows/ci.yml",
        ".vscode/settings.json",
        "requirements.ci.lock",
        "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        "formal/python/tools/loop_control_registry_integrity.py",
        "formal/toe_formal/ToeFormalAll.lean",
    ]
    completed = subprocess.run(
        ["git", "check-attr", "eol", "--", *paths],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    rows = [line for line in completed.stdout.splitlines() if line.strip()]
    assert len(rows) == len(paths)
    assert all(line.endswith(": lf") for line in rows)


def test_eol_policy_does_not_glob_hash_bound_historical_trees() -> None:
    attributes = (REPO_ROOT / ".gitattributes").read_text(encoding="utf-8")
    forbidden_broad_rules = [
        "formal/docs/release/*.json text",
        "formal/output/**/*.json text",
        "formal/python/**/*.py text",
        "formal/toe_formal/**/*.lean text",
    ]
    for rule in forbidden_broad_rules:
        assert rule not in attributes
