from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


ROOT = find_repo_root(Path(__file__))
INVENTORY_PATH = ROOT / (
    "formal/docs/release/"
    "JULY_16_19_RESTRUCTURED_RECONCILIATION_"
    "DIVERGENT_LINEAGE_INVENTORY_20260727_v0.json"
)
REGISTRY_PATH = ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
BASELINE = "a099c6867493d48a7aaba2f79bf2e29ecbf2cfd3"
POST_RECOVERY_TIP = "e785b98d8aa9bc7c755e5b6767706bcd29d285a6"


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    ).stdout.strip()


def _inventory() -> dict:
    return json.loads(INVENTORY_PATH.read_text(encoding="utf-8"))


def test_all_inventory_objects_and_preservation_tags_resolve_exactly() -> None:
    inventory = _inventory()
    for row in inventory["protected_lineages"]:
        assert _git("rev-parse", f"{row['tag']}^{{}}") == row["commit"]
        assert _git("cat-file", "-t", row["commit"]) == "commit"


def test_post_recovery_lineage_relationship_and_acceptance_inventory_are_exact() -> None:
    inventory = _inventory()
    relationship = inventory["post_recovery_scientific_descendant_relationship"]
    assert _git("merge-base", BASELINE, POST_RECOVERY_TIP) == BASELINE
    assert int(_git("rev-list", "--count", f"{BASELINE}..{POST_RECOVERY_TIP}")) == (
        relationship["commits_after_restructured_baseline"]
    )
    assert _git("rev-parse", f"{POST_RECOVERY_TIP}^{{tree}}") == (
        inventory["protected_lineages"][2]["tree"]
    )
    observed = {
        line.split("\t", 1)[0]: line.split("\t", 1)[1]
        for line in _git(
            "log",
            "--format=%H%x09%s",
            "--regexp-ignore-case",
            "--grep=^accept",
            f"{BASELINE}..{POST_RECOVERY_TIP}",
        ).splitlines()
    }
    expected = {
        row["commit"]: row["subject"]
        for row in inventory["case_insensitive_acceptance_named_commits"]
    }
    assert observed == expected


def test_divergent_lineage_is_not_current_scientific_authority() -> None:
    inventory = _inventory()
    registry = json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    firewall = inventory["current_reconciliation_scientific_firewall"]
    assert registry["current_projection_v0"]["current_target"] == (
        firewall["canonical_target"]
    )
    assert firewall["scientific_target_rotated"] is False
    assert firewall["july_16_19_chain_adopted"] is False
    assert firewall["post_recovery_scientific_descendant_adopted"] is False
    assert inventory["post_recovery_scientific_descendant_relationship"][
        "maintenance_replay_adopts_this_lineage"
    ] is False
