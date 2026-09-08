from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_DIR / "LOOP_CONTROL_REGISTRY_v0.json"
SELECTOR_PATH = RELEASE_DIR / (
    "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_"
    "MAINTENANCE_ROUTE_SELECTION_20260719_v0.json"
)
PACKET_PATH = RELEASE_DIR / (
    "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_PACKET_20260719_v0.json"
)
REVIEW_PATH = RELEASE_DIR / (
    "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_"
    "AUTHORIZATION_INDEPENDENT_REVIEW_20260719_v0.json"
)


class ReviewError(RuntimeError):
    pass


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical(value: dict[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_review() -> dict[str, Any]:
    registry = _read(REGISTRY_PATH)
    selector = _read(SELECTOR_PATH)
    packet = _read(PACKET_PATH)
    checks = {
        "selector_targets_recovery_maintenance_only": selector.get(
            "selected_maintenance_target"
        )
        == "prepare_repository_authority_custody_and_reproducibility_recovery_packet_v0",
        "prior_sharding_lane_deferred_not_retired": selector.get(
            "previous_maintenance_lane_disposition"
        )
        == "DEFERRED_NOT_RETIRED",
        "registry_target_unchanged": selector.get("scientific_authority", {}).get(
            "current_target"
        )
        == registry.get("CURRENT_LIVE_NEXT_TARGET_v0"),
        "registry_evidence_unchanged": selector.get("scientific_authority", {}).get(
            "current_target_evidence"
        )
        == registry.get("CURRENT_LIVE_TARGET_EVIDENCE_v0"),
        "scientific_execution_frozen": selector.get("boundaries", {}).get(
            "scientific_execution_frozen"
        )
        is True,
        "no_scientific_registry_mutation": selector.get("boundaries", {}).get(
            "scientific_registry_mutation_authorized"
        )
        is False,
        "phase_order_is_frozen": [row.get("phase") for row in packet.get("phases", [])]
        == ["A", "B", "C"],
        "phase_a_is_read_only": packet.get("phases", [{}])[0].get(
            "may_modify_audited_worktree"
        )
        is False,
        "phase_b_requires_phase_a_review": packet.get("phases", [{}, {}])[1].get(
            "may_start_before_phase_a_acceptance"
        )
        is False,
        "phase_c_requires_fresh_clone": packet.get("phases", [{}, {}, {}])[2].get(
            "must_run_in_fresh_clone"
        )
        is True,
        "v2_regeneration_prohibited": "NO_V2_REGENERATION"
        in packet.get("prohibitions", []),
        "scientific_resumption_not_automatic": packet.get("phases", [{}, {}, {}])[2].get(
            "scientific_resumption_authorized_by_completion"
        )
        is False,
    }
    accepted = all(checks.values())
    return {
        "schema_id": (
            "REPOSITORY_AUTHORITY_CUSTODY_AND_REPRODUCIBILITY_RECOVERY_"
            "AUTHORIZATION_INDEPENDENT_REVIEW_20260719_v0"
        ),
        "accepted": accepted,
        "verdict": "ACCEPT" if accepted else "B-BLOCKED",
        "status": (
            "RECOVERY_MAINTENANCE_AUTHORITY_READY_FOR_PHASE_A"
            if accepted
            else "RECOVERY_MAINTENANCE_AUTHORITY_INCOMPLETE"
        ),
        "selector_sha256": _sha(SELECTOR_PATH),
        "packet_sha256": _sha(PACKET_PATH),
        "checks": checks,
        "selected_next_action": (
            "activate_repository_authority_custody_and_reproducibility_"
            "recovery_maintenance_authority_v0"
            if accepted
            else "stop_without_activation"
        ),
        "scientific_target_rotated": False,
        "scientific_execution_authorized": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    review = build_review()
    expected = _canonical(review)
    if args.write:
        REVIEW_PATH.write_bytes(expected)
    elif REVIEW_PATH.read_bytes() != expected:
        raise ReviewError("authorization review artifact is stale")
    return 0 if review["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
