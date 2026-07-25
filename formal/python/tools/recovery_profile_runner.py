from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROFILE_ROOT = REPO_ROOT / "formal/output/validation_profiles"
PROFILE_FILES = {
    "current_control_plane": PROFILE_ROOT
    / "CURRENT_CONTROL_PLANE_PROFILE_20260725_v2.json",
    "historical_debt": PROFILE_ROOT / "HISTORICAL_DEBT_PROFILE_20260725_v2.json",
}
REGISTRY_PATH = PROFILE_ROOT / "RECOVERY_OBLIGATION_REGISTRY_20260725_v2.json"
RECONCILIATION_PATH = (
    PROFILE_ROOT / "VALIDATION_PROFILE_RECONCILIATION_20260725_v2.json"
)
IMMUTABLE_PROFILE_PATHS = (
    *PROFILE_FILES.values(),
    REGISTRY_PATH,
    RECONCILIATION_PATH,
)


class ProfileRunError(ValueError):
    """Raised when a validation run is not bound to an immutable profile."""


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def freeze_profile_state() -> dict[str, str]:
    missing = [str(path) for path in IMMUTABLE_PROFILE_PATHS if not path.is_file()]
    if missing:
        raise ProfileRunError(f"profile files are missing: {missing}")
    return {
        path.relative_to(REPO_ROOT).as_posix(): sha256_path(path)
        for path in IMMUTABLE_PROFILE_PATHS
    }


def load_profile(name: str) -> dict[str, Any]:
    if name not in PROFILE_FILES:
        raise ProfileRunError(f"unknown execution profile: {name}")
    payload = json.loads(PROFILE_FILES[name].read_bytes())
    if payload.get("profile") != name:
        raise ProfileRunError(f"profile name mismatch: {name}")
    nodeids = payload.get("nodeids")
    if (
        not isinstance(nodeids, list)
        or len(nodeids) != payload.get("nodeid_count")
        or len(nodeids) != len(set(nodeids))
    ):
        raise ProfileRunError(f"profile membership is invalid: {name}")
    return payload


def verify_inventory(profile: dict[str, Any], inventory_path: Path) -> None:
    raw = inventory_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != profile["inventory_sha256"]:
        raise ProfileRunError("execution inventory hash differs from frozen profile")
    nodeids = [line for line in raw.decode("utf-8").splitlines() if line]
    if len(nodeids) != profile["inventory_count"]:
        raise ProfileRunError("execution inventory count differs from frozen profile")


def run_profile(
    *,
    name: str,
    inventory_path: Path,
    output_junit: Path,
    basetemp: Path,
) -> dict[str, Any]:
    before = freeze_profile_state()
    profile = load_profile(name)
    verify_inventory(profile, inventory_path)
    output_junit.parent.mkdir(parents=True, exist_ok=True)
    basetemp.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f"toe-{name}-args-") as temp:
        args_path = Path(temp) / "pytest-args.txt"
        args_path.write_text(
            "\n".join(
                [
                    "-p",
                    "no:cacheprovider",
                    "-q",
                    f"--basetemp={basetemp}",
                    f"--junitxml={output_junit}",
                    *profile["nodeids"],
                ]
            )
            + "\n",
            encoding="utf-8",
            newline="\n",
        )
        env = dict(os.environ)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        completed = subprocess.run(
            [sys.executable, "-m", "pytest", f"@{args_path}"],
            cwd=REPO_ROOT,
            env=env,
            check=False,
        )
    after = freeze_profile_state()
    if before != after:
        raise ProfileRunError("test execution mutated its frozen profile state")
    return {
        "profile": name,
        "profile_hashes_before": before,
        "profile_hashes_after": after,
        "profile_state_unchanged": True,
        "nodeid_count": profile["nodeid_count"],
        "pytest_exit_code": completed.returncode,
        "junit": str(output_junit),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--profile",
        required=True,
        choices=sorted(PROFILE_FILES),
    )
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--junit", type=Path, required=True)
    parser.add_argument("--basetemp", type=Path, required=True)
    args = parser.parse_args()
    result = run_profile(
        name=args.profile,
        inventory_path=args.inventory,
        output_junit=args.junit,
        basetemp=args.basetemp,
    )
    print(json.dumps(result, indent=2))
    return result["pytest_exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
