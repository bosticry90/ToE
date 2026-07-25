from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROFILE_ROOT = REPO_ROOT / "formal/output/validation_profiles"
PROFILE_FILES = {
    "current_control_plane": PROFILE_ROOT
    / "CURRENT_CONTROL_PLANE_PROFILE_20260725_v7.json",
    "historical_debt": PROFILE_ROOT / "HISTORICAL_DEBT_PROFILE_20260725_v7.json",
}
REGISTRY_PATH = PROFILE_ROOT / "RECOVERY_OBLIGATION_REGISTRY_20260725_v7.json"
RECONCILIATION_PATH = (
    PROFILE_ROOT / "VALIDATION_PROFILE_RECONCILIATION_20260725_v7.json"
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


def verify_inventory_bytes(profile: dict[str, Any], raw: bytes) -> None:
    if hashlib.sha256(raw).hexdigest() != profile["inventory_sha256"]:
        raise ProfileRunError("execution inventory hash differs from frozen profile")
    nodeids = [line for line in raw.decode("utf-8").splitlines() if line]
    if len(nodeids) != profile["inventory_count"]:
        raise ProfileRunError("execution inventory count differs from frozen profile")


def collect_inventory_bytes() -> bytes:
    from formal.python.tools.recovery_current_acceptance_inventory import (
        collect_nodeids,
    )

    return ("\n".join(collect_nodeids()) + "\n").encode("utf-8")


def _junit_identity_map(nodeids: list[str]) -> dict[tuple[str, str], str]:
    mapped: dict[tuple[str, str], str] = {}
    for nodeid in nodeids:
        path, *selectors = nodeid.split("::")
        if not selectors:
            raise ProfileRunError(f"profile node ID has no selector: {nodeid}")
        classname = path.removesuffix(".py").replace("/", ".")
        if len(selectors) > 1:
            classname += "." + ".".join(selectors[:-1])
        key = (classname, selectors[-1])
        if key in mapped:
            raise ProfileRunError(f"ambiguous JUnit identity: {key}")
        mapped[key] = nodeid
    return mapped


def reconcile_historical_junit(
    *,
    profile: dict[str, Any],
    junit_path: Path,
    pytest_exit_code: int,
) -> dict[str, Any]:
    if profile["profile"] != "historical_debt":
        raise ProfileRunError("recorded-failure reconciliation is historical-only")
    root = ET.parse(junit_path).getroot()
    testcases = list(root.iter("testcase"))
    identity_map = _junit_identity_map(profile["nodeids"])
    observed_nonpassing: list[str] = []
    unmapped: list[dict[str, str]] = []
    for testcase in testcases:
        if testcase.find("failure") is None and testcase.find("error") is None:
            continue
        key = (testcase.attrib.get("classname", ""), testcase.attrib.get("name", ""))
        nodeid = identity_map.get(key)
        if nodeid is None:
            unmapped.append({"classname": key[0], "name": key[1]})
        else:
            observed_nonpassing.append(nodeid)
    observed = set(observed_nonpassing)
    known = set(profile["known_nonpassing_nodeids"])
    unexpected = sorted(observed - known)
    recovered = sorted(known - observed)
    complete = len(testcases) == profile["nodeid_count"]
    accepted = (
        complete
        and pytest_exit_code in {0, 1}
        and not unmapped
        and not unexpected
    )
    return {
        "verdict": (
            "HISTORICAL_DEBT_COMPLETE_WITH_RECORDED_FAILURES"
            if accepted
            else "HISTORICAL_REPORTING_BLOCKED"
        ),
        "reporting_completed": complete,
        "profile_nodeids": profile["nodeid_count"],
        "junit_testcases": len(testcases),
        "known_nonpassing": len(known),
        "observed_nonpassing": len(observed),
        "unexpected_nonpassing": unexpected,
        "recovered_nodeids": recovered,
        "unmapped_nonpassing": unmapped,
        "pytest_exit_code": pytest_exit_code,
        "accepted": accepted,
    }


def run_profile(
    *,
    name: str,
    inventory_path: Path | None,
    collect_current_inventory: bool,
    output_junit: Path,
    basetemp: Path,
    allow_recorded_historical_failures: bool = False,
) -> dict[str, Any]:
    before = freeze_profile_state()
    profile = load_profile(name)
    if (inventory_path is None) == (not collect_current_inventory):
        raise ProfileRunError(
            "provide exactly one of inventory_path or collect_current_inventory"
        )
    inventory_raw = (
        collect_inventory_bytes()
        if collect_current_inventory
        else inventory_path.read_bytes()
    )
    verify_inventory_bytes(profile, inventory_raw)
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
    result = {
        "profile": name,
        "profile_hashes_before": before,
        "profile_hashes_after": after,
        "profile_state_unchanged": True,
        "nodeid_count": profile["nodeid_count"],
        "pytest_exit_code": completed.returncode,
        "junit": str(output_junit),
        "inventory_mode": (
            "COLLECTED_FROM_COMMITTED_TEST_SOURCE"
            if collect_current_inventory
            else "FROZEN_EXTERNAL_INVENTORY"
        ),
    }
    if allow_recorded_historical_failures:
        result["historical_reporting"] = reconcile_historical_junit(
            profile=profile,
            junit_path=output_junit,
            pytest_exit_code=completed.returncode,
        )
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--profile",
        required=True,
        choices=sorted(PROFILE_FILES),
    )
    inventory_group = parser.add_mutually_exclusive_group(required=True)
    inventory_group.add_argument("--inventory", type=Path)
    inventory_group.add_argument(
        "--collect-current-inventory",
        action="store_true",
    )
    parser.add_argument("--junit", type=Path, required=True)
    parser.add_argument("--basetemp", type=Path, required=True)
    parser.add_argument("--allow-recorded-historical-failures", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    result = run_profile(
        name=args.profile,
        inventory_path=args.inventory,
        collect_current_inventory=args.collect_current_inventory,
        output_junit=args.junit,
        basetemp=args.basetemp,
        allow_recorded_historical_failures=args.allow_recorded_historical_failures,
    )
    raw = json.dumps(result, indent=2) + "\n"
    if args.report is not None:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(raw, encoding="utf-8", newline="\n")
    print(raw, end="")
    if args.allow_recorded_historical_failures:
        return 0 if result["historical_reporting"]["accepted"] else 2
    return result["pytest_exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
