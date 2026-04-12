from __future__ import annotations

import argparse
import re
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
TGC92_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "WS_10_TGC_92_CLOSURE_TO_BLOCKER_TRACEABILITY_DECISION_PACKAGE_20260410_v0.md"
)
TGC93_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md"
)


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token: str) -> str:
    pattern = re.compile(
        rf"(?m)^\s*(?:[-*]\s+)?`?{re.escape(token)}`?\s*:\s*`?(\S+?)`?\s*$"
    )
    match = pattern.search(text)
    if not match:
        raise ValueError(f"Missing token: {token}")
    return match.group(1).strip()


def _enforce_branch(tgc92_evidence: str, tgc93_decision: str, tgc93_auth: str) -> None:
    if tgc92_evidence == "TRUE":
        if tgc93_decision != "AUTHORIZE_SINGLE_SEAM_REENTRY":
            raise AssertionError(
                "TGC-93 branch mismatch: expected AUTHORIZE_SINGLE_SEAM_REENTRY when TGC92 evidence is TRUE."
            )
        if tgc93_auth != "AUTHORIZED":
            raise AssertionError(
                "TGC-93 authorization mismatch: expected AUTHORIZED when TGC92 evidence is TRUE."
            )
        return

    if tgc92_evidence == "FALSE":
        if tgc93_decision != "ROUTE_TO_THEOREM_GAP_REWORK":
            raise AssertionError(
                "TGC-93 branch mismatch: expected ROUTE_TO_THEOREM_GAP_REWORK when TGC92 evidence is FALSE."
            )
        if tgc93_auth != "DENIED":
            raise AssertionError(
                "TGC-93 authorization mismatch: expected DENIED when TGC92 evidence is FALSE."
            )
        return

    raise AssertionError(
        f"Unexpected TGC92 blocker-reducing evidence token value: {tgc92_evidence!r}"
    )


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate TGC-93 branch decision routing against TGC-92 evidence.")
    parser.add_argument("--tgc92", type=Path, default=TGC92_PATH, help="Path to TGC-92 markdown package.")
    parser.add_argument("--tgc93", type=Path, default=TGC93_PATH, help="Path to TGC-93 markdown package.")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    tgc92_path = ns.tgc92 if ns.tgc92.is_absolute() else (REPO_ROOT / ns.tgc92)
    tgc93_path = ns.tgc93 if ns.tgc93.is_absolute() else (REPO_ROOT / ns.tgc93)

    tgc92_text = _read(tgc92_path)
    tgc93_text = _read(tgc93_path)

    tgc92_evidence = _extract_token(tgc92_text, "TGC92_BLOCKER_REDUCING_CLOSURE_EVIDENCE_v0")
    tgc93_input = _extract_token(tgc93_text, "TGC93_INPUT_TGC92_BLOCKER_REDUCING_CLOSURE_EVIDENCE_v0")
    tgc93_decision = _extract_token(tgc93_text, "TGC93_BRANCH_DECISION_v0")
    tgc93_auth = _extract_token(tgc93_text, "TGC93_SEAM_REENTRY_AUTHORIZATION_v0")

    if tgc92_evidence != tgc93_input:
        raise AssertionError(
            "TGC-93 input token must match TGC-92 blocker-reducing evidence token. "
            f"observed tgc92={tgc92_evidence} tgc93_input={tgc93_input}"
        )

    _enforce_branch(tgc92_evidence, tgc93_decision, tgc93_auth)

    print(
        "tgc93_branch_decision_router: "
        f"tgc92_evidence={tgc92_evidence} "
        f"decision={tgc93_decision} "
        f"authorization={tgc93_auth}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
