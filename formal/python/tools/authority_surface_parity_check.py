from __future__ import annotations

import argparse
import re
from pathlib import Path


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = _find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

REMEDIATION_TOKEN_RE = re.compile(
    r"THEORY_RESTART_T\d+_REMEDIATION_[A-Z0-9_]+_v0:\s*[^`\r\n]+"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def extract_remediation_tokens(content: str) -> list[str]:
    tokens = REMEDIATION_TOKEN_RE.findall(content)
    return [token.strip() for token in tokens]


def compare_remediation_tokens(state_tokens: list[str], roadmap_tokens: list[str], strict_order: bool) -> list[str]:
    errors: list[str] = []

    state_set = set(state_tokens)
    roadmap_set = set(roadmap_tokens)

    missing_in_roadmap = sorted(state_set - roadmap_set)
    missing_in_state = sorted(roadmap_set - state_set)

    if missing_in_roadmap:
        errors.append("Missing in PHYSICS_ROADMAP_v0.md:\n- " + "\n- ".join(missing_in_roadmap))
    if missing_in_state:
        errors.append("Missing in State_of_the_Theory.md:\n- " + "\n- ".join(missing_in_state))

    if strict_order and state_tokens != roadmap_tokens:
        errors.append("Token order mismatch between State and Roadmap for remediation token sequence.")

    return errors


def run(strict_order: bool) -> int:
    state_tokens = extract_remediation_tokens(_read_text(STATE_PATH))
    roadmap_tokens = extract_remediation_tokens(_read_text(ROADMAP_PATH))

    errors = compare_remediation_tokens(state_tokens, roadmap_tokens, strict_order=strict_order)
    if errors:
        print("authority_surface_parity_check: FAILED")
        for error in errors:
            print(error)
        return 1

    print("authority_surface_parity_check: OK")
    print(f"token_count={len(state_tokens)}")
    print(f"strict_order={strict_order}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate remediation token parity between State_of_the_Theory and PHYSICS_ROADMAP authority surfaces."
    )
    parser.add_argument(
        "--strict-order",
        action="store_true",
        help="Require token sequence order to be identical across both surfaces.",
    )
    args = parser.parse_args()
    return run(strict_order=args.strict_order)


if __name__ == "__main__":
    raise SystemExit(main())
