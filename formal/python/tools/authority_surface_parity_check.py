from __future__ import annotations

import argparse
import re
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

THEORY_RESTART_TOKEN_RE = re.compile(
    r"THEORY_RESTART_T\d+_[A-Z0-9_]+_v\d+:\s*[^`\r\n]+"
)
REMEDIATION_TOKEN_RE = re.compile(
    r"THEORY_RESTART_T\d+_REMEDIATION_[A-Z0-9_]+_v0:\s*[^`\r\n]+"
)
THEORY_RESTART_BULLET_RE = re.compile(
    r"(?m)^- `THEORY_RESTART_T\d+_[A-Z0-9_]+_v\d+:\s*[^`\r\n]+`\s*$"
)
DERIVED_BLOCK_BEGIN = "<!-- BEGIN DERIVED REMEDIATION TOKENS -->"
DERIVED_BLOCK_END = "<!-- END DERIVED REMEDIATION TOKENS -->"


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def extract_remediation_tokens(content: str) -> list[str]:
    tokens = REMEDIATION_TOKEN_RE.findall(content)
    return [token.strip() for token in tokens]


def extract_theory_restart_tokens(content: str) -> list[str]:
    tokens = THEORY_RESTART_TOKEN_RE.findall(content)
    return [token.strip() for token in tokens]


def render_theory_restart_block(tokens: list[str]) -> str:
    body = [f"- `{token}`" for token in tokens]
    lines = [
        DERIVED_BLOCK_BEGIN,
        "> Derived from `State_of_the_Theory.md`. Refresh with `./py.ps1 -m formal.python.tools.authority_surface_parity_check --write-roadmap`.",
        *body,
        DERIVED_BLOCK_END,
    ]
    return "\n".join(lines)


def generate_synced_roadmap_content(state_content: str, roadmap_content: str) -> str:
    rendered_block = render_theory_restart_block(extract_theory_restart_tokens(state_content))

    if DERIVED_BLOCK_BEGIN in roadmap_content and DERIVED_BLOCK_END in roadmap_content:
        pattern = re.compile(
            rf"{re.escape(DERIVED_BLOCK_BEGIN)}.*?{re.escape(DERIVED_BLOCK_END)}",
            flags=re.DOTALL,
        )
        return pattern.sub(rendered_block, roadmap_content, count=1)

    matches = list(THEORY_RESTART_BULLET_RE.finditer(roadmap_content))
    if not matches:
        raise RuntimeError("Could not locate THEORY_RESTART token block in PHYSICS_ROADMAP_v0.md.")

    start = matches[0].start()
    end = matches[-1].end()
    return roadmap_content[:start] + rendered_block + roadmap_content[end:]


def sync_roadmap_from_state(*, write: bool) -> bool:
    state_content = _read_text(STATE_PATH)
    roadmap_content = _read_text(ROADMAP_PATH)
    synced_content = generate_synced_roadmap_content(state_content, roadmap_content)

    if write and synced_content != roadmap_content:
        ROADMAP_PATH.write_text(synced_content, encoding="utf-8")
        return True
    return False


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
    parser.add_argument(
        "--write-roadmap",
        action="store_true",
        help="Rewrite the remediation-token block in PHYSICS_ROADMAP_v0.md from State_of_the_Theory.md.",
    )
    args = parser.parse_args()
    if args.write_roadmap:
        changed = sync_roadmap_from_state(write=True)
        print(f"authority_surface_parity_check: roadmap_sync={'UPDATED' if changed else 'UNCHANGED'}")
    return run(strict_order=args.strict_order)


if __name__ == "__main__":
    raise SystemExit(main())
