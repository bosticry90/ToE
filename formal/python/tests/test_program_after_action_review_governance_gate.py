from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
AAR_POLICY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "PROGRAM_AFTER_ACTION_REVIEW_GOVERNANCE_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_aar_policy_identity_tokens_exist() -> None:
    text = _read(AAR_POLICY_PATH)
    required = [
        "# Program After-Action Review Governance v0",
        "`PROGRAM_AFTER_ACTION_REVIEW_GOVERNANCE_v0`",
        "`P-POLICY`",
        "`PROGRAM_AAR_GOVERNANCE_ADJUDICATION: ACTIVE_v0`",
    ]
    missing = [tok for tok in required if tok not in text]
    assert not missing, (
        "AAR governance policy is missing required identity token(s): "
        + ", ".join(missing)
    )


def test_aar_policy_mandatory_sections_exist() -> None:
    text = _read(AAR_POLICY_PATH)
    required_headers = [
        "## 1) Purpose",
        "## 2) Plain-language glossary (mandatory meanings)",
        "## 3) Mission statement (enforceable)",
        "## 4) What worked and must continue (non-negotiable)",
        "## 5) Gaps that must be improved (required work areas)",
        "## 6) Program phase policy",
        "## 7) Top five actionable program directives (binding)",
        "## 8) Execution guardrails (binding)",
        "## 9) Success criteria for this governance artifact",
        "## 10) Change control",
    ]
    missing = [h for h in required_headers if h not in text]
    assert not missing, (
        "AAR governance policy is missing required section header(s): "
        + ", ".join(missing)
    )


def test_aar_policy_top_five_directives_are_present() -> None:
    text = _read(AAR_POLICY_PATH)
    required_directives = [
        "1. Reduce modeling-bridge size.",
        "2. Consolidate documentation layers.",
        "3. Introduce first falsifiable predictive deviation.",
        "4. Add non-algebraic derivation strategies.",
        "5. Define explicit long-term inevitability criteria.",
    ]
    missing = [d for d in required_directives if d not in text]
    assert not missing, (
        "AAR governance policy is missing one or more top-five directives: "
        + ", ".join(missing)
    )


def test_aar_policy_enforcement_language_is_explicit() -> None:
    text = _read(AAR_POLICY_PATH)
    must_tokens = [
        "MUST",
        "MUST NOT",
        "authoritative",
        "enforceable",
        "anti-circular",
        "canonical",
        "compatibility",
    ]
    missing = [tok for tok in must_tokens if tok not in text]
    assert not missing, (
        "AAR governance policy is missing required enforcement term(s): "
        + ", ".join(missing)
    )
