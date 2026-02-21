from __future__ import annotations

import json
import re
import unicodedata
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
REGISTRY_PATH = PAPER_DIR / "PILLAR_DISCHARGE_REGISTRY_v0.json"
ROADMAP_PATH = PAPER_DIR / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = PAPER_DIR / "RESULTS_TABLE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

CANONICAL_REQUIRED_HEADERS = [
    "## TARGET section",
    "## ASSUMPTION_FREEZE section",
    "## CANONICAL_ROUTE section",
    "## ANTI_SHORTCUT section",
    "## COUNTERFACTUAL section",
    "## INDEPENDENT_NECESSITY section",
    "## HARDENING section",
    "## BOUNDED_SCOPE section",
    "## DRIFT_GATES section",
    "## ADJUDICATION_SYNC section",
]
FORBIDDEN_LEGACY_HEADERS = [
    "## ASSUMPTION FREEZE section",
    "## CANONICAL ROUTE section",
    "## COUNTERFACTUAL ROUTE section",
    "## INDEPENDENT NECESSITY ROUTE section",
    "## BOUNDED SCOPE section",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _normalize_heading(raw_heading_line: str) -> str:
    text = unicodedata.normalize("NFKC", raw_heading_line)
    text = text.replace("\u00A0", " ")
    text = re.sub(r"\s+", " ", text.strip())
    return text


def _heading_lines(markdown: str) -> list[str]:
    return re.findall(r"^##\s+.*$", markdown, flags=re.MULTILINE)


def _extract_token_value(token: str, text: str) -> str:
    m = re.search(rf"{re.escape(token)}:\s*([A-Za-z0-9_\-,]+)", text)
    assert m is not None, f"Missing token: {token}"
    return m.group(1)


def _extract_adjudication_value(pillar_key: str, text: str) -> str:
    token = f"PILLAR_{pillar_key}_FULL_DERIVATION_DISCHARGE_ADJUDICATION"
    m = re.search(rf"{re.escape(token)}:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing adjudication token: {token}"
    return m.group(1)


def _matrix_status_for_pillar(pillar_name: str, roadmap_text: str) -> str:
    m = re.search(
        rf"^\|\s*`{re.escape(pillar_name)}`\s*\|\s*`([^`]+)`\s*\|",
        roadmap_text,
        flags=re.MULTILINE,
    )
    assert m is not None, f"Missing roadmap row for {pillar_name}."
    return m.group(1)


def _results_row_status(row_id: str, results_text: str) -> str:
    m = re.search(rf"^\|\s*{re.escape(row_id)}\s*\|\s*`([^`]+)`\s*\|", results_text, flags=re.MULTILINE)
    assert m is not None, f"Missing results row: {row_id}"
    return m.group(1)


def test_normalize_heading_handles_whitespace_nbsp_and_nfkc_compatibility() -> None:
    # NBSP and repeated spaces collapse to canonical single-space formatting.
    raw_nbsp = "##\u00A0ASSUMPTION_FREEZE\u00A0\u00A0section"
    assert _normalize_heading(raw_nbsp) == "## ASSUMPTION_FREEZE section"

    # Tabs and mixed whitespace collapse to canonical spacing.
    raw_tabs = "##\tCANONICAL_ROUTE\t\tsection   "
    assert _normalize_heading(raw_tabs) == "## CANONICAL_ROUTE section"

    # NFKC compatibility normalization converts full-width characters.
    raw_fullwidth = "## ＡＮＴＩ＿ＳＨＯＲＴＣＵＴ section"
    assert _normalize_heading(raw_fullwidth) == "## ANTI_SHORTCUT section"

    # Heading words containing spaces normalize to single-space form.
    raw_spaced = "##  INDEPENDENT   NECESSITY   ROUTE   section  "
    assert _normalize_heading(raw_spaced) == "## INDEPENDENT NECESSITY ROUTE section"

    # Hyphenated forms are not silently canonicalized to underscore token grammar.
    raw_hyphen = "## ANTI-SHORTCUT section"
    assert _normalize_heading(raw_hyphen) == "## ANTI-SHORTCUT section"
    assert _normalize_heading(raw_hyphen) not in CANONICAL_REQUIRED_HEADERS


def test_pillar_discharge_registry_shape_and_files_exist() -> None:
    registry = _read_json(REGISTRY_PATH)
    assert registry.get("registry_id") == "PILLAR_DISCHARGE_REGISTRY_v0"
    assert registry.get("registry_version") == 1
    required_headers = registry.get("required_headers")
    assert isinstance(required_headers, list) and required_headers, "Registry required_headers must be a non-empty list."
    assert required_headers == CANONICAL_REQUIRED_HEADERS, (
        "Registry required_headers must match the canonical pillar-discharge header contract."
    )
    assert len(required_headers) == len(set(required_headers)), "Registry required_headers must be unique."

    pillars = registry.get("pillars")
    assert isinstance(pillars, list) and pillars, "Registry pillars must be a non-empty list."
    key_fields = ["pillar_key", "pillar_name", "roadmap_row_id", "discharge_target_id"]
    for field in key_fields:
        values = [entry[field] for entry in pillars]
        assert len(values) == len(set(values)), f"Registry field `{field}` must be unique across pillars."

    paper_dir_prefix = "formal/docs/paper/"
    for entry in pillars:
        discharge_doc_rel = entry["discharge_doc_path"]
        umbrella_doc_rel = entry["umbrella_target_doc_path"]
        assert discharge_doc_rel.startswith(paper_dir_prefix), (
            f"Registry discharge_doc_path must be under `{paper_dir_prefix}`: {discharge_doc_rel}"
        )
        assert umbrella_doc_rel.startswith(paper_dir_prefix), (
            f"Registry umbrella_target_doc_path must be under `{paper_dir_prefix}`: {umbrella_doc_rel}"
        )
        assert (REPO_ROOT / Path(discharge_doc_rel)).exists(), f"Missing discharge doc path: {discharge_doc_rel}"
        assert (REPO_ROOT / Path(umbrella_doc_rel)).exists(), f"Missing umbrella doc path: {umbrella_doc_rel}"

        required_rows = entry["required_results_rows"]
        assert isinstance(required_rows, list) and required_rows, (
            f"Registry required_results_rows must be a non-empty list for pillar `{entry['pillar_name']}`."
        )
        assert len(required_rows) == len(set(required_rows)), (
            f"Registry required_results_rows must be unique for pillar `{entry['pillar_name']}`."
        )

    _ = _read(ROADMAP_PATH)
    _ = _read(RESULTS_PATH)
    _ = _read(STATE_PATH)


def test_pillar_full_derivation_discharge_lane_contract_is_enforced_for_registered_pillars() -> None:
    registry = _read_json(REGISTRY_PATH)
    required_headers: list[str] = list(registry["required_headers"])
    pillars: list[dict] = list(registry["pillars"])

    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)
    state_text = _read(STATE_PATH)

    violations: list[str] = []

    for entry in pillars:
        pillar_key = entry["pillar_key"]
        pillar_name = entry["pillar_name"]
        target_id = entry["discharge_target_id"]
        discharge_doc_rel = entry["discharge_doc_path"]
        umbrella_doc_rel = entry["umbrella_target_doc_path"]
        state_header = entry["state_checkpoint_header"]
        required_rows: list[str] = list(entry["required_results_rows"])

        discharge_path = REPO_ROOT / Path(discharge_doc_rel)
        umbrella_path = REPO_ROOT / Path(umbrella_doc_rel)
        discharge_text = _read(discharge_path)
        umbrella_text = _read(umbrella_path)
        raw_headings = _heading_lines(discharge_text)
        normalized_headings = [_normalize_heading(h) for h in raw_headings]

        if target_id not in discharge_text:
            violations.append(f"{pillar_name}: discharge target ID missing from discharge doc ({discharge_doc_rel}).")

        for header in required_headers:
            normalized_header = _normalize_heading(header)
            count = sum(1 for h in normalized_headings if h == normalized_header)
            if count == 0:
                violations.append(
                    f"{pillar_name}: missing required discharge-doc header `{header}` in {discharge_doc_rel}."
                )
            elif count != 1:
                violations.append(
                    f"{pillar_name}: required discharge-doc header `{header}` must appear exactly once in {discharge_doc_rel}."
                )
        for header in FORBIDDEN_LEGACY_HEADERS:
            normalized_header = _normalize_heading(header)
            if normalized_header in normalized_headings:
                violations.append(
                    f"{pillar_name}: forbidden legacy discharge-doc header `{header}` present in {discharge_doc_rel}."
                )

        for raw in raw_headings:
            if "\t" in raw:
                violations.append(f"{pillar_name}: tabs are forbidden in discharge-doc headings (`{raw}`).")
            if not raw.isascii():
                violations.append(f"{pillar_name}: non-ASCII characters are forbidden in discharge-doc headings (`{raw}`).")

        normalized_required_headers = {_normalize_heading(header) for header in required_headers}
        for normalized_heading in normalized_headings:
            if re.fullmatch(r"## [A-Z0-9_]+ section", normalized_heading):
                if normalized_heading not in normalized_required_headers:
                    violations.append(
                        f"{pillar_name}: unknown section heading `{normalized_heading}` is not in canonical registry header set."
                    )
            elif normalized_heading.endswith(" section"):
                violations.append(
                    f"{pillar_name}: section heading `{normalized_heading}` violates canonical `## [A-Z0-9_]+ section` format."
                )

        adjudication_value = _extract_adjudication_value(pillar_key, discharge_text)
        if not (adjudication_value == "NOT_YET_DISCHARGED" or adjudication_value.startswith("DISCHARGED")):
            violations.append(
                f"{pillar_name}: adjudication value `{adjudication_value}` must be NOT_YET_DISCHARGED or DISCHARGED_*."
            )

        pre_discharge_no_promotion_value = "ATTEMPT_ONLY_NO_DISCHARGE"
        discharged_no_promotion_value = "DISCHARGED_NO_AUTOMATIC_PROMOTION"
        is_discharged_posture = adjudication_value.startswith("DISCHARGED_")
        expected_no_promotion_value = (
            discharged_no_promotion_value if is_discharged_posture else pre_discharge_no_promotion_value
        )

        localization_token = (
            f"PILLAR_{pillar_key}_FULL_DERIVATION_DISCHARGE_LOCALIZATION_GATE_v0: "
            "FULL_DISCHARGE_ARTIFACTS_ONLY"
        )
        no_promotion_token = (
            f"PILLAR_{pillar_key}_FULL_DERIVATION_DISCHARGE_NO_PROMOTION_v0: "
            f"{expected_no_promotion_value}"
        )
        boundary_token = (
            f"PILLAR_{pillar_key}_FULL_DERIVATION_DISCHARGE_BOUNDARY_v0: "
            "NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION"
        )
        required_doc_tokens = [localization_token, no_promotion_token, boundary_token]
        for token in required_doc_tokens:
            if token not in discharge_text:
                violations.append(f"{pillar_name}: missing required discharge-doc token `{token}`.")

        no_promotion_pre_token = (
            f"PILLAR_{pillar_key}_FULL_DERIVATION_DISCHARGE_NO_PROMOTION_v0: "
            f"{pre_discharge_no_promotion_value}"
        )
        no_promotion_post_token = (
            f"PILLAR_{pillar_key}_FULL_DERIVATION_DISCHARGE_NO_PROMOTION_v0: "
            f"{discharged_no_promotion_value}"
        )
        if no_promotion_pre_token in discharge_text and no_promotion_post_token in discharge_text:
            violations.append(
                f"{pillar_name}: no-promotion token appears in both pre- and post-discharge forms; keep exactly one."
            )
        if is_discharged_posture and no_promotion_pre_token in discharge_text:
            violations.append(
                f"{pillar_name}: discharged adjudication cannot keep legacy no-promotion value "
                f"`{pre_discharge_no_promotion_value}`."
            )
        if adjudication_value == "NOT_YET_DISCHARGED" and no_promotion_post_token in discharge_text:
            violations.append(
                f"{pillar_name}: NOT_YET_DISCHARGED adjudication cannot use post-discharge no-promotion value "
                f"`{discharged_no_promotion_value}`."
            )

        if discharge_doc_rel == umbrella_doc_rel:
            equivalence_token = f"PILLAR_{pillar_key}_DISCHARGE_DOC_IS_UMBRELLA_DOC_v0: TRUE"
            if equivalence_token not in discharge_text:
                violations.append(
                    f"{pillar_name}: discharge_doc_path equals umbrella_target_doc_path, "
                    f"but missing explicit equivalence token `{equivalence_token}`."
                )

        if target_id not in umbrella_text:
            violations.append(f"{pillar_name}: umbrella target doc does not reference discharge target ID `{target_id}`.")
        if discharge_doc_rel not in umbrella_text:
            violations.append(f"{pillar_name}: umbrella target doc does not reference discharge doc path `{discharge_doc_rel}`.")
        if target_id not in state_text:
            violations.append(f"{pillar_name}: State_of_the_Theory.md missing discharge target ID `{target_id}`.")
        if discharge_doc_rel not in state_text:
            violations.append(f"{pillar_name}: State_of_the_Theory.md missing discharge doc path `{discharge_doc_rel}`.")
        if state_header not in state_text:
            violations.append(f"{pillar_name}: State_of_the_Theory.md missing checkpoint header `{state_header}`.")
        if target_id not in roadmap_text:
            violations.append(f"{pillar_name}: roadmap missing discharge target ID `{target_id}`.")
        if discharge_doc_rel not in roadmap_text:
            violations.append(f"{pillar_name}: roadmap missing discharge doc path `{discharge_doc_rel}`.")

        physics_status = _extract_token_value(f"PILLAR-{pillar_key}_PHYSICS_STATUS", roadmap_text)
        governance_status = _extract_token_value(f"PILLAR-{pillar_key}_GOVERNANCE_STATUS", roadmap_text)
        proceed_gate = _extract_token_value(f"PROCEED_GATE_{pillar_key}", roadmap_text)
        matrix_gate = _extract_token_value(f"MATRIX_CLOSURE_GATE_{pillar_key}", roadmap_text)
        required_rows_from_roadmap_raw = _extract_token_value(f"REQUIRED_{pillar_key}_CLOSURE_ROWS", roadmap_text)
        required_rows_from_roadmap = {row.strip() for row in required_rows_from_roadmap_raw.split(",") if row.strip()}
        if required_rows_from_roadmap != set(required_rows):
            violations.append(
                f"{pillar_name}: roadmap REQUIRED_{pillar_key}_CLOSURE_ROWS mismatch "
                f"(roadmap={sorted(required_rows_from_roadmap)} registry={sorted(required_rows)})."
            )

        matrix_row_status = _matrix_status_for_pillar(pillar_name, roadmap_text)
        if matrix_row_status == "CLOSED":
            if not adjudication_value.startswith("DISCHARGED"):
                violations.append(
                    f"{pillar_name}: matrix status is CLOSED but adjudication is not DISCHARGED_* "
                    f"(found `{adjudication_value}`)."
                )
            if not proceed_gate.startswith("ALLOWED_"):
                violations.append(f"{pillar_name}: matrix status is CLOSED but proceed gate is not ALLOWED_*.")
            if not matrix_gate.startswith("ALLOWED_"):
                violations.append(f"{pillar_name}: matrix status is CLOSED but matrix closure gate is not ALLOWED_*.")
            if not physics_status.startswith("CLOSED_"):
                violations.append(f"{pillar_name}: matrix status is CLOSED but physics status is not CLOSED_*.")
            if not governance_status.startswith("CLOSED_"):
                violations.append(f"{pillar_name}: matrix status is CLOSED but governance status is not CLOSED_*.")
        elif adjudication_value == "NOT_YET_DISCHARGED":
            if matrix_row_status == "CLOSED":
                violations.append(f"{pillar_name}: NOT_YET_DISCHARGED adjudication cannot coexist with matrix CLOSED status.")

        for row_id in required_rows:
            if not row_id.startswith(f"TOE-{pillar_key}-"):
                violations.append(f"{pillar_name}: required results row `{row_id}` must use prefix `TOE-{pillar_key}-`.")

            row_occurrences = len(re.findall(rf"^\|\s*{re.escape(row_id)}\s*\|", results_text, flags=re.MULTILINE))
            if row_occurrences != 1:
                violations.append(f"{pillar_name}: required results row `{row_id}` must appear exactly once (found {row_occurrences}).")
                continue

            row_status = _results_row_status(row_id, results_text)
            if matrix_row_status == "CLOSED" and row_status.startswith("B-"):
                violations.append(
                    f"{pillar_name}: matrix status CLOSED requires non-blocked required rows, but `{row_id}` is `{row_status}`."
                )

        if adjudication_value == "NOT_YET_DISCHARGED":
            forbidden_patterns = [
                r"\bwe prove\b",
                r"\bwe derive\b",
                r"\bT-PROVED\b",
                rf"\|\s*`{re.escape(pillar_name)}`\s*\|\s*`CLOSED`\s*\|",
            ]
            present_forbidden = [
                pattern
                for pattern in forbidden_patterns
                if re.search(pattern, discharge_text, flags=re.IGNORECASE | re.DOTALL)
            ]
            if present_forbidden:
                violations.append(
                    f"{pillar_name}: NOT_YET_DISCHARGED discharge doc contains promotional language: "
                    + ", ".join(present_forbidden)
                )

        micro_docs = sorted(PAPER_DIR.glob("DERIVATION_TARGET*_MICRO_*.md"))
        localization_leaks = [
            str(path.relative_to(REPO_ROOT))
            for path in micro_docs
            if localization_token in _read(path)
        ]
        if localization_leaks:
            violations.append(
                f"{pillar_name}: localization token leaked into micro-cycle artifacts: " + ", ".join(localization_leaks)
            )

    assert not violations, "Pillar full-derivation discharge lane violations:\n- " + "\n- ".join(violations)


def test_results_table_row_ids_are_unique() -> None:
    text = _read(RESULTS_PATH)
    row_ids: list[str] = []
    for line in text.splitlines():
        if not line.startswith("| "):
            continue
        if line.startswith("|---") or line.startswith("| Result ID "):
            continue
        m = re.match(r"^\|\s*([^|]+?)\s*\|", line)
        if m is None:
            continue
        row_ids.append(m.group(1).strip())

    assert row_ids, "Expected at least one results row."
    duplicates = sorted({row_id for row_id in row_ids if row_ids.count(row_id) > 1})
    assert not duplicates, "RESULTS_TABLE_v0.md row IDs must be unique; duplicates: " + ", ".join(duplicates)
