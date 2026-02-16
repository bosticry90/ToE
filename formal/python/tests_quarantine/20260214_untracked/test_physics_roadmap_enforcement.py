from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
ROADMAP_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
RESULTS_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
CHECKLIST_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR01_DERIVATION_GRADE_CHECKLIST_v0.md"
)
ACTION_RAC_STANCE_DOC = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ACTION_RAC_STANCE_v0.md"
)
CLOSURE_PACKAGE_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md"
)
ACTION_RAC_ALIGNMENT_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def _split_semicolon_tokens(cell: str) -> list[str]:
    return [token.strip() for token in cell.split(";") if token.strip()]


def _parse_roadmap_rows(text: str) -> list[tuple[str, str, list[str], list[str], list[str]]]:
    rows = re.findall(
        r"^\|\s*`(PILLAR-[A-Z]+)`\s*\|\s*`(ACTIVE|LOCKED|CLOSED)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|",
        text,
        flags=re.MULTILINE,
    )
    parsed: list[tuple[str, str, list[str], list[str], list[str]]] = []
    for pillar, status, target_ids_cell, artifacts_cell, prereq_cell in rows:
        target_ids = _split_semicolon_tokens(target_ids_cell)
        artifact_paths = _split_semicolon_tokens(artifacts_cell)
        prereqs = _split_semicolon_tokens(prereq_cell)
        parsed.append((pillar, status, target_ids, artifact_paths, prereqs))
    return parsed


def _parse_promotion_attempt_rows(
    text: str,
) -> list[tuple[str, str, str, str, str, str, str, str, str, str]]:
    rows = re.findall(
        r"^\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*`([^`]+)`\s*\|\s*`(B-AWAITING-DISCHARGE-ATTEMPT|B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN)`\s*\|\s*`(YES|NO)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*([^|]+?)\s*\|$",
        text,
        flags=re.MULTILINE,
    )
    return [tuple(field.strip() for field in row) for row in rows]


def _promotion_attempt_log_section(text: str) -> str:
    section_match = re.search(
        r"## Promotion Attempt Log\s*(?P<section>.*?)(?:\n##\s+|\Z)",
        text,
        flags=re.DOTALL,
    )
    assert section_match is not None, "Physics roadmap must include Promotion Attempt Log section."
    return section_match.group("section")


def _extract_single_enum_token(
    text: str,
    token_name: str,
    allowed_values_pattern: str,
) -> str:
    matches = re.findall(
        rf"^\s*-\s*`{re.escape(token_name)}:\s*({allowed_values_pattern})`\s*$",
        text,
        flags=re.MULTILINE,
    )
    assert len(matches) == 1, (
        f"Document must contain exactly one `{token_name}: <value>` token."
    )
    return matches[0]


def test_physics_roadmap_doc_exists_and_required_tokens() -> None:
    text = _read(ROADMAP_DOC)
    required_tokens = [
        "PHYSICS_ROADMAP_v0",
        "Classification:",
        "`P-POLICY`",
        "No-deviation sequencing rule:",
        "Pillar Activation Matrix",
        "`PILLAR-GR`",
        "`PILLAR-QM`",
        "`PILLAR-EM`",
        "`PILLAR-SR`",
        "`PILLAR-QFT`",
        "`PILLAR-STAT`",
        "`PILLAR-COSMO`",
        "TARGET-GR01-DERIV-CHECKLIST-PLAN",
        "TARGET-GR01-3D-03-PLAN",
        "TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN",
        "TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN",
        "TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN",
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "TARGET-GR01-3D-POINT-SOURCE-PLAN",
        "TARGET-QM-EVOL-PLAN",
        "TARGET-QM-MEAS-PLAN",
        "TARGET-QM-SYMM-PLAN",
        "TARGET-EM-U1-PLAN",
        "TARGET-SR-COV-PLAN",
        "TARGET-QFT-GAUGE-PLAN",
        "TARGET-QFT-EVOL-PLAN",
        "TARGET-TH-ENTROPY-PLAN",
        "TARGET-COSMO-BG-PLAN",
        "Post-GR01 unlock queue (frozen order intent):",
        "first unlock cohort: `PILLAR-SR` and `PILLAR-EM`",
        "Path 2 closure sprint lock (GR-only):",
        "do not unlock `PILLAR-QM`, `PILLAR-EM`, or `PILLAR-SR` while `TOE-GR-3D-03`",
        "`NOT_YET_DISCHARGED`.",
        "PHYSICS_PAPER_OUTLINE_v0.md",
        "Pillar-claim mapping rule (new-claim gate):",
        "`TOE-GR-*` -> `TARGET-GR01-DERIV-CHECKLIST-PLAN`",
        "`TOE-SR-*` -> `TARGET-SR-COV-PLAN`",
        "`TOE-EM-*` -> `TARGET-EM-U1-PLAN`",
        "`TOE-QM-*` -> `TARGET-QM-EVOL-PLAN;TARGET-QM-MEAS-PLAN;TARGET-QM-SYMM-PLAN`",
        "`TOE-QFT-*` -> `TARGET-QFT-GAUGE-PLAN;TARGET-QFT-EVOL-PLAN`",
        "`TOE-STAT-*` -> `TARGET-TH-ENTROPY-PLAN`",
        "`TOE-COSMO-*` -> `TARGET-COSMO-BG-PLAN`",
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TOE-GR-CONS-01",
        "DERIVATION_TARGET_GR01_3D_POINT_SOURCE_CLASS_v0.md",
        "DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md",
        "DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md",
        "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md",
        "DERIVATION_COMPLETENESS_GATE_v0.md",
        "Derivation completeness gate semantics (publication-grade tier):",
        "DERIVATION_COMPLETENESS_GATE",
        "conditional-publish endpoint",
        "Blocker discharge-attempt semantics (active-pillar blockers):",
        "`B-AWAITING-DISCHARGE-ATTEMPT`",
        "`B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN`",
        "Promotion attempt trigger and execution requirement:",
        "bounded attempt-package target/artifact pointer when the blocker is `TOE-GR-3D-03`",
        "closure-package target/artifact pointer when the blocker is `TOE-GR-3D-03`",
        "Promotion Attempt Log",
        "Next promotion objective (token)",
        "`PILLAR-GR / TOE-GR-3D-03 (Track B)`",
        "`PILLAR-GR / TOE-GR-CONS-01`",
        "TARGET-GR-CONS-PLAN",
        "formal/toe_formal/ToeFormal/GR/ConservationContract.lean",
        "gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility",
        "gr_conservation_under_contract_assumptions",
    ]
    for token in required_tokens:
        assert token in text, f"Physics roadmap missing required token: {token}"


def test_physics_roadmap_rows_have_target_ids_and_artifact_pointers() -> None:
    text = _read(ROADMAP_DOC)
    rows = _parse_roadmap_rows(text)
    assert rows, "Physics roadmap must include at least one parsed pillar row."

    required_pillars = {
        "PILLAR-GR",
        "PILLAR-QM",
        "PILLAR-EM",
        "PILLAR-SR",
        "PILLAR-QFT",
        "PILLAR-STAT",
        "PILLAR-COSMO",
    }
    parsed_pillars = {pillar for pillar, _, _, _, _ in rows}
    assert parsed_pillars == required_pillars, (
        "Physics roadmap must define exactly the required pillars.\n"
        f"Expected: {sorted(required_pillars)}\n"
        f"Found: {sorted(parsed_pillars)}"
    )

    for pillar, _, target_ids, artifact_paths, _ in rows:
        assert target_ids and target_ids != ["NONE"], (
            f"{pillar} must define at least one target ID."
        )
        assert artifact_paths and artifact_paths != ["NONE"], (
            f"{pillar} must define at least one target artifact pointer."
        )
        for rel in artifact_paths:
            artifact = REPO_ROOT / rel
            assert artifact.exists(), (
                f"{pillar} references missing target artifact pointer: {rel}"
            )


def test_pillar_gr_row_is_singleton_by_raw_prefix_and_marks_deriv_gate_closed() -> None:
    text = _read(ROADMAP_DOC)

    gr_row_prefix_count = len(
        re.findall(r"^\|\s*`PILLAR-GR`\s*\|", text, flags=re.MULTILINE)
    )
    assert gr_row_prefix_count == 1, (
        "Roadmap must contain exactly one raw `PILLAR-GR` row prefix in the pillar matrix."
    )

    gr_row_match = re.search(r"^\|\s*`PILLAR-GR`\s*\|.*$", text, flags=re.MULTILINE)
    assert gr_row_match is not None, "Missing `PILLAR-GR` row in pillar matrix."
    gr_row = gr_row_match.group(0)

    assert "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN" in gr_row, (
        "`PILLAR-GR` row must retain derivation-completeness gate target token."
    )
    assert "TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN" in gr_row, (
        "`PILLAR-GR` row must retain the bounded 3D-03 discharge-attempt package target token."
    )
    assert "TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN" in gr_row, (
        "`PILLAR-GR` row must retain the bounded 3D-03 closure-focused package target token."
    )
    assert "TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN" in gr_row, (
        "`PILLAR-GR` row must retain the action/RAC retirement-alignment target token."
    )
    assert "already `CLOSED` for v0 discrete-only scope" in gr_row, (
        "`PILLAR-GR` row must explicitly mark the derivation-completeness gate as already closed in v0 scope."
    )


def test_physics_roadmap_active_and_prerequisite_enforcement() -> None:
    text = _read(ROADMAP_DOC)
    rows = _parse_roadmap_rows(text)

    active_rows = [row for row in rows if row[1] == "ACTIVE"]
    assert len(active_rows) == 1, (
        f"Physics roadmap must have exactly one ACTIVE pillar (found {len(active_rows)})."
    )
    active_pillar = active_rows[0][0]
    assert active_pillar == "PILLAR-GR", (
        "During v0 sequencing, PILLAR-GR must be the only ACTIVE pillar."
    )

    target_status: dict[str, str] = {}
    for _, status, target_ids, _, _ in rows:
        for target_id in target_ids:
            target_status[target_id] = status

    for pillar, status, _, _, prereqs in rows:
        if status not in {"ACTIVE", "CLOSED"}:
            continue
        for prereq in prereqs:
            if prereq == "NONE":
                continue
            assert prereq in target_status, (
                f"{pillar} references unknown prerequisite target ID: {prereq}"
            )
            assert target_status[prereq] == "CLOSED", (
                f"{pillar} cannot be {status} while prerequisite {prereq} is "
                f"{target_status[prereq]}."
            )


def test_path2_gr_only_lock_keeps_qm_em_sr_locked_while_blockers_remain() -> None:
    roadmap = _read(ROADMAP_DOC)
    closure_package = _read(CLOSURE_PACKAGE_DOC)
    alignment_package = _read(ACTION_RAC_ALIGNMENT_DOC)
    rows = _parse_roadmap_rows(roadmap)
    status_by_pillar = {pillar: status for pillar, status, _, _, _ in rows}

    closure_adjudication = _extract_single_enum_token(
        closure_package,
        "ADJUDICATION",
        r"NOT_YET_SATISFIED|SATISFIED_v0_DISCRETE",
    )
    alignment_adjudication = _extract_single_enum_token(
        alignment_package,
        "ALIGNMENT_ADJUDICATION",
        r"NOT_YET_DISCHARGED|DISCHARGED_CONDITIONAL_PUBLISH_v0",
    )

    if (
        closure_adjudication == "NOT_YET_SATISFIED"
        or alignment_adjudication == "NOT_YET_DISCHARGED"
    ):
        for pillar in ["PILLAR-QM", "PILLAR-EM", "PILLAR-SR"]:
            assert status_by_pillar.get(pillar) == "LOCKED", (
                "Path 2 closure sprint lock requires "
                f"{pillar} to remain LOCKED while GR blockers remain."
            )


def test_physics_roadmap_target_ids_are_declared_in_target_artifacts() -> None:
    text = _read(ROADMAP_DOC)
    rows = _parse_roadmap_rows(text)

    for pillar, _, target_ids, artifact_paths, _ in rows:
        artifacts_text = [(REPO_ROOT / rel).read_text(encoding="utf-8") for rel in artifact_paths]
        for target_id in target_ids:
            assert any(target_id in artifact_text for artifact_text in artifacts_text), (
                f"{pillar} target ID {target_id} must be declared in at least one listed target artifact."
            )


def test_toe_claim_prefixes_map_to_frozen_pillar_closure_tokens() -> None:
    roadmap = _read(ROADMAP_DOC)
    results = _read(RESULTS_DOC)

    prefix_to_required_tokens = {
        "GR": ["TARGET-GR01-DERIV-CHECKLIST-PLAN"],
        "SR": ["TARGET-SR-COV-PLAN"],
        "EM": ["TARGET-EM-U1-PLAN"],
        "QM": ["TARGET-QM-EVOL-PLAN", "TARGET-QM-MEAS-PLAN", "TARGET-QM-SYMM-PLAN"],
        "QFT": ["TARGET-QFT-GAUGE-PLAN", "TARGET-QFT-EVOL-PLAN"],
        "STAT": ["TARGET-TH-ENTROPY-PLAN"],
        "COSMO": ["TARGET-COSMO-BG-PLAN"],
    }
    for prefix, tokens in prefix_to_required_tokens.items():
        for token in tokens:
            assert token in roadmap, (
                f"Roadmap claim-prefix mapping for TOE-{prefix}-* must include closure token: {token}"
            )

    result_ids = re.findall(r"^\|\s*([A-Z0-9-]+)\s*\|", results, flags=re.MULTILINE)
    ignore_ids = {"TOE-PLAN-01", "TOE-SPEC-01", "TOE-MAP-01", "TOE-ASM-01"}
    for result_id in result_ids:
        if not result_id.startswith("TOE-"):
            continue
        if result_id in ignore_ids:
            continue
        m = re.match(r"^TOE-([A-Z]+)-", result_id)
        assert m is not None, (
            f"TOE result row must use a valid pillar-prefixed ID form TOE-<PILLAR>-*: {result_id}"
        )
        pillar_prefix = m.group(1)
        assert pillar_prefix in prefix_to_required_tokens, (
            f"TOE result ID prefix has no frozen pillar-closure mapping in roadmap: {result_id}"
        )


def test_gr_cannot_be_marked_closed_without_3d_and_action_rac_closure_tokens() -> None:
    roadmap = _read(ROADMAP_DOC)
    results = _read(RESULTS_DOC)
    checklist = _read(CHECKLIST_DOC)
    action_rac = _read(ACTION_RAC_STANCE_DOC)
    rows = _parse_roadmap_rows(roadmap)
    gr_rows = [row for row in rows if row[0] == "PILLAR-GR"]
    assert len(gr_rows) == 1, "Roadmap must include exactly one PILLAR-GR row."
    gr_status = gr_rows[0][1]

    if gr_status != "CLOSED":
        return

    roadmap_required = [
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TARGET-GR01-3D-03-PLAN",
        "TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN",
        "DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md",
        "TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN",
        "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md",
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "DERIVATION_COMPLETENESS_GATE_v0.md",
        "TOE-GR-CONS-01",
        "conditional-publish endpoint",
        "TOE_GR01_ACTION_RAC_STANCE_v0.md",
    ]
    for token in roadmap_required:
        assert token in roadmap, (
            f"PILLAR-GR cannot be CLOSED without roadmap closure token: {token}"
        )

    checklist_required = [
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TARGET-GR01-3D-03-PLAN",
        "DERIVATION_TARGET_GR01_3D_MAINSTREAM_CLASS_v0.md",
        "TARGET-GR01-ACTION-RAC-RETIREMENT-ALIGNMENT-PLAN",
        "DERIVATION_TARGET_GR01_ACTION_RAC_RETIREMENT_ALIGNMENT_v0.md",
        "TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN",
        "DERIVATION_COMPLETENESS_GATE_v0.md",
        "mainstream equivalence proof to canonical weak-field form `nabla^2 Phi = kappa * rho`",
        "Separable3DMappingAssumptions",
        "poissonEquation3D_of_componentwise_poissonEquation1D_under_separable",
        "conditional-publish endpoint",
    ]
    for token in checklist_required:
        assert token in checklist, (
            f"PILLAR-GR cannot be CLOSED without checklist closure token: {token}"
        )

    action_rac_required = [
        "conditional-publish endpoint",
        "hAction",
        "hRAC",
    ]
    for token in action_rac_required:
        assert token in action_rac, (
            f"PILLAR-GR cannot be CLOSED without action/RAC stance token: {token}"
        )

    results_required = [
        "TOE-GR-3D-02",
        "TOE-GR-3D-03",
        "TOE-GR-CONS-01",
    ]
    for token in results_required:
        assert token in results, (
            f"PILLAR-GR cannot be CLOSED without results token: {token}"
        )


def test_blocker_promotion_attempt_log_enforces_attempt_execution_for_defined_paths() -> None:
    text = _read(ROADMAP_DOC)
    rows = _parse_promotion_attempt_rows(text)
    assert rows, "Physics roadmap must include at least one promotion-attempt log row."
    section = _promotion_attempt_log_section(text)

    required_blocker_rows = {
        "PILLAR-GR / TOE-GR-3D-03 (Track B)",
        "PILLAR-GR / TOE-GR-CONS-01",
    }
    found_blocker_rows = {row[0] for row in rows}
    assert required_blocker_rows.issubset(found_blocker_rows), (
        "Promotion-attempt log must include required GR blocker rows.\n"
        f"Missing: {sorted(required_blocker_rows - found_blocker_rows)}"
    )
    for blocker_id in sorted(required_blocker_rows):
        raw_row_count = len(
            re.findall(
                rf"^\|\s*`{re.escape(blocker_id)}`\s*\|",
                section,
                flags=re.MULTILINE,
            )
        )
        assert raw_row_count == 1, (
            "Promotion-attempt log body must contain exactly one raw table row for blocker ID "
            f"{blocker_id} (found {raw_row_count})."
        )

    seen: set[str] = set()
    for (
        blocker_id,
        target_id,
        hypothesis,
        mechanism,
        cycle_id,
        attempt_status,
        discharge_path_defined,
        scaffold_module,
        objective_token,
        result,
    ) in rows:
        assert blocker_id not in seen, (
            f"Promotion-attempt log must contain exactly one row per blocker ID: {blocker_id}"
        )
        seen.add(blocker_id)

        assert target_id != "NONE", f"{blocker_id} must define a target ID."
        assert hypothesis != "NONE", f"{blocker_id} must define a promotion hypothesis."
        assert mechanism != "NONE", f"{blocker_id} must define a promotion mechanism."
        assert cycle_id.startswith("Cycle-"), (
            f"{blocker_id} must pin a promotion attempt cycle ID (Cycle-*)."
        )
        assert objective_token != "NONE", (
            f"{blocker_id} must define a next promotion objective theorem token."
        )
        assert result != "NONE", f"{blocker_id} must define an attempt result statement."

        if discharge_path_defined == "YES":
            assert scaffold_module != "NONE", (
                f"{blocker_id} marks discharge path as defined but has no scaffold module pointer."
            )
            scaffold = REPO_ROOT / scaffold_module
            assert scaffold.exists(), (
                f"{blocker_id} references missing discharge scaffold module: {scaffold_module}"
            )
            assert attempt_status != "B-AWAITING-DISCHARGE-ATTEMPT", (
                f"{blocker_id} cannot remain B-AWAITING-DISCHARGE-ATTEMPT when discharge path is defined."
            )
            scaffold_text = scaffold.read_text(encoding="utf-8")
            if attempt_status == "B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN":
                assert objective_token in scaffold_text, (
                    f"{blocker_id} attempted status requires objective token "
                    f"to exist in scaffold module: {objective_token}"
                )
        else:
            assert scaffold_module == "NONE", (
                f"{blocker_id} must set scaffold module to NONE when discharge path is NO."
            )

        if attempt_status == "B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN":
            assert "attempt executed" in result.lower(), (
                f"{blocker_id} attempted status must report executed attempt result text."
            )


def test_track_b_attempt_log_row_is_singleton_and_contains_attempt_package_tokens() -> None:
    text = _read(ROADMAP_DOC)
    section = _promotion_attempt_log_section(text)
    blocker_id = "PILLAR-GR / TOE-GR-3D-03 (Track B)"

    raw_row_count = len(
        re.findall(
            rf"^\|\s*`{re.escape(blocker_id)}`\s*\|",
            section,
            flags=re.MULTILINE,
        )
    )
    assert raw_row_count == 1, (
        "Promotion-attempt log must contain exactly one raw table row for "
        f"{blocker_id}."
    )

    row_match = re.search(
        rf"^\|\s*`{re.escape(blocker_id)}`\s*\|(?P<rest>.*)$",
        section,
        flags=re.MULTILINE,
    )
    assert row_match is not None, f"Missing attempt-log row for blocker: {blocker_id}"
    row_text = row_match.group(0)

    required_row_tokens = [
        "`TARGET-GR01-3D-POINT-SOURCE-PLAN`",
        "TARGET-GR01-3D-03-ATTEMPT-PACKAGE-PLAN",
        "DERIVATION_TARGET_GR01_3D_03_DISCHARGE_ATTEMPT_PACKAGE_v0.md",
        "TARGET-GR01-3D-03-CLOSURE-PACKAGE-PLAN",
        "DERIVATION_TARGET_GR01_3D_03_CLOSURE_PACKAGE_v0.md",
        "`Cycle-002 (2026-02-14)`",
        "`B-DISCHARGE-ATTEMPTED-BUT-UNPROVEN`",
        "`YES`",
        "`formal/toe_formal/ToeFormal/Variational/GR01Mainstream3DPointSource.lean`",
        "`gr01_mainstream3d_point_source_poissonEquation3D_away_from_source_exists_from_operator_equation_under_invertibility`",
    ]
    for token in required_row_tokens:
        assert token in row_text, (
            f"Track-B attempt-log row missing required token: {token}"
        )

    stale_row_tokens = [
        "`Cycle-001 (2026-02-14)`",
        "`gr01_mainstream3d_point_source_solution_exists_for_operator_equation_under_invertibility`",
    ]
    for stale_token in stale_row_tokens:
        assert stale_token not in row_text, (
            "Track-B attempt-log row must not retain stale Cycle-001 objective tokens "
            f"after Cycle-002 advancement: {stale_token}"
        )


def test_promotion_attempt_log_schema_is_singleton_and_new_format_only() -> None:
    text = _read(ROADMAP_DOC)
    heading = "## Promotion Attempt Log"
    old_header = (
        "| Pillar / Blocker | Target ID | Promotion hypothesis | Promotion mechanism | "
        "Promotion attempt cycle | Attempt status | Discharge path defined | "
        "Discharge scaffold module | Result |"
    )
    new_header = (
        "| Pillar / Blocker | Target ID | Promotion hypothesis | Promotion mechanism | "
        "Promotion attempt cycle | Attempt status | Discharge path defined | "
        "Discharge scaffold module | Next promotion objective (token) | Result |"
    )

    assert text.count(heading) == 1, (
        "Roadmap must contain exactly one Promotion Attempt Log section heading."
    )
    assert text.count(new_header) == 1, (
        "Roadmap must contain exactly one Promotion Attempt Log table header "
        "with objective-token schema."
    )
    assert text.count(old_header) == 0, (
        "Roadmap must not contain the obsolete 9-column Promotion Attempt Log schema."
    )
