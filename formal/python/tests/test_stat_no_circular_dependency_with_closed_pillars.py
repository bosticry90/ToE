from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STAT_PLAN_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
THERMO_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md"
QM_DISCHARGE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md"
QFT_DISCHARGE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _split_token_cell(cell: str) -> list[str]:
    value = cell.strip().strip("`")
    if value.upper() == "NONE":
        return []
    return [token.strip().strip("`") for token in value.split(";") if token.strip()]


def _pillar_rows(text: str) -> dict[str, dict[str, object]]:
    rows: dict[str, dict[str, object]] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line.startswith("| `PILLAR-"):
            continue
        cols = [c.strip() for c in line.split("|") if c.strip()]
        if len(cols) < 5:
            continue

        pillar_id = cols[0].strip("`")
        status = cols[1].strip("`")
        # Skip non-pillar inventory rows such as "PILLAR-GR / TOE-GR-...".
        if not re.fullmatch(r"PILLAR-[A-Z0-9-]+", pillar_id):
            continue
        if status not in {"LOCKED", "ACTIVE", "CLOSED"}:
            continue

        assert pillar_id not in rows, f"Duplicate roadmap pillar row detected: {pillar_id}"
        rows[pillar_id] = {
            "status": status,
            "targets": _split_token_cell(cols[2]),
            "prereqs": _split_token_cell(cols[4]),
            "raw": line,
        }
    assert rows, "No canonical pillar rows were parsed from PHYSICS_ROADMAP_v0.md."
    return rows


def _pillar_dependency_graph(rows: dict[str, dict[str, object]]) -> dict[str, set[str]]:
    target_owner: dict[str, str] = {}
    for pillar_id, row in rows.items():
        for target in row["targets"]:  # type: ignore[index]
            assert target not in target_owner, (
                f"Duplicate pillar-target ownership in roadmap table: `{target}` "
                f"owned by both `{target_owner[target]}` and `{pillar_id}`."
            )
            target_owner[target] = pillar_id

    graph: dict[str, set[str]] = {pillar_id: set() for pillar_id in rows}
    for pillar_id, row in rows.items():
        for prereq in row["prereqs"]:  # type: ignore[index]
            owner = target_owner.get(prereq)
            if owner is not None:
                graph[pillar_id].add(owner)
    return graph


def _reachable(graph: dict[str, set[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        node = stack.pop()
        for dep in graph.get(node, set()):
            if dep in seen:
                continue
            seen.add(dep)
            stack.append(dep)
    return seen


def _assert_no_match(text: str, pattern: str, *, path: Path) -> None:
    m = re.search(pattern, text)
    assert m is None, f"Unexpected token `{m.group(0)}` in {path} (STAT readiness circularity gate)."


def test_stat_no_circular_dependency_with_closed_pillars() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    rows = _pillar_rows(roadmap_text)
    graph = _pillar_dependency_graph(rows)
    matrix = _read_json(MATRIX_PATH)

    assert "PILLAR-STAT" in rows, "Roadmap must define a canonical `PILLAR-STAT` row."
    stat_row = rows["PILLAR-STAT"]
    assert stat_row["status"] in {"LOCKED", "ACTIVE"}, (
        "STAT dependency gate expects either the historical LOCKED posture or the canonical ACTIVE posture."
    )
    assert "TARGET-TH-ENTROPY-PLAN" in stat_row["targets"]  # type: ignore[operator]

    matrix_pillars = matrix.get("pillars", {})
    for pillar_id in ("PILLAR-QFT", "PILLAR-QM", "PILLAR-GR", "PILLAR-EM", "PILLAR-SR"):
        entry = matrix_pillars.get(pillar_id)
        assert isinstance(entry, dict), f"Missing matrix entry for `{pillar_id}`."
        assert entry.get("matrix_status") == "CLOSED", f"`{pillar_id}` must remain `CLOSED` during STAT readiness."

    reachable_from_stat = _reachable(graph, "PILLAR-STAT")
    if stat_row["status"] == "LOCKED":
        assert "PILLAR-QM" not in reachable_from_stat, (
            "STAT prerequisite chain must not route through QM during locked readiness."
        )
        assert "PILLAR-QFT" not in reachable_from_stat, (
            "STAT prerequisite chain must not route through QFT during locked readiness."
        )
    assert all(rows[p]["status"] == "CLOSED" for p in reachable_from_stat), (
        "STAT prerequisite chain must only traverse CLOSED pillars."
    )

    closed_pillars = [pillar_id for pillar_id, row in rows.items() if row["status"] == "CLOSED"]
    for pillar_id in closed_pillars:
        assert "PILLAR-STAT" not in _reachable(graph, pillar_id), (
            f"Circular dependency detected: `{pillar_id}` depends (directly or transitively) on `PILLAR-STAT`."
        )

    stat_plan_text = _read(STAT_PLAN_PATH)
    thermo_target_text = _read(THERMO_TARGET_PATH)
    for path, text in (
        (STAT_PLAN_PATH, stat_plan_text),
        (THERMO_TARGET_PATH, thermo_target_text),
    ):
        # Locked-stage STAT docs must remain free of cross-pillar assumption imports.
        _assert_no_match(text, r"\bASM-QM-[A-Z0-9-]+\b", path=path)
        _assert_no_match(text, r"\bASM-QFT-[A-Z0-9-]+\b", path=path)
        _assert_no_match(text, r"\bASM-GR(?:01)?-[A-Z0-9-]+\b", path=path)

        # Prevent hidden coupling to unresolved QM/QFT execution artifacts at readiness stage.
        for forbidden in (
            "DERIVATION_TARGET_QM_",
            "DERIVATION_TARGET_QFT_",
            "TARGET-QM-",
            "TARGET-QFT-",
            "formal/output/qm_",
            "formal/output/qft_",
        ):
            assert forbidden not in text, (
                f"Unexpected QM/QFT dependency token `{forbidden}` in {path} during STAT locked readiness."
            )

    qm_discharge_text = _read(QM_DISCHARGE_PATH)
    qft_discharge_text = _read(QFT_DISCHARGE_PATH)
    assert "TARGET-TH-ENTROPY-PLAN" not in qm_discharge_text, (
        "QM discharge target must not depend on STAT entropy target during STAT readiness."
    )
    assert "TARGET-TH-ENTROPY-PLAN" not in qft_discharge_text, (
        "QFT discharge target must not depend on STAT entropy target."
    )
