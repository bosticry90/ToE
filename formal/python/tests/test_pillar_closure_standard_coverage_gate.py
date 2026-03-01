from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / 'formal').exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STANDARD_PATH = REPO_ROOT / 'formal' / 'docs' / 'release' / 'PILLAR_CLOSURE_STANDARD_v0.md'
ROADMAP_PATH = REPO_ROOT / 'formal' / 'docs' / 'paper' / 'PHYSICS_ROADMAP_v0.md'
MATRIX_PATH = REPO_ROOT / 'formal' / 'docs' / 'paper' / 'PILLAR_STATUS_MATRIX_v1.json'
REGISTRY_PATH = REPO_ROOT / 'formal' / 'docs' / 'paper' / 'PILLAR_DISCHARGE_REGISTRY_v0.json'
STATE_PATH = REPO_ROOT / 'State_of_the_Theory.md'


def _read(path: Path) -> str:
    assert path.exists(), f'Missing required file: {path}'
    return path.read_text(encoding='utf-8')


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token: str) -> str:
    m = re.search(rf"\b{re.escape(token)}\s*:\s*([A-Za-z0-9_,-]+)", text)
    assert m is not None, f'Missing roadmap token: {token}'
    return m.group(1)


def test_pillar_closure_standard_structure_gate() -> None:
    text = _read(STANDARD_PATH)
    state_text = _read(STATE_PATH)

    assert 'Spec ID:' in text and '`PILLAR_CLOSURE_STANDARD_v0`' in text
    assert 'Classification:' in text and '`P-POLICY`' in text
    assert '## Standard rules' in text

    for required_path in (
        'formal/docs/paper/PHYSICS_ROADMAP_v0.md',
        'formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json',
        'formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json',
        'formal/python/tests/test_pillar_dual_layer_gate_template.py',
        'formal/python/tests/test_pillar_full_discharge_completion_mechanics.py',
        'formal/python/tests/test_pillar_closure_standard_coverage_gate.py',
    ):
        assert f'`{required_path}`' in text, f'Closure standard must pin `{required_path}`.'

    assert 'Any pillar admitted to `PILLAR_STATUS_MATRIX_v1.json` must define exactly one roadmap token each for:' in text
    assert '`PILLAR-*_PHYSICS_STATUS`' in text
    assert '`PILLAR-*_GOVERNANCE_STATUS`' in text
    assert '`PROCEED_GATE_*`' in text
    assert '`MATRIX_CLOSURE_GATE_*`' in text
    assert '`REQUIRED_*_CLOSURE_ROWS`' in text
    assert 'Any pillar with `matrix_status = CLOSED` in `PILLAR_STATUS_MATRIX_v1.json` must have exactly one registry entry in `PILLAR_DISCHARGE_REGISTRY_v0.json`.' in text
    assert 'Any future pillar promoted into `PILLAR_STATUS_MATRIX_v1.json` must satisfy Rule 1 in the same change set as matrix admission.' in text
    assert '`formal/docs/release/PILLAR_CLOSURE_STANDARD_v0.md`' in state_text


def test_all_matrix_pillars_have_standardized_closure_coverage() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    registry = _read_json(REGISTRY_PATH)
    registry_keys = {entry['pillar_key'] for entry in registry.get('pillars', []) if isinstance(entry, dict)}

    pillars = matrix.get('pillars', {})
    assert pillars, 'Expected matrix pillars to be defined.'

    for pillar_id, entry in pillars.items():
        pillar_key = pillar_id.replace('PILLAR-', '')
        physics = _extract_token(roadmap_text, f'PILLAR-{pillar_key}_PHYSICS_STATUS')
        governance = _extract_token(roadmap_text, f'PILLAR-{pillar_key}_GOVERNANCE_STATUS')
        proceed = _extract_token(roadmap_text, f'PROCEED_GATE_{pillar_key}')
        matrix_gate = _extract_token(roadmap_text, f'MATRIX_CLOSURE_GATE_{pillar_key}')
        required_rows = _extract_token(roadmap_text, f'REQUIRED_{pillar_key}_CLOSURE_ROWS')

        assert required_rows, f'{pillar_id}: required closure rows token must not be empty.'

        matrix_status = entry.get('matrix_status')
        if matrix_status == 'CLOSED':
            assert pillar_key in registry_keys, f'{pillar_id}: CLOSED pillars must be enrolled in the discharge registry.'
            assert physics.startswith('CLOSED_'), f'{pillar_id}: CLOSED pillars must carry CLOSED_* physics status.'
            assert governance.startswith('CLOSED_'), f'{pillar_id}: CLOSED pillars must carry CLOSED_* governance status.'
            assert proceed.startswith('ALLOWED_'), f'{pillar_id}: CLOSED pillars must carry ALLOWED_* proceed gate.'
            assert matrix_gate.startswith('ALLOWED_'), f'{pillar_id}: CLOSED pillars must carry ALLOWED_* matrix gate.'
        elif matrix_status == 'ACTIVE':
            assert physics.startswith('OPEN_'), f'{pillar_id}: ACTIVE pillars must carry OPEN_* physics status.'
            assert governance.startswith('OPEN_'), f'{pillar_id}: ACTIVE pillars must carry OPEN_* governance status.'
            assert proceed.startswith('BLOCKED_'), f'{pillar_id}: ACTIVE pillars must carry BLOCKED_* proceed gate.'
            assert matrix_gate.startswith('BLOCKED_'), f'{pillar_id}: ACTIVE pillars must carry BLOCKED_* matrix gate.'
