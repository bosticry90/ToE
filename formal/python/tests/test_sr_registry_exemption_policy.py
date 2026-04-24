from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / 'formal' / 'docs' / 'paper' / 'PILLAR_DISCHARGE_REGISTRY_v0.json'
ROADMAP_PATH = REPO_ROOT / 'formal' / 'docs' / 'paper' / 'PHYSICS_ROADMAP_v0.md'
STATE_PATH = REPO_ROOT / 'State_of_the_Theory.md'
SR_ROADMAP_PATH = REPO_ROOT / 'formal' / 'docs' / 'paper' / 'DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md'

SR_EXEMPTION_TOKEN = 'PILLAR-SR_REGISTRY_EXEMPTION_v0: SR_CLOSURE_NOT_TRACKED_IN_GENERIC_REGISTRY'


def _read(path: Path) -> str:
    assert path.exists(), f'Missing required file: {path}'
    return path.read_text(encoding='utf-8')


def test_sr_registry_exemption_is_retired_after_registry_enrollment() -> None:
    registry = json.loads(_read(REGISTRY_PATH))
    pillars = registry.get('pillars', [])
    pillar_keys = {entry.get('pillar_key') for entry in pillars if isinstance(entry, dict)}
    assert 'SR' in pillar_keys, 'SR must now be enrolled in PILLAR_DISCHARGE_REGISTRY_v0.json.'

    roadmap_text, _ = split_active_and_archived(_read(ROADMAP_PATH), ROADMAP_PATH)
    state_text, _ = split_active_and_archived(_read(STATE_PATH), STATE_PATH)
    sr_roadmap_text, _ = split_active_and_archived(_read(SR_ROADMAP_PATH), SR_ROADMAP_PATH)

    assert SR_EXEMPTION_TOKEN not in roadmap_text, 'Roadmap must retire the SR registry-exemption token after enrollment.'
    assert SR_EXEMPTION_TOKEN not in state_text, 'State must retire the SR registry-exemption token after enrollment.'
    assert SR_EXEMPTION_TOKEN not in sr_roadmap_text, 'SR discharge doc must retire the SR registry-exemption token after enrollment.'
