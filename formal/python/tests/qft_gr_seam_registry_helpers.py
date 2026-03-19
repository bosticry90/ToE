from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REGISTRY_REL_PATH = "formal/docs/paper/QFT_GR_SEAM_PACKET_REGISTRY_v0.json"


def get_repo_root(start: Path) -> Path:
    return find_repo_root(start)


def load_registry(start: Path) -> dict:
    repo_root = get_repo_root(start)
    registry_path = repo_root / REGISTRY_REL_PATH
    if not registry_path.exists():
        raise AssertionError(f"Missing seam packet registry: {registry_path}")
    return json.loads(registry_path.read_text(encoding="utf-8"))


def get_packet_entry(registry: dict, packet_id: int) -> dict:
    packets = registry.get("packets", [])
    for packet in packets:
        if packet.get("packet_id") == packet_id:
            return packet
    raise AssertionError(f"Missing packet_id={packet_id} in seam registry")


def resolve_rel_path(repo_root: Path, rel_path: str) -> Path:
    return repo_root / rel_path
