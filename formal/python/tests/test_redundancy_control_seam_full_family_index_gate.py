from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
INDEX_PATH = (
	REPO_ROOT
	/ "formal"
	/ "output"
	/ "reports"
	/ "redundancy_control_seam_family_index_full_20260409_v0.json"
)

EXPECTED_FAMILY_IDS = {
	"SEAM_QM_STAT_CLASS_B_PHYSICS_PILOT",
	"SEAM_COSMO_SR_CLASS_B_PHYSICS_PILOT",
}


def _read(path: Path) -> str:
	assert path.exists(), f"Missing required file: {path}"
	return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
	active, _ = split_active_and_archived(_read(path), path)
	return active


def _json(path: Path) -> dict:
	return json.loads(_read(path))


def test_redundancy_control_seam_full_family_index_shape() -> None:
	payload = _json(INDEX_PATH)

	assert payload.get("schema_id") == "REDUNDANCY_CONTROL_SEAM_FAMILY_INDEX_FULL_20260409_v0"
	assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM_EXPANDED"
	assert payload.get("pilot_scope") == "ALL_ACTIVE_SEAM_FAMILIES"
	assert payload.get("admission_rule") == (
		"MISSING_OWNER_OR_RETENTION_OR_ARCHIVE_OR_PARITY_DEPENDENCIES_IS_HARD_FAIL"
	)

	families = payload.get("families")
	assert isinstance(families, list)

	observed_ids = {str(f.get("family_id", "")) for f in families}
	assert observed_ids == EXPECTED_FAMILY_IDS

	for family in families:
		owner = family.get("canonical_owner")
		retention = family.get("retention_policy")
		archive_destination = family.get("archive_destination")
		parity = family.get("parity_dependencies")

		assert isinstance(owner, str) and owner
		assert (REPO_ROOT / owner).exists(), f"Canonical owner path must exist: {owner}"

		assert retention == "ACTIVE_WINDOW_90_DAYS_THEN_ARCHIVE"

		assert isinstance(archive_destination, str) and archive_destination.startswith("archive/")
		assert (REPO_ROOT / archive_destination).exists(), (
			f"Archive destination must exist: {archive_destination}"
		)

		assert isinstance(parity, list) and len(parity) >= 3
		for dep in parity:
			assert isinstance(dep, str) and dep
			assert (REPO_ROOT / dep).exists(), f"Parity dependency path must exist: {dep}"


def test_redundancy_control_seam_full_family_index_tokens_present() -> None:
	state_text = _active_text(STATE_PATH)
	checklist_text = _read(CHECKLIST_PATH)

	state_required = [
		"REDUNDANCY_CONTROL_SEAM_FULL_INDEX_STATUS_v0: ACTIVE_ALL_FAMILIES_NONLIVE_NONCLAIM",
		"REDUNDANCY_CONTROL_SEAM_FULL_INDEX_v0: formal/output/reports/redundancy_control_seam_family_index_full_20260409_v0.json",
		"REDUNDANCY_CONTROL_SEAM_FULL_INDEX_GATE_v0: formal/python/tests/test_redundancy_control_seam_full_family_index_gate.py",
	]
	for token in state_required:
		assert token in state_text, f"Missing state token: {token}"

	checklist_required = [
		"Seam full-family index declared? YES / NO",
		"Seam full-family coverage complete? YES / NO",
	]
	for token in checklist_required:
		assert token in checklist_text, f"Missing checklist token: {token}"
