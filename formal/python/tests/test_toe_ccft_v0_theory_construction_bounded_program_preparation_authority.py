from __future__ import annotations
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
A=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0.json"
V=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0.json"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_authority_is_preparation_only():
    a=read(A); assert a["authorized_target"]=="prepare_bounded_ccft_v0_theory_construction_program"; assert a["proposal_preparation_authorized"] is True
    assert a["program_installation_authorized"] is False; assert a["branch_selection_authorized"] is False
def test_terminal_bindings_reproduce():
    assert all(sha(ROOT/x["path"])==x["sha256"] for x in read(A)["consumed_terminal_checkpoint"])
def test_four_options_are_required_without_selection():
    a=read(A); assert len(a["required_director_packet_options"])==4; assert a["postulate_or_model_construction_authorized"] is False
def test_theorem_and_archive_work_are_prohibited():
    a=read(A); assert a["theorem_discovery_authorized"] is False; assert "REOPEN_HISTORICAL_OR_TARGETED_ARCHIVE_RECOVERY" in a["prohibited_work"]
def test_review_accepts_all_checks():
    v=read(V); assert v["authority_sha256"]==sha(A); assert v["accepted"] is True; assert all(v["checks"].values())
