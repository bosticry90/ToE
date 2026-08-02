from __future__ import annotations
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
A=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_v0.json"
V=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_REVIEW_v0.json"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_authority_is_installation_only():
    a=read(A); assert a["authorized_target"]=="install_toe_ccft_v0_theory_construction_and_theorem_discovery_bounded_program_v0"; assert a["installation_authorized"] is True
    assert a["scientific_stage_open_authorized"] is False; assert a["branch_selection_authorized"] is False
    assert a["model_or_postulate_construction_authorized"] is False; assert a["theorem_execution_authorized"] is False
def test_authority_review_accepts_bound_proposal():
    a=read(A); v=read(V); assert v["authority_sha256"]==sha(A); assert v["accepted"] is True; assert all(v["checks"].values())
    p=ROOT/a["consumed_proposal"]["path"]; q=ROOT/a["consumed_proposal"]["review_path"]
    assert sha(p)==a["consumed_proposal"]["sha256"]; assert sha(q)==a["consumed_proposal"]["review_sha256"]
