from __future__ import annotations
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
P=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
V=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
D=R/"TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0.json"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_director_packet_has_four_unselected_options():
    d=read(D); assert len(d["options"])==4; assert d["option_selected"]=="NONE"; assert d["model_or_postulate_created"] is False
def test_proposal_has_five_stages_one_model_and_one_theorem_packet():
    p=read(P); assert len(p["stage_definitions_proposed"])==5; assert p["maximum_frozen_model_versions"]==1; assert p["maximum_primary_theorem_packets"]==1
def test_provenance_and_status_vocabularies_are_separate():
    p=read(P); assert len(p["provenance_vocabulary"])==5; assert len(p["theorem_status_vocabulary"])==7
def test_external_checks_are_not_action_terms():
    p=read(P); assert p["external_evaluation_checks"]==["C_FINITE_APPROXIMATION","C_IDENTIFIABILITY","C_COMPLEXITY"]; assert p["external_checks_are_not_action_terms"] is True
def test_program_remains_uninstalled_unopened_and_nonexecuting():
    p=read(P); assert p["program_installation_status"]=="UNINSTALLED"; assert p["scientific_attempts"]==0; assert p["branch_selected"]=="NONE"; assert p["ccft_v0_model"]=="NONE"; assert p["theorem_or_counterexample_attempted"] is False
def test_review_accepts_all_checks_and_hashes():
    v=read(V); assert v["accepted"] is True; assert v["reviewed_result"]["sha256"]==sha(P); assert v["reviewed_director_packet"]["sha256"]==sha(D); assert all(v["checks"].values())
