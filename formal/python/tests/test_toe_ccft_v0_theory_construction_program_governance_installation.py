from __future__ import annotations
import hashlib, json
from pathlib import Path
from formal.python.tools import bounded_program_governance as g
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
M=ROOT/"formal/docs/release/bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
I=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_RESULT_v0.json"
V=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_REVIEW_v0.json"
REG=R/"LOOP_CONTROL_REGISTRY_v0.json"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_manifest_has_five_sequenced_stages():
    m=read(M); assert m["authorized_stage_count"]==5; assert [x["stage_number"] for x in m["stages"]]==[1,2,3,4,5]
    assert m["stages"][2]["semantic_stage_id"]=="CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION"
    assert m["stages"][3]["semantic_stage_id"]=="CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION"
def test_manifest_hash_and_scope_hashes_reproduce():
    m=read(M); assert m["manifest_hash"]==g._hashed_payload(m,"manifest_hash")
    assert all(x["canonical_scope_hash"]==g.scope_hash(x["canonical_scope"]) for x in m["stages"])
def test_director_and_provenance_contracts_are_bound():
    m=read(M); assert m["director_decision_packet_binding"]["option_selected"]=="NONE"
    assert m["provenance_vocabulary"]==['SOURCE_RECOVERED', 'KNOWN_PHYSICS_BASELINE', 'NEW_CCFT_POSTULATE', 'NUMERICAL_CONVENTION', 'MATHEMATICAL_CONTROL']; assert m["external_evaluation_checks"]==['C_FINITE_APPROXIMATION', 'C_IDENTIFIABILITY', 'C_COMPLEXITY']
    assert m["external_checks_are_not_action_terms"] is True
def test_stage_one_two_candidate_or_no_branch_results_block_silent_narrowing():
    m=read(M); assert set(m["stage_1_blocking_outcomes"])=={"RETAIN_TWO_SEPARATE_CONSTRUCTION_CANDIDATES","NO_BRANCH_READY_WITHOUT_FOUNDATIONAL_POSTULATE"}
def test_program_is_registered_unopened():
    r=read(REG)[g.PROGRAMS_KEY]["TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"]; assert r["state"]=="UNOPENED"; assert r["events"]==[]
    assert r["current_stage_number"]==0; assert r["repair_attempt_count"]==0; assert r["program_terminal_status"]=="INSTALLED_UNOPENED"
def test_installation_created_no_scientific_output():
    i=read(I); assert i["installed_program_state"]=="INSTALLED_UNOPENED"; assert i["scientific_attempts"]==0
    assert i["branch_selected"]=="NONE"; assert i["ccft_v0_model"]=="NONE"; assert i["primary_theorem_packet"]=="NONE"; assert i["theorem_or_counterexample_attempted"] is False
def test_independent_review_binds_result_and_manifest():
    v=read(V); assert v["accepted"] is True; assert v["reviewed_result"]["sha256"]==sha(I); assert v["reviewed_manifest"]["sha256"]==sha(M); assert all(v["checks"].values())
