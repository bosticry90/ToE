"""Retain and generalize the v1 phase-sensitivity regression witness."""
from copy import deepcopy

import pytest
import sympy as sp

from formal.python.toe.generic_runner import rv_source_derivation_v2 as r
from formal.python.toe.generic_runner import seven_record_source_candidate_v5 as candidate


@pytest.fixture(scope='module')
def source(): return r.load_inputs()


@pytest.fixture(scope='module')
def results(source): return r.calculate(source)


@pytest.mark.parametrize('index',range(6))
@pytest.mark.parametrize('vertex',range(2))
def test_changed_gauge_vertex_phase_fails_for_every_record(source,index,vertex):
    bad=deepcopy(source)
    row=bad['records'][index]['vertices'][vertex]
    row['exact_rule']=row['exact_rule'].replace('+i*','-i*',1)
    with pytest.raises(r.exact.VerificationError,match='RV_VERTEX_PHASE_OR_RULE_INCONSISTENT'):
        r.calculate(bad)


@pytest.mark.parametrize('index',range(2))
def test_changed_propagator_prescription_rejected(source,index):
    bad=deepcopy(source)
    bad['propagators'][index]['rule']=bad['propagators'][index]['rule'].replace('+i*0','-i*0')
    with pytest.raises(r.exact.VerificationError,match='PHASE_DOMAIN'): r.calculate(bad)


@pytest.mark.parametrize('field,value',[
    ('path_integral_phase','exp(-i*S)'),
    ('covariant_derivative','D_mu=partial_mu+i*g*A'),
])
def test_changed_action_convention_rejected(source,field,value):
    bad=deepcopy(source)
    bad['fourier'][field]=value
    with pytest.raises(r.exact.VerificationError): r.calculate(bad)


def test_baselines_preserved_with_executed_phase_ledgers(source,results):
    original=r.v1.calculate(source)
    for old,new in zip(original,results):
        assert old['physical_coefficient']==new['physical_coefficient']
        assert new['phase']['phase']==sp.prod(new['phase']['factors'])==1
        assert new['phase']['uv_master_residue']==1


def test_rv06_consistent_zero_charge_propagates(source,results):
    bad=deepcopy(source)
    rec=bad['records'][5]
    rec['fields'][0]['hypercharge']='0'
    rec['vertices'][0]['generator_representation']='0'
    rec['vertices'][0]['exact_rule']='+i*g1*gamma^mu*T_0'
    updated=r.calculate(bad)
    assert updated[5]['physical_coefficient']==0 and results[5]['physical_coefficient']!=0
    assert updated[:5]==results[:5]


def test_stale_representation_binding_rejected(source):
    bad=deepcopy(source)
    bad['records'][2]['fields'][0]['su2']='SINGLET_1'
    with pytest.raises(r.exact.VerificationError,match='RV_PHASE_REPRESENTATION_BINDING'): r.calculate(bad)


def test_phase_nodes_are_active_coefficient_parents():
    packet=candidate.compute()
    nodes={n['node_id']:n for n in packet['stage_dag']['nodes']}
    for record in r.RECORDS:
        assert record+'.PHASE_DERIVATION' in nodes[record+'.COEFFICIENT_DERIVATION']['parents']
        assert nodes[record+'.PHASE_DERIVATION']['operation']=='SOURCE_FEYNMAN_PHASES'
    assert packet['authority']['scientific_requalification']=='NOT_EARNED'
    assert packet['stage_dag']['complete_fine_grained_pass0280_dag'] is False
