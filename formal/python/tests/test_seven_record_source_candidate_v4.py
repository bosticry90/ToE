"""Component controls; deliberately not a replacement for the frozen gates."""
from copy import deepcopy

import pytest
import sympy as sp

from formal.python.toe.generic_runner import c03_source_derivation_v1 as c
from formal.python.toe.generic_runner import c03_native_projection_v1 as n
from formal.python.toe.generic_runner import rv_source_derivation_v1 as r
from formal.python.toe.generic_runner import seven_record_source_candidate_v4 as candidate


@pytest.fixture(scope='module')
def source(): return c.load_inputs()


@pytest.fixture(scope='module')
def native(): return n.load_inputs()


@pytest.fixture(scope='module')
def physical(source): return c.calculate(source)


@pytest.fixture(scope='module')
def rv_source(): return r.load_inputs()


@pytest.fixture(scope='module')
def rv(rv_source): return r.calculate(rv_source)


@pytest.fixture(scope='module')
def packet(): return candidate.compute()


def test_c03_derived_chain(physical):
    assert physical['weights']['grassmann']==physical['weights']['color']==-1
    assert physical['weights']['IDENTICAL_UR_EXCHANGE']==1
    num=physical['numerator']
    assert num['G_SUM']==sp.zeros(2,1) and num['L_SUM']==sp.ones(2,1)
    assert num['PT_SUM']==-sp.ones(2,1)
    assert sp.cancel(physical['common_kernel_coefficient']-(sp.Symbol('xi1')-1))==0
    assert physical['phase']['incidence']*physical['phase']['routing']==sp.zeros(3,1)


@pytest.mark.parametrize('path,value',[
    (('operator','normalization'),'UNSPECIFIED'),
    (('target','ordered_fields'),['dR','uR','eR','uR']),
    (('regularization','metric_signature'),'-+++'),
    (('fourier','path_integral_phase'),'exp(-i*S)'),
    (('target','fermionic_labeled_slot_orbit_size'),1),
    (('occurrences',0,'gamma_chains',0,'source_factors',0,'lorentz_slot'),'P_L'),
    (('occurrences',0,'gamma_chains',0,'chirality_projector'),'LEFT'),
    (('occurrences',0,'angular_average','pairing_terms',0,'exact_weight'),'2/d'),
    (('vertices',0,'generator_representation'),'1'),
    (('propagators',0,'rule'),'+i*slash(k)/(k^2-m^2-i*0)'),
])
def test_source_defects_fail_closed(source,path,value):
    bad=deepcopy(source)
    node=bad
    for key in path[:-1]: node=node[key]
    node[path[-1]]=value
    with pytest.raises(c.exact.VerificationError): c.calculate(bad)


def test_change_charge_propagates_at_fixed_reference(source,physical):
    bad=deepcopy(source)
    bad['fields'][0]['hypercharge']='-2/3'
    bad['vertices'][0]['generator_representation']='-2/3'
    bad['vertices'][0]['exact_rule']='+i*g1*gamma^mu*T_-2/3'
    result=c.calculate(bad)
    assert result['reference']==physical['reference']
    assert sp.cancel(result['common_kernel_coefficient']-2*physical['common_kernel_coefficient'])==0


def test_changed_gauge_vertex_phase_propagates(source,physical):
    bad=deepcopy(source)
    bad['vertices'][0]['exact_rule']=bad['vertices'][0]['exact_rule'].replace('+i*','-i*')
    result=c.calculate(bad)
    assert result['phase']['phase']==-physical['phase']['phase']
    assert sp.cancel(result['common_kernel_coefficient']+physical['common_kernel_coefficient'])==0


def test_old_exchange_sign_breaks_physical_target(source,physical):
    weights=deepcopy(physical['weights'])
    weights['IDENTICAL_UR_EXCHANGE']=sp.Integer(-1)
    with pytest.raises(c.exact.VerificationError,match='C03_NOT_SOURCE_TARGET_DIRECTION'):
        c.physical_numerator(source,weights)


def test_native_calculated_not_assigned(source,native,physical):
    result=n.calculate(source,native,physical)
    assert result['coordinates'].rows==14 and result['state']=='EVALUATED_NONZERO'
    assert result['xi1_equals_1_nonzero_count']==4
    assert result['physical_leakage']==0 and result['unexplained_residual']==sp.zeros(38,1)
    assert any(row['stored_external_sign']!=row['recomputed_external_sign'] for row in result['occurrence_coefficients'])


def test_old_exchange_sign_recreates_native_false_zero(source,native,physical):
    changed=deepcopy(physical)
    changed['weights']['IDENTICAL_UR_EXCHANGE']=sp.Integer(-1)
    result=n.calculate(source,native,changed)
    assert result['coordinates']==sp.zeros(14,1)
    assert result['state']=='EVALUATED_ZERO'


@pytest.mark.parametrize('part', ['dual','representative','remainder','relations'])
def test_native_matrix_tampering_rejected(source,native,physical,part):
    changed=deepcopy(native)
    changed[part]['entries'][0]['coefficient']='99'
    with pytest.raises(c.exact.VerificationError): n.calculate(source,changed,physical)


def test_native_definition_tampering_rejected(source,native,physical):
    changed=deepcopy(native)
    changed['defects'][0]['definition']='T_open(d)-(99)*Lift(Q_duue)'
    with pytest.raises(c.exact.VerificationError,match='DEFECT_DEFINITION_MISMATCH'): n.calculate(source,changed,physical)


def test_native_honors_exact_source_weights(source,native,physical):
    changed=deepcopy(source)
    changed['occurrences'][0]['exact_coefficient']='999'
    with pytest.raises(c.exact.VerificationError,match='LEGACY_COEFFICIENT_DECOMPOSITION'): n.calculate(changed,native,physical)


@pytest.mark.parametrize('text', ['__import__("os")','sqrt(-1)','sqrt(101)','sqrt(2,3)','1/0','a','1.5','2**100'])
def test_radical_parser_capability_rejection(text):
    with pytest.raises(c.exact.VerificationError): r.radical(text)


def test_rv_source_values(rv):
    g1,g2,g3,x1,x2,x3=sp.symbols('g1 g2 g3 xi1 xi2 xi3')
    expected=[-g3**2*(x3+3)/3,2*g3**2*(x3+3)/3,-g2**2*(x2+3)/4,g1**2*(x1+3)/12,2*g3**2*(x3+3)/3,g1**2*(x1+3)/9]
    for row,value in zip(rv,expected):
        assert sp.cancel(row['physical_coefficient']-value)==0
        assert row['normalization']['output']==row['physical_coefficient']
        assert row['evanescent']['state']=='EVALUATED_ZERO' and row['evanescent']['evaluated'] is True
    assert rv[2]['group_receipt']['channel']=='WEAK_TRIPLET_A_FLAVOR'


def test_rv03_wrong_channel_source_rejected(rv_source):
    bad=deepcopy(rv_source['records'][2])
    bad['source']['operator']=bad['source']['operator'].replace('+H_dagger_j','-H_dagger_j')
    with pytest.raises(c.exact.VerificationError,match='NONABELIAN_SOURCE_CHANNEL_UNSUPPORTED'): r.group_action(bad)


def test_c03_absence_domain_rejected(rv_source):
    profile=dict(touched_spinor_chains=2,current_count=2,fermion_propagators=2,source_derivatives=0,target_derivatives=0)
    with pytest.raises(c.exact.VerificationError,match='ABSENCE_DOMAIN_REJECTED'): r.absence_certificate(profile,rv_source)


@pytest.mark.parametrize('index',range(6))
def test_rv_derivative_mutation_rejected(rv_source,index):
    bad=deepcopy(rv_source['records'][index])
    bad['topology']['source_derivative_count']=1
    with pytest.raises(c.exact.VerificationError,match='RV_DERIVATIVE_DOMAIN'): r.domain(bad)


def test_rv06_charge_mutation_changes_result(rv_source,rv):
    bad=deepcopy(rv_source)
    row=bad['records'][5]
    row['fields'][0]['hypercharge']='0'
    row['vertices'][0]['generator_representation']='0'
    row['vertices'][0]['exact_rule']='+i*g1*gamma^mu*T_0'
    outputs=r.calculate(bad)
    assert outputs[5]['physical_coefficient']==0 and rv[5]['physical_coefficient']!=0
    assert outputs[:5]==rv[:5]


def test_packet_has_all_roots_but_withholds_full_dag_claim(packet):
    assert len(packet['authoritative_outputs'])==16 and len(packet['records'])==7
    assert packet['stage_dag']['complete_fine_grained_pass0280_dag'] is False
    assert packet['authority']['scientific_requalification']=='NOT_EARNED'
    assert packet['authority']['activation'] is False


def test_packet_recomputation_rejects_forged_zero(packet):
    bad=deepcopy(packet)
    bad['authoritative_outputs']['RV01.OUTPUT.EVANESCENT_STATE']='NOT_EVALUATED'
    with pytest.raises(c.exact.VerificationError,match='SOURCE_RECOMPUTATION_MISMATCH'): candidate.verify(bad)


def test_c03_receipt_recomputation_rejects_hidden_plus_four(source,physical):
    bad=c.serial(physical)
    bad['common_kernel_coefficient']='xi1+3'
    with pytest.raises(c.exact.VerificationError,match='C03_RECOMPUTATION_MISMATCH'): c.check_receipt(source,bad)
