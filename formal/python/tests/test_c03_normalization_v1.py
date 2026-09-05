"""Normalization component controls; no seven-record requalification claim."""
import copy
import hashlib

import pytest
import sympy as sp

from formal.python.toe.generic_runner import c03_normalization_v1 as n


@pytest.fixture(scope='module')
def bound_inputs():
    return n.load_inputs()


def test_existing_allowed_source_decodes_without_comparison(bound_inputs):
    ref=n.derive_reference(bound_inputs)
    assert n.verify_reference(bound_inputs,ref)['generic_round_trip_residuals']==['0','0']
    assert ref['reference_scalar']=='-1/3' and ref['raw_to_common_scale']=='-3'
    assert len(bound_inputs['repeated_prefactors'])==32
    contract,profile=n.load_contract()
    assert len(profile['allowed_inputs'])==21 and profile['added_scientific_inputs']==[]
    assert profile['comparison_oracle_read_allowed'] is False
    assert bound_inputs['source_refs']['prefactor']['semantic_locator']=='/common_prefactor_factored'


def test_receipt_has_derived_scale_not_fictitious_source():
    receipt=n.receipt()
    nodes={node['node_id']:node for node in receipt['normalization_fragment']['nodes']}
    assert 'C03.SOURCE.TARGET_NORMALIZATION' not in nodes
    scale=nodes['C03.DERIVED.TARGET_NORMALIZATION_SCALE']
    assert scale['kind']=='NORMALIZATION_MAP' and scale['parents']==['C03.DERIVED.REFERENCE_SCALAR']
    assert nodes['C03.SOURCE.COUPLING_MONOMIAL']['evidence']['semantic_locator'].endswith('/coupling_monomial')
    assert receipt['scientific_requalification'] is False and receipt['raw_physics_derived'] is False


@pytest.mark.parametrize('field', ['reference_scalar','raw_to_common_scale','common_to_raw_scale','removed_monomial','source_prefactor'])
def test_forged_reference_receipt_rejected(bound_inputs,field):
    ref=n.derive_reference(bound_inputs)
    ref[field]='999'
    with pytest.raises(n.exact.VerificationError,match='RECOMPUTATION_MISMATCH'):
        n.verify_reference(bound_inputs,ref)


@pytest.mark.parametrize('change,code',[
    ('zero','NONINVERTIBLE'),('symbolic_remainder','NONINVERTIBLE'),('extra_term','NONINVERTIBLE'),
    ('bad_occurrence','INCONSISTENT_RECORDED'),('empty_occurrences','SOURCE_OCCURRENCE_SET_EMPTY'),
    ('wrong_operator','WRONG_OPERATOR'),('derivative','DERIVATIVE_DOMAIN'),('boolean_derivative','DERIVATIVE_DOMAIN'),
    ('wrong_loop','TOPOLOGY_DOMAIN'),('false_1pi','TOPOLOGY_DOMAIN'),('mixed_gauge','GAUGE_SYMBOL'),
    ('wrong_gauge_count','GAUGE_MONOMIAL'),('non_symbol_gauge','GAUGE_SYMBOL'),('non_symbol_wilson','WILSON_SYMBOL'),
])
def test_decoded_input_mutations_fail_closed(bound_inputs,change,code):
    inputs=copy.deepcopy(bound_inputs)
    t=inputs['topology']
    if change in ('zero','symbolic_remainder','extra_term'):
        expr={'zero':'0','symbolic_remainder':'g1**2*C_duue*x','extra_term':'g1**2*C_duue+1'}[change]
        inputs['prefactor']=expr
        for row in inputs['repeated_prefactors']: row['expression']=expr
    elif change=='bad_occurrence': inputs['repeated_prefactors'][0]['expression']='g1**2*C_duue'
    elif change=='empty_occurrences': inputs['repeated_prefactors']=[]
    elif change=='wrong_operator': t['source_insertion_id']='unrelated'
    elif change=='derivative': t['target_derivative_count']=7
    elif change=='boolean_derivative': t['source_derivative_count']=False
    elif change=='wrong_loop': t['loop_count']=2
    elif change=='false_1pi': t['one_particle_irreducible']=False
    elif change=='mixed_gauge': t['coupling_monomial']=['g1','g2']
    elif change=='wrong_gauge_count': t['coupling_monomial']=['g1']
    elif change=='non_symbol_gauge': t['coupling_monomial']=['1','1']
    elif change=='non_symbol_wilson': inputs['wilson_symbol']='1'
    with pytest.raises(n.exact.VerificationError,match=code): n.derive_reference(inputs)


def test_fixed_reference_sensitivity_does_not_cancel_raw_change(bound_inputs):
    ref=n.derive_reference(bound_inputs)
    baseline=n.map_raw('R',bound_inputs,ref)
    changed=n.map_raw('2*R',bound_inputs,ref)
    assert sp.cancel(changed-2*baseline)==0 and sp.cancel(changed-baseline)!=0


def test_explicit_reference_change_has_disclosed_different_dependency(bound_inputs):
    """Decoded-input experiment, not an authorized new physics source."""
    changed=copy.deepcopy(bound_inputs)
    changed['prefactor']='2*('+changed['prefactor']+')'
    for row in changed['repeated_prefactors']: row['expression']=changed['prefactor']
    old=n.derive_reference(bound_inputs)
    new=n.derive_reference(changed)
    assert old['reference_scalar']!=new['reference_scalar']
    assert old['raw_to_common_scale']!=new['raw_to_common_scale']
    assert sp.cancel(n.map_raw('2*R',changed,new)-n.map_raw('R',bound_inputs,old))==0


def test_unbound_current_charge_fields_do_not_modify_reference(bound_inputs):
    altered=copy.deepcopy(bound_inputs)
    altered['current_hypercharges']={'dR':'-2/3','eR':'-1'}
    assert n.derive_reference(altered)==n.derive_reference(bound_inputs)
    # This is a normalization-only statement. The full runner must independently
    # propagate/validate action changes when it derives R.


def test_profile_tampering_rejected(tmp_path):
    path=tmp_path/n.PROFILE_PATH
    path.parent.mkdir(parents=True)
    path.write_text('{}')
    with pytest.raises(n.exact.VerificationError,match='PROFILE_HASH'): n.load_inputs(tmp_path)


def test_source_hash_tampering_rejected(tmp_path,bound_inputs):
    contract,profile=n.load_contract()
    (tmp_path/n.PROFILE_PATH).parent.mkdir(parents=True)
    (tmp_path/n.PROFILE_PATH).write_bytes((n.ROOT/n.PROFILE_PATH).read_bytes())
    for row in (profile['contract'],profile['parent_allowlist']):
        path=tmp_path/row['path']
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes((n.ROOT/row['path']).read_bytes())
    row=contract['source_bindings']['universe']
    path=tmp_path/row['path']
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text('{}')
    with pytest.raises(n.exact.VerificationError,match='SOURCE_HASH_MISMATCH'): n.load_inputs(tmp_path)


def test_decoder_module_has_no_record_answer_or_old_runner_import():
    import ast
    path=n.ROOT/'formal/python/toe/generic_runner/c03_normalization_v1.py'
    tree=ast.parse(path.read_text())
    imports=[node.module for node in ast.walk(tree) if isinstance(node,ast.ImportFrom)]
    assert not any(x and ('strict_model1_seven_record_semantic_runner' in x or 'acceptance_tests' in x) for x in imports)
    # Narrow dependency inventory, not a claimed whole-program anti-oracle proof.


def test_algebraically_equivalent_prefactor_decodes_identically(bound_inputs):
    altered=copy.deepcopy(bound_inputs)
    altered['prefactor']='(-C_duue*g1*g1)/3'
    assert n.derive_reference(altered)==n.derive_reference(bound_inputs)


def test_composite_preserves_other_scientific_requirements():
    contract,profile=n.load_contract()
    parent=n.exact.read_json((n.ROOT/contract['parent_dag_contract']['path']).read_bytes())
    composite=n.exact.read_json((n.ROOT/n.AREA/'effective_normalization_dag_contract_v1.json').read_bytes())
    assert composite['output_roots_required']==parent['output_roots_required']
    assert len(composite['output_roots_required'])==16
    assert composite['dag_checks']==parent['dag_checks']
    old={x['node_id']:x for x in parent['c03_physical_required_dag']['nodes']}
    new={x['node_id']:x for x in composite['c03_physical_required_dag']['nodes']}
    for key,value in old.items():
        if key!='C03.SOURCE.TARGET_NORMALIZATION': assert new[key]==value
    assert 'C03.SOURCE.TARGET_NORMALIZATION' not in new
    assert composite['role']=='COMPARISON_SIDE_ACCEPTANCE_CONTRACT_NOT_CANDIDATE_SCIENTIFIC_INPUT'
    allowed={r['path'] for r in profile['allowed_inputs']}
    assert n.AREA+'/effective_normalization_dag_contract_v1.json' not in allowed


def test_changed_scalar_and_inverse_cannot_be_laundered_together(bound_inputs):
    receipt=n.derive_reference(bound_inputs)
    receipt['reference_scalar']='-2/3'
    receipt['common_to_raw_scale']='-2/3'
    receipt['raw_to_common_scale']='-3/2'
    with pytest.raises(n.exact.VerificationError,match='RECOMPUTATION_MISMATCH'):
        n.map_raw('R',bound_inputs,receipt)
