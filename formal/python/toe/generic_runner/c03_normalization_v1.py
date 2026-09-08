"""Source-recorded C03 reference normalization; no scientific target calculator.

This decoder never reads the comparison oracle or imports the old runner. It
extracts a reference scale from an already admitted common-prefactor field.
Raw coefficient derivation and full-runner qualification remain separate.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

import sympy as sp

from formal.python.meta.repo_environment import find_repo_root
from formal.python.toe.generic_runner import provenance_verifier_v4 as exact

ROOT = find_repo_root(Path(__file__))
AREA = 'formal/docs/research/project_situation_audit_20260904/c03_normalization_amendment_v1'
PROFILE_PATH = AREA+'/source_profile_v1.json'
PROFILE_HASH = '6ba34bcfd572d50842d32cb3995dca131f8aba153597fadbd06b09ca0e8af2c9'
CONTRACT_HASH = '646503046f4ab3fc0dd7109964cd8a47eb4b68ee38bab1bc7e2d4988c45372fa'
require = exact.require


def text(value):
    return sp.sstr(sp.cancel(value))


def _bound_file(root, row):
    relative = row['path']
    require(type(relative) is str and ':' not in relative and '\\' not in relative and '..' not in Path(relative).parts,
            'NORMALIZATION_PROFILE_PATH')
    path = (root/relative).resolve(strict=True)
    require(root.resolve() in path.parents,'NORMALIZATION_PROFILE_ESCAPE')
    raw = path.read_bytes()
    require(len(raw)==row['byte_size'] and hashlib.sha256(raw).hexdigest()==row['sha256'], 'NORMALIZATION_INPUT_HASH')
    return exact.read_json(raw)


def load_contract(root=ROOT):
    root = Path(root)
    raw = (root/PROFILE_PATH).read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PROFILE_HASH,'NORMALIZATION_PROFILE_HASH')
    profile = exact.read_json(raw)
    require(profile['contract']['sha256']==CONTRACT_HASH,'NORMALIZATION_CONTRACT_HASH')
    contract = _bound_file(root,profile['contract'])
    parent = _bound_file(root,profile['parent_allowlist'])
    require(exact.canonical(parent['allowed_inputs'])==exact.canonical(profile['allowed_inputs']), 'SOURCE_ALLOWLIST_CHANGED')
    require(profile['added_scientific_inputs']==[] and profile['removed_scientific_inputs']==[], 'SCIENTIFIC_INPUT_EXPANSION')
    require(contract['reference_policy']['id']=='FIXED_SOURCE_RECORDED_PREFACTOR', 'REFERENCE_POLICY_MISMATCH')
    return contract,profile


def load_inputs(root=ROOT):
    contract,profile = load_contract(root)
    sources = exact.BoundSources(root,profile['allowed_inputs'])
    def resolve(label,pointer):
        binding = contract['source_bindings'][label]
        evidence = dict(artifact_path=binding['path'],artifact_sha256=binding['sha256'],semantic_locator=pointer)
        value = sources.resolve(evidence)
        return value,evidence
    prefactor,prefactor_ref = resolve('universe',contract['semantic_locators']['prefactor'])
    topology,topology_ref = resolve('topologies',contract['semantic_locators']['topology'])
    coupling_monomial,coupling_ref = resolve('topologies',contract['semantic_locators']['topology']+'/coupling_monomial')
    require(coupling_monomial==topology['coupling_monomial'],'SOURCE_COUPLING_DECODE_MISMATCH')
    occurrences,occurrences_ref = resolve('universe','/typed_tensor_occurrences')
    for key in ('disputed_projection_consumed','four_dimensional_projection_performed'):
        flag,_ = resolve('universe','/'+key)
        require(flag is False, 'SOURCE_PROJECTION_ADMISSION', key)
    require(type(occurrences) is list and len(occurrences)>0, 'SOURCE_OCCURRENCE_SET_EMPTY')
    repeated=[]
    ids=[]
    for index,row in enumerate(occurrences):
        require(type(row) is dict and 'occurrence_id' in row and 'factored_scientific_prefactors' in row,
                'SOURCE_OCCURRENCE_SCHEMA')
        ids.append(row['occurrence_id'])
        require(type(ids[-1]) is str,'SOURCE_OCCURRENCE_ID')
        repeated.append(dict(pointer='/typed_tensor_occurrences/'+str(index)+'/factored_scientific_prefactors/common',
                             expression=row['factored_scientific_prefactors']['common']))
    require(len(set(ids))==len(ids),'DUPLICATE_SOURCE_OCCURRENCE')
    return dict(prefactor=prefactor,topology=topology,repeated_prefactors=repeated,
                wilson_symbol=contract['reference_policy']['wilson_symbol'],
                source_refs=dict(prefactor=prefactor_ref,topology=topology_ref,coupling_monomial=coupling_ref,occurrences=occurrences_ref),
                field_reads=sources.read_receipts,contract_sha256=CONTRACT_HASH,profile_sha256=PROFILE_HASH)


def _input_shape(inputs):
    topology = inputs['topology']
    require(topology['source_insertion_id']=='D6-PSI4-DUUE','NORMALIZATION_WRONG_OPERATOR')
    require(type(topology['source_derivative_count']) is int and type(topology['target_derivative_count']) is int and
            topology['source_derivative_count']==0 and topology['target_derivative_count']==0,
            'NORMALIZATION_DERIVATIVE_DOMAIN')
    require(type(topology['loop_count']) is int and topology['loop_count']==1 and topology['one_particle_irreducible'] is True,
            'NORMALIZATION_TOPOLOGY_DOMAIN')
    gauge = topology['coupling_monomial']
    require(type(gauge) is list and len(gauge)==2 and all(type(g) is str for g in gauge),'NORMALIZATION_GAUGE_MONOMIAL')
    symbols = [exact.exact_expr(g) for g in gauge]
    require(all(isinstance(g,sp.Symbol) for g in symbols) and symbols[0]==symbols[1], 'NORMALIZATION_GAUGE_SYMBOL')
    wilson = exact.exact_expr(inputs['wilson_symbol'])
    require(isinstance(wilson,sp.Symbol) and wilson not in symbols,'NORMALIZATION_WILSON_SYMBOL')
    require(type(inputs['repeated_prefactors']) is list and len(inputs['repeated_prefactors'])>0,'SOURCE_OCCURRENCE_SET_EMPTY')
    return symbols,wilson


def derive_reference(inputs):
    """Pure decoded-input calculation; altered dictionaries are test inputs,
    not a bypass of load_inputs' source-admission hashes.
    """
    symbols,wilson = _input_shape(inputs)
    prefactor = exact.exact_expr(inputs['prefactor'])
    for row in inputs['repeated_prefactors']:
        require(sp.cancel(exact.exact_expr(row['expression'])-prefactor)==0, 'INCONSISTENT_RECORDED_PREFACTOR', row['pointer'])
    gauge_monomial = sp.prod(symbols)
    removed = gauge_monomial*wilson
    scalar = sp.cancel(prefactor/removed)
    require(scalar.is_Rational is True and scalar!=0, 'NONINVERTIBLE_OR_SYMBOL_DEPENDENT_REFERENCE')
    scale = sp.cancel(1/scalar)
    require(sp.cancel(scale*scalar-1)==0,'NORMALIZATION_INVERSE_MISMATCH')
    return dict(source_prefactor=text(prefactor),gauge_monomial=text(gauge_monomial),wilson_symbol=text(wilson),
                removed_monomial=text(removed),reference_scalar=text(scalar),raw_to_common_scale=text(scale),
                common_to_raw_scale=text(scalar),reference_policy='FIXED_SOURCE_RECORDED_PREFACTOR')


def verify_reference(inputs, reference):
    """Complementary polynomial coefficient extraction, not an oracle check.
    Both implementations are author-lineage code; this is not external review.
    """
    _input_shape(inputs)
    topology = inputs['topology']
    coupling_names = topology['coupling_monomial']
    c = exact.exact_expr(coupling_names[0])
    w = exact.exact_expr(inputs['wilson_symbol'])
    require(len(coupling_names)==2 and coupling_names[0]==coupling_names[1] and isinstance(c,sp.Symbol) and isinstance(w,sp.Symbol) and c!=w,
            'POLYNOMIAL_REFERENCE_PROFILE')
    expr = exact.exact_expr(inputs['prefactor'])
    try:
        polynomial = sp.Poly(expr,c,w,domain=sp.QQ)
    except (sp.PolynomialError,sp.CoercionFailed) as exc:
        raise exact.VerificationError('POLYNOMIAL_REFERENCE_DOMAIN') from exc
    require(polynomial.monoms()==[(2,1)],'REFERENCE_NOT_SINGLE_DECLARED_MONOMIAL')
    coefficient = polynomial.coeff_monomial(c**2*w)
    require(coefficient!=0,'NONINVERTIBLE_REFERENCE')
    for row in inputs['repeated_prefactors']:
        require(sp.cancel(exact.exact_expr(row['expression'])-expr)==0,'INCONSISTENT_RECORDED_PREFACTOR')
    expected = dict(source_prefactor=text(expr),gauge_monomial=text(c**2),wilson_symbol=text(w),removed_monomial=text(c**2*w),
                    reference_scalar=text(coefficient),raw_to_common_scale=text(1/coefficient),common_to_raw_scale=text(coefficient),
                    reference_policy='FIXED_SOURCE_RECORDED_PREFACTOR')
    require(exact.canonical(reference)==exact.canonical(expected),'NORMALIZATION_RECEIPT_RECOMPUTATION_MISMATCH')
    r,k = sp.symbols('RAW_INPUT KERNEL_INPUT')
    forward = exact.arithmetic('INVERTIBLE_NORMALIZATION',[r,1/coefficient,coefficient])
    inverse = exact.arithmetic('INVERTIBLE_NORMALIZATION',[k,coefficient,1/coefficient])
    residuals=[sp.cancel(inverse.subs(k,forward)-r),sp.cancel(forward.subs(r,inverse)-k)]
    require(residuals==[0,0],'NORMALIZATION_ROUND_TRIP_FAILURE')
    return dict(method='EXACT_POLYNOMIAL_COEFFICIENT_CROSSCHECK_AND_SYMBOLIC_INVERSES',
                status='PASS_NORMALIZATION_MAP_ONLY',generic_round_trip_residuals=[text(x) for x in residuals])


def map_raw(raw, inputs, reference):
    verify_reference(inputs,reference)
    return exact.arithmetic('INVERTIBLE_NORMALIZATION',[exact.exact_expr(raw),
        exact.exact_expr(reference['raw_to_common_scale']),exact.exact_expr(reference['common_to_raw_scale'])])


def receipt(root=ROOT):
    inputs = load_inputs(root)
    reference = derive_reference(inputs)
    verified = verify_reference(inputs,reference)
    nodes = [
        dict(node_id='C03.SOURCE.COMMON_PREFACTOR',kind='SOURCE_FACT',operation='SOURCE_DECODE',parents=[],
             value=reference['source_prefactor'],evidence=inputs['source_refs']['prefactor']),
        dict(node_id='C03.SOURCE.COUPLING_MONOMIAL',kind='SOURCE_FACT',operation='SOURCE_DECODE',parents=[],
             value=inputs['topology']['coupling_monomial'],evidence=inputs['source_refs']['coupling_monomial']),
        dict(node_id='C03.CONVENTION.WILSON_SYMBOL',kind='DECLARED_NOTATION_CONVENTION',operation='CONTRACT_DECODE',parents=[],
             value=reference['wilson_symbol'],contract_sha256=CONTRACT_HASH,pointer='/reference_policy/wilson_symbol'),
        dict(node_id='C03.DERIVED.REMOVED_MONOMIAL',kind='DERIVED_FACT',operation='NORMALIZATION_MONOMIAL',
             parents=['C03.SOURCE.COUPLING_MONOMIAL','C03.CONVENTION.WILSON_SYMBOL'],value=reference['removed_monomial']),
        dict(node_id='C03.DERIVED.REFERENCE_SCALAR',kind='DERIVED_FACT',operation='NORMALIZATION_REFERENCE_SCALAR',
             parents=['C03.SOURCE.COMMON_PREFACTOR','C03.DERIVED.REMOVED_MONOMIAL'],value=reference['reference_scalar']),
        dict(node_id='C03.DERIVED.TARGET_NORMALIZATION_SCALE',kind='NORMALIZATION_MAP',operation='NORMALIZATION_RECIPROCAL',
             parents=['C03.DERIVED.REFERENCE_SCALAR'],value=reference['raw_to_common_scale']),
    ]
    return dict(schema_id='C03_NORMALIZATION_REFERENCE_RECEIPT_v1',status='SOURCE_REFERENCE_DECODED_AND_MAP_CHECKED',
        source_profile_sha256=PROFILE_HASH,contract_sha256=CONTRACT_HASH,reference=reference,verification=verified,
        normalization_fragment=dict(nodes=nodes,edges=[[p,n['node_id']] for n in nodes for p in n['parents']],
            required_downstream_inputs=['C03.DERIVED.RAW_GRAPH','C03.DERIVED.TARGET_NORMALIZATION_SCALE','C03.DERIVED.REFERENCE_SCALAR'],
            full_pass0280_dag=False),
        repeated_prefactor_fields_checked=len(inputs['repeated_prefactors']),source_field_reads=inputs['field_reads'],
        execution_scope='NORMALIZATION_COMPONENT_ONLY_NOT_SEVEN_RECORD_SOURCE_EXECUTION',
        source_access_claim='Bound helper-mediated reads; not OS-level complete I/O audit',
        raw_physics_derived=False,comparison_input_policy='FORBIDDEN__NOT_PART_OF_COMPONENT_INPUTS',
        complete_io_audit='NOT_PERFORMED',scientific_requalification=False,candidate_activation=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.parse_args()
    print(exact.canonical(receipt()))


if __name__=='__main__': main()
