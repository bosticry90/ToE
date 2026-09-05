"""Executable verifier tests; toy algebra is not seven-record requalification."""
import copy
import hashlib
import json

import pytest
import sympy as sp

from formal.python.toe.generic_runner import provenance_verifier_v4 as v


def seal(graph):
    for n in graph['nodes']:
        n['recomputation_digest'] = v.digest({k:x for k,x in n.items() if k!='recomputation_digest'}, 'PASS0281_PROVENANCE_NODE_v0')
    graph['node_count'], graph['edge_count'] = len(graph['nodes']), len(graph['edges'])
    graph['canonical_digest'] = v.digest(dict(nodes=graph['nodes'],edges=graph['edges']), 'PASS0281_DAG_v0')


@pytest.fixture
def sample(tmp_path):
    raw = json.dumps(dict(raw='x', scale='2', inverse='1/2', wrong_row=dict(scale='2'))).encode()
    (tmp_path/'source.json').write_bytes(raw)
    h = hashlib.sha256(raw).hexdigest()
    sources = v.BoundSources(tmp_path,[dict(path='source.json',byte_size=len(raw),sha256=h)])
    nodes = []
    def node(key,kind,semantic_type,value,parents,operation,pointer=None):
        nodes.append(dict(node_id=key,kind=kind,semantic_type=semantic_type,typed_value=value,parents=parents,
                          operation=operation,operation_parameters={},domain_status='IN_DOMAIN',
                          epistemic_status='SOURCE_GROUNDED' if kind=='SOURCE_FACT' else 'DERIVED',
                          evidence_refs=[] if pointer is None else [dict(artifact_path='source.json',artifact_sha256=h,semantic_locator=pointer)]))
    node('S.raw','SOURCE_FACT','SYMBOLIC_COEFFICIENT','x',[],'SOURCE_DECODE','/raw')
    node('S.scale','SOURCE_FACT','INVERTIBLE_SCALE','2',[],'SOURCE_DECODE','/scale')
    node('S.inverse','SOURCE_FACT','INVERTIBLE_SCALE','1/2',[],'SOURCE_DECODE','/inverse')
    node('N','NORMALIZATION_MAP','SYMBOLIC_COEFFICIENT','2*x',['S.raw','S.scale','S.inverse'],'INVERTIBLE_NORMALIZATION')
    node('O','OUTPUT_ROOT','SYMBOLIC_COEFFICIENT','2*x',['N'],'OUTPUT_BIND')
    graph = dict(nodes=nodes,edges=[[p,n['node_id']] for n in nodes for p in n['parents']])
    seal(graph)
    contract = dict(allowed_node_kinds=['SOURCE_FACT','NORMALIZATION_MAP','OUTPUT_ROOT','DERIVED_FACT'],
                    allowed_operations=['SOURCE_DECODE','INVERTIBLE_NORMALIZATION','OUTPUT_BIND','EXACT_CLIFFORD_ACTION'],
                    node_schema=dict(required_fields=list(nodes[0])),output_roots_required=['O'])
    return graph,contract,sources,{'O':'x+x'}


def test_supported_graph_evaluates_sources_parents_and_output(sample):
    result = v.evaluate_graph(*sample)
    assert result['status']=='PASS_SUPPORTED_EXACT_ALGEBRA_PROFILE_ONLY'
    assert len(result['receipts'])==5 and len(result['source_read_receipts'])==3
    assert result['scientific_requalification'] is False


@pytest.mark.parametrize('attack,code',[
    ('false_intermediate','RECOMPUTED_VALUE_MISMATCH'),
    ('wrong_inverse','RECOMPUTED_VALUE_MISMATCH'),
    ('unknown_operation','UNKNOWN_OPERATION'),
    ('undeclared_physics','OPERATION_NOT_IMPLEMENTED'),
    ('nonexistent_pointer','SOURCE_POINTER_MISSING'),
    ('row_as_scalar','EXPLICIT_SOURCE_DECODER_REQUIRED'),
    ('bypass_stale_edges','PARENT_EDGE_MISMATCH'),
    ('bypass_repaired_edges','DECORATIVE_OR_DISCONNECTED_NODE'),
    ('direct_output','OUTPUT_BIND_ARITY'),
    ('invented_parameter','OPERATION_PARAMETERS_REQUIRE_IMPLEMENTED_SIGNATURE'),
    ('no_source_binding','SOURCE_DECODE_SIGNATURE'),
    ('source_value_lie','RECOMPUTED_VALUE_MISMATCH'),
    ('source_hash_lie','SOURCE_HASH_MISMATCH'),
    ('duplicate_node','DUPLICATE_NODE_ID'),
    ('duplicate_parent','DUPLICATE_PARENT'),
    ('unknown_kind','UNKNOWN_NODE_KIND'),
    ('out_of_domain','NODE_OUT_OF_DOMAIN'),
    ('extra_edge','PARENT_EDGE_MISMATCH'),
    ('duplicate_edge','DUPLICATE_EDGE'),
    ('cycle','CYCLIC_GRAPH'),
    ('emitted_output_lie','EMITTED_VALUE_MISMATCH'),
    ('emitted_output_missing','EMITTED_ROOT_SET_MISMATCH'),
])
def test_semantic_mutations_reject(sample, attack, code):
    graph,contract,sources,output = sample
    n = {row['node_id']:row for row in graph['nodes']}
    if attack=='false_intermediate': n['N']['typed_value']='999'
    elif attack=='wrong_inverse': n['S.inverse']['typed_value']='1/3'
    elif attack=='unknown_operation': n['N']['operation']='UNDECLARED_TARGET_LOOKUP'
    elif attack=='undeclared_physics': n['N']['operation']='EXACT_CLIFFORD_ACTION'
    elif attack=='nonexistent_pointer': n['S.scale']['evidence_refs'][0]['semantic_locator']='/review/nonexistent/source/field'
    elif attack=='row_as_scalar': n['S.scale']['evidence_refs'][0]['semantic_locator']='/wrong_row'
    elif attack.startswith('bypass_'):
        n['O']['parents']=['S.raw']
        if attack=='bypass_repaired_edges': graph['edges']=[[p,row['node_id']] for row in graph['nodes'] for p in row['parents']]
    elif attack=='direct_output':
        # Keep N on the ancestry but provide two parents: not a value-preserving bind.
        n['O']['parents']=['N','S.raw']
        graph['edges'].append(['S.raw','O'])
    elif attack=='invented_parameter': n['N']['operation_parameters']={'scale':'2','inverse_verified':True}
    elif attack=='no_source_binding': n['S.raw']['evidence_refs']=[]
    elif attack=='source_value_lie': n['S.raw']['typed_value']='x+1'
    elif attack=='source_hash_lie': n['S.raw']['evidence_refs'][0]['artifact_sha256']='0'*64
    elif attack=='duplicate_node': graph['nodes'].append(copy.deepcopy(n['S.raw']))
    elif attack=='duplicate_parent': n['N']['parents'].append('S.raw')
    elif attack=='unknown_kind': n['N']['kind']='ORACLE_LOOKUP'
    elif attack=='out_of_domain': n['N']['domain_status']='UNKNOWN'
    elif attack=='extra_edge': graph['edges'].append(['S.raw','O'])
    elif attack=='duplicate_edge': graph['edges'].append(graph['edges'][0])
    elif attack=='cycle':
        n['S.raw']['parents']=['O']
        graph['edges'].append(['O','S.raw'])
    elif attack=='emitted_output_lie': output['O']='999'
    elif attack=='emitted_output_missing': output.clear()
    seal(graph)  # These are semantic attacks with honest fresh digests.
    with pytest.raises(v.VerificationError, match=code):
        v.evaluate_graph(graph,contract,sources,output)


@pytest.mark.parametrize('expr', ['__import__("os").system("echo unsafe")','x.__class__','x[0]','lambda: 1','~0','0.5','True','x**999','1/0'])
def test_expression_parser_does_not_execute_host_language(expr):
    with pytest.raises(v.VerificationError): v.exact_expr(expr)


def test_expression_symbolic_equivalence():
    assert v.exact_equal(v.exact_expr('x+x'),v.exact_expr('2*x'))
    assert not v.exact_equal(False,0)


@pytest.mark.parametrize('locator,code',[
    ('/rows[id=missing]','SOURCE_SELECTOR_NOT_UNIQUE'),
    ('/rows[id=A]/missing','SOURCE_POINTER_MISSING'),
    ('/rows/01','SOURCE_ARRAY_INDEX'),
    ('/rows/-1','SOURCE_ARRAY_INDEX'),
    ('/rows/5','SOURCE_POINTER_MISSING'),
    ('/rows;/other','COMPOUND_LOCATOR_REQUIRES_EXPLICIT_DECODER'),
    ('/a~9b','POINTER_ESCAPE'),
])
def test_locator_rejections(locator,code):
    with pytest.raises(v.VerificationError, match=code): v.resolve_locator({'rows':[{'id':'A'}]},locator)


def test_unique_selector_returns_canonical_pointer():
    assert v.resolve_locator({'rows':[{'id':'A','q':'-1/3'}]},'/rows[id=A]/q')==('-1/3','/rows/0/q')
    with pytest.raises(v.VerificationError, match='SOURCE_SELECTOR_NOT_UNIQUE'):
        v.resolve_locator({'rows':[{'id':'A'},{'id':'A'}]},'/rows[id=A]')
    assert v.resolve_locator({'a/b':{'c~d':1}},'/a~1b/c~0d')==(1,'/a~1b/c~0d')


def test_changed_source_bytes_rejected(sample):
    graph,contract,sources,output = sample
    (sources.root/'source.json').write_text('{}')
    with pytest.raises(v.VerificationError,match='SOURCE_HASH_MISMATCH'):
        v.evaluate_graph(*sample)


def test_duplicate_json_rejected():
    with pytest.raises(v.VerificationError,match='DUPLICATE_JSON_KEY'): v.read_json('{"a":1,"a":2}')
    with pytest.raises(v.VerificationError,match='NONFINITE_JSON'): v.read_json('{"a":NaN}')


def test_exact_algebra_operations():
    x = sp.Symbol('x')
    assert v.arithmetic('PRODUCT',[x,sp.Integer(2)])==2*x
    a,b = (sp.Integer(1),sp.Integer(0)),(sp.Integer(0),sp.Integer(1))
    assert v.arithmetic('TENSOR_SUM',[a,b])==(1,1)
    assert v.arithmetic('TENSOR_DIFFERENCE',[a,b])==(1,-1)
    assert v.arithmetic('LINEAR_COMBINATION',[sp.Integer(2),a,x,b])==(2,x)
    assert v.arithmetic('EXACT_MATRIX_PROJECTION',[sp.eye(2),a])==a
    assert v.arithmetic('PERMUTATION_PARITY',[(sp.Integer(1),sp.Integer(0))])==-1
    with pytest.raises(v.VerificationError,match='NORMALIZATION_INVERSE_MISMATCH'):
        v.arithmetic('INVERTIBLE_NORMALIZATION',[x,sp.Integer(2),sp.Integer(1)])


def test_output_parent_type_mismatch_even_when_values_equal(sample):
    graph,contract,sources,output = sample
    graph['nodes'][-2]['semantic_type']='INVERTIBLE_SCALE'
    graph['nodes'][-2]['typed_value']='2'
    graph['nodes'][0]['typed_value']='1'
    # Test the bind contract directly through graph with a source that resolves 1.
    raw = json.dumps(dict(raw='1',scale='2',inverse='1/2')).encode()
    (sources.root/'source.json').write_bytes(raw)
    h = hashlib.sha256(raw).hexdigest()
    sources.allowed['source.json'].update(byte_size=len(raw),sha256=h)
    for n in graph['nodes']:
        for e in n['evidence_refs']: e['artifact_sha256']=h
    graph['nodes'][-1]['typed_value']='2'
    output['O']='2'
    seal(graph)
    with pytest.raises(v.VerificationError,match='OUTPUT_BIND_TYPE_MISMATCH'): v.evaluate_graph(*sample)
