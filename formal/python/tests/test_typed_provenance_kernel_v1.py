"""Executable unit controls, not seven-record scientific acceptance receipts."""
from __future__ import annotations
import copy
import hashlib
import json
from pathlib import Path

import pytest

from formal.python.toe.generic_runner.typed_provenance_kernel_v1 import (
    ProvenanceError, SourceStore, node_digest, scalar, source_pointer, strict_json, verify,
)


def node(identity, kind, operation, value, parents=(), evidence=(), semantic_type='SYMBOLIC_COEFFICIENT'):
    result = dict(node_id=identity, kind=kind, semantic_type=semantic_type, operation=operation,
                  typed_value=value, parents=list(parents), evidence_refs=list(evidence),
                  operation_parameters={}, domain_status='IN_DOMAIN', epistemic_status='DERIVED')
    result['recomputation_digest'] = node_digest(result)
    return result


def setup_graph(tmp_path):
    raw = b'{"inputs":{"charge":"2/3","gauge":"xi"},"scales":{"map":"3/2"}}'
    (tmp_path / 'source.json').write_bytes(raw)
    sha = hashlib.sha256(raw).hexdigest()
    store = SourceStore(tmp_path, {'allowed_inputs': [dict(path='source.json', byte_size=len(raw), sha256=sha)]})
    def source(identity, value, pointer):
        return node(identity, 'SOURCE_FACT', 'SOURCE_DECODE', value,
                    evidence=[dict(artifact_path='source.json', artifact_sha256=sha, semantic_locator=pointer)])
    nodes = [source('S.charge', '2/3', '/inputs/charge'), source('S.gauge', 'xi', '/inputs/gauge'),
             source('S.scale', '3/2', '/scales/map'),
             node('D.raw', 'DERIVED_FACT', 'PRODUCT', '2*xi/3', ['S.charge','S.gauge']),
             node('D.normalized', 'NORMALIZATION_MAP', 'INVERTIBLE_NORMALIZATION', 'xi', ['D.raw','S.scale']),
             node('R.coefficient', 'OUTPUT_ROOT', 'OUTPUT_BIND', 'xi', ['D.normalized'])]
    payload = dict(provenance_dag=dict(nodes=nodes, edges=[[p,n['node_id']] for n in nodes for p in n['parents']]),
                   outputs={'coefficient':'xi'}, output_bindings={'R.coefficient':'/outputs/coefficient'})
    profile = dict(node_schema={'required_fields':[k for k in nodes[0] if k != 'operation_parameters']},
                   allowed_node_kinds=['SOURCE_FACT','DERIVED_FACT','NORMALIZATION_MAP','OUTPUT_ROOT'],
                   allowed_operations=['SOURCE_DECODE','PRODUCT','INVERTIBLE_NORMALIZATION','OUTPUT_BIND'],
                   output_roots_required=['R.coefficient'], output_bindings=payload['output_bindings'].copy())
    return payload, profile, store


def rehash(payload):
    for n in payload['provenance_dag']['nodes']: n['recomputation_digest'] = node_digest(n)


def rejects(payload, profile, store, code):
    with pytest.raises(ProvenanceError, match=code): verify(payload, profile, store)


def test_positive_graph_recomputes_each_intermediate(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    result = verify(p, profile, source)
    assert result['recomputed_nodes'] == 6 and result['roots'] == 1
    assert result['receipts'][-1]['computed_value'] == 'xi'
    assert result['full_physics_profile_qualification'] is False


def test_false_intermediate_cannot_hide_behind_correct_final_value(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['provenance_dag']['nodes'][3]['typed_value'] = '999*xi'
    rehash(p)
    rejects(p, profile, source, 'RECOMPUTATION_MISMATCH:D.raw')


def test_unknown_operation_is_not_accepted_by_its_name_or_digest(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['provenance_dag']['nodes'][3]['operation'] = 'UNDECLARED_TARGET_LOOKUP'
    rehash(p)
    rejects(p, profile, source, 'UNKNOWN_OPERATION')


def test_known_but_unimplemented_physics_operation_fails_closed(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    profile['allowed_operations'].append('EXACT_CLIFFORD_ACTION')
    p['provenance_dag']['nodes'][3]['operation'] = 'EXACT_CLIFFORD_ACTION'
    rehash(p)
    rejects(p, profile, source, 'INDEPENDENT_OPERATION_NOT_IMPLEMENTED')


def test_nonexistent_source_locator_rejected(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['provenance_dag']['nodes'][0]['evidence_refs'][0]['semantic_locator'] = '/review/nonexistent/source/field'
    rehash(p)
    rejects(p, profile, source, 'SOURCE_LOCATOR_NOT_FOUND')


def test_existing_wrong_source_field_rejected(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['provenance_dag']['nodes'][0]['evidence_refs'][0]['semantic_locator'] = '/scales/map'
    rehash(p)
    rejects(p, profile, source, 'RECOMPUTATION_MISMATCH')


def test_changed_parents_with_unchanged_edges_rejected(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['provenance_dag']['nodes'][-1]['parents'] = ['S.gauge']
    rehash(p)
    rejects(p, profile, source, 'PARENT_EDGE_DISAGREEMENT')


def test_matching_edges_do_not_authorize_bypassing_mandatory_derivation(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    profile['c03_physical_required_dag'] = {'nodes': [], 'edges': [['D.normalized','R.coefficient']]}
    p['provenance_dag']['nodes'][-1]['parents'] = ['S.gauge']
    p['provenance_dag']['edges'][-1] = ['S.gauge','R.coefficient']
    rehash(p)
    rejects(p, profile, source, 'MANDATORY_EDGE_ABSENT')


def test_unit_scale_parent_cannot_bind_nonunit_coefficient(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['provenance_dag']['nodes'][-2]['typed_value'] = '1'
    rehash(p)
    rejects(p, profile, source, 'RECOMPUTATION_MISMATCH:D.normalized')


def test_emitted_value_checked_independently_of_dag(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['outputs']['coefficient'] = 'xi+4'
    rejects(p, profile, source, 'EMITTED_ROOT_MISMATCH')


def test_candidate_cannot_redirect_output_binding(tmp_path):
    p, profile, source = setup_graph(tmp_path)
    p['outputs']['hidden'] = 'xi'
    p['output_bindings']['R.coefficient'] = '/outputs/hidden'
    rejects(p, profile, source, 'UNAUTHORIZED_PAYLOAD_BINDING')


def test_source_sensitivity_recomputes_actual_graph(tmp_path):
    p, profile, store = setup_graph(tmp_path)
    path = tmp_path / 'source.json'
    content = json.loads(path.read_text())
    content['inputs']['charge'] = '4/3'
    raw = json.dumps(content).encode()
    path.write_bytes(raw)
    sha = hashlib.sha256(raw).hexdigest()
    changed_store = SourceStore(tmp_path, {'allowed_inputs':[dict(path='source.json',byte_size=len(raw),sha256=sha)]})
    for n in p['provenance_dag']['nodes']:
        for e in n['evidence_refs']: e['artifact_sha256'] = sha
    p['provenance_dag']['nodes'][0]['typed_value'] = '4/3'
    rehash(p)
    rejects(p, profile, changed_store, 'RECOMPUTATION_MISMATCH:D.raw')
    for i, value in ((3,'4*xi/3'),(4,'2*xi'),(5,'2*xi')):
        p['provenance_dag']['nodes'][i]['typed_value'] = value
    p['outputs']['coefficient'] = '2*xi'
    rehash(p)
    assert verify(p, profile, changed_store)['receipts'][-1]['computed_value'] == '2*xi'


@pytest.mark.parametrize('value', ["__import__('os').system('x')", 'x.real', 'f(x)', '~0',
                                  '[x][0]', '2**1000000', '1/0', '0.5', 'True'])
def test_symbolic_input_is_not_executed_or_silently_coerced(value):
    with pytest.raises(ProvenanceError): scalar(value)


@pytest.mark.parametrize('pointer', ['/missing','/a/00','/a/-1','/a/-','/a/9','/bad~2escape'])
def test_json_pointer_boundary(pointer):
    with pytest.raises(ProvenanceError): source_pointer({'a':[1,2]}, pointer)


def test_json_pointer_escaped_tokens_and_zero_index():
    assert source_pointer({'a/b': {'x~y':[7]}}, '/a~1b/x~0y/0') == 7


def test_duplicate_json_keys_rejected():
    with pytest.raises(ProvenanceError): strict_json(b'{"x":1,"x":2}')


@pytest.mark.parametrize('change', ['duplicate_node','duplicate_edge','cycle','decorative','missing_parent'])
def test_graph_structure_guards(tmp_path, change):
    p, profile, source = setup_graph(tmp_path)
    nodes, edges = p['provenance_dag']['nodes'], p['provenance_dag']['edges']
    if change == 'duplicate_node': nodes.append(copy.deepcopy(nodes[0]))
    elif change == 'duplicate_edge': edges.append(edges[0].copy())
    elif change == 'cycle':
        nodes[3]['parents'].append('R.coefficient'); edges.append(['R.coefficient','D.raw'])
    elif change == 'decorative':
        extra = copy.deepcopy(nodes[0]); extra['node_id'] = 'S.decorative'; nodes.append(extra)
    else:
        nodes[3]['parents'].append('missing'); edges.append(['missing','D.raw'])
    rehash(p)
    with pytest.raises(ProvenanceError): verify(p, profile, source)
