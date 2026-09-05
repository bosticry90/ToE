"""Fail-closed verifier kernel, not a scientifically qualified runner.

Unlike the v3 evidence checker, acceptance here requires evaluated parents,
resolved source values and exact operation signatures. Unsupported physics
operations raise an explicit error; they never inherit the claimed value.
No candidate, oracle or historical verifier is imported.
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from typing import Any

import sympy as sp


class VerificationError(ValueError):
    def __init__(self, code: str, detail: str = ''):
        self.code, self.detail = code, detail
        super().__init__(code + (': ' + detail if detail else ''))


def require(ok, code, detail=''):
    if not ok:
        raise VerificationError(code, detail)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False)


def digest(value, domain):
    return hashlib.sha256((domain+'\0'+canonical(value)).encode()).hexdigest()


def read_json(raw):
    def object_pairs(pairs):
        result = {}
        for k, v in pairs:
            require(k not in result, 'DUPLICATE_JSON_KEY', k)
            result[k] = v
        return result
    def nonfinite(value):
        raise VerificationError('NONFINITE_JSON', value)
    return json.loads(raw, object_pairs_hook=object_pairs, parse_constant=nonfinite)


def exact_expr(value):
    """Small non-eval expression grammar: integers, symbols and arithmetic."""
    require(type(value) in (int, str), 'EXACT_SCALAR_REQUIRED')
    text = str(value)
    require(len(text) <= 4096, 'EXPRESSION_SIZE_LIMIT')
    try:
        tree = ast.parse(text, mode='eval')
    except SyntaxError as exc:
        raise VerificationError('EXPRESSION_SYNTAX') from exc
    require(sum(1 for _ in ast.walk(tree)) <= 256, 'EXPRESSION_NODE_LIMIT')
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            require(node.value.bit_length() <= 256, 'INTEGER_SIZE_LIMIT')
            return sp.Integer(node.value)
        if isinstance(node, ast.Name):
            require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', node.id) is not None, 'SYMBOL_GRAMMAR')
            return sp.I if node.id == 'I' else sp.Symbol(node.id)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            result = visit(node.operand)
            return -result if isinstance(node.op, ast.USub) else result
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return a+b
            if isinstance(node.op, ast.Sub): return a-b
            if isinstance(node.op, ast.Mult): return a*b
            if isinstance(node.op, ast.Div):
                require(b != 0, 'ZERO_DENOMINATOR')
                return a/b
            if isinstance(node.op, ast.Pow):
                require(b.is_Integer is True and abs(int(b)) <= 8, 'POWER_DOMAIN')
                require(not (a == 0 and b < 0), 'ZERO_DENOMINATOR')
                return a**b
        raise VerificationError('EXPRESSION_CAPABILITY_FORBIDDEN', type(node).__name__)
    result = sp.cancel(visit(tree.body))
    require(not result.has(sp.zoo, sp.nan, sp.oo, -sp.oo), 'NONFINITE_EXPRESSION')
    return result


SCALARS = {'INTEGER','SIGN','RATIONAL','PHASE','SYMBOL','SYMBOLIC_SCALAR',
           'SYMBOLIC_COEFFICIENT','INVERTIBLE_SCALE'}
VECTORS = {'BASIS_VECTOR_XY','BASIS_TENSOR','PAIR_OF_RATIONALS',
           'SYMBOLIC_VECTOR_14','SYMBOLIC_VECTOR_38','SYMBOLIC_VECTOR'}
DIMENSIONS = {'BASIS_VECTOR_XY':2, 'BASIS_TENSOR':2, 'PAIR_OF_RATIONALS':2,
              'SYMBOLIC_VECTOR_14':14, 'SYMBOLIC_VECTOR_38':38}


def typed_decode(kind, value):
    if kind in SCALARS:
        result = exact_expr(value)
        if kind in ('INTEGER','SIGN'):
            require(result.is_Integer is True, 'INTEGER_TYPE_MISMATCH')
        if kind == 'SIGN': require(result in (-1,1), 'SIGN_DOMAIN')
        if kind in ('RATIONAL','PHASE','INVERTIBLE_SCALE'):
            require(result.is_Rational is True, 'RATIONAL_TYPE_MISMATCH')
        if kind == 'INVERTIBLE_SCALE': require(result != 0, 'SINGULAR_NORMALIZATION')
        if kind == 'SYMBOL': require(isinstance(result, sp.Symbol), 'SYMBOL_TYPE_MISMATCH')
        return result
    if kind in VECTORS:
        require(type(value) is list and all(type(x) in (str,int) for x in value), 'VECTOR_TYPE_MISMATCH')
        if kind in DIMENSIONS: require(len(value) == DIMENSIONS[kind], 'VECTOR_DIMENSION_MISMATCH')
        require(len(value) <= 256, 'VECTOR_SIZE_LIMIT')
        return tuple(exact_expr(x) for x in value)
    if kind == 'SYMBOLIC_MATRIX':
        require(type(value) is list and value and type(value[0]) is list and value[0], 'MATRIX_TYPE_MISMATCH')
        require(len(value)*len(value[0]) <= 4096, 'MATRIX_SIZE_LIMIT')
        require(all(type(row) is list and len(row) == len(value[0]) for row in value), 'RAGGED_MATRIX')
        return sp.ImmutableMatrix([[exact_expr(x) for x in row] for row in value])
    if kind == 'BOOLEAN':
        require(type(value) is bool, 'BOOLEAN_TYPE_MISMATCH')
    elif kind in ('EVANESCENT_EVALUATION_STATE','TENSOR_FINGERPRINT','SYMBOL_TEXT'):
        require(type(value) is str, 'TEXT_TYPE_MISMATCH')
        if kind == 'EVANESCENT_EVALUATION_STATE':
            require(value in ('NOT_EVALUATED','EVALUATED_ZERO','EVALUATED_NONZERO'), 'EPISTEMIC_STATE_DOMAIN')
    else:
        raise VerificationError('TYPE_DECODER_NOT_IMPLEMENTED', kind)
    return value


def exact_equal(a, b):
    if isinstance(a, sp.MatrixBase) or isinstance(b, sp.MatrixBase):
        return isinstance(a, sp.MatrixBase) and isinstance(b, sp.MatrixBase) and a.shape == b.shape and all(exact_equal(x,y) for x,y in zip(a,b))
    if isinstance(a, tuple) or isinstance(b, tuple):
        return isinstance(a,tuple) and isinstance(b,tuple) and len(a)==len(b) and all(exact_equal(x,y) for x,y in zip(a,b))
    if isinstance(a, sp.Basic) or isinstance(b, sp.Basic):
        return isinstance(a,sp.Basic) and isinstance(b,sp.Basic) and sp.cancel(a-b)==0
    return type(a) is type(b) and a == b


def resolve_locator(document, locator):
    """JSON pointers plus the frozen legacy [key=value] unique-row syntax.

    Compound semicolon locators are rejected, not guessed. Return the resolved
    value AND canonical pointer so a selector cannot conceal multiple matches.
    """
    require(type(locator) is str and locator.startswith('/'), 'SOURCE_LOCATOR_SYNTAX')
    require(';' not in locator, 'COMPOUND_LOCATOR_REQUIRES_EXPLICIT_DECODER')
    current, canonical_parts = document, []
    for raw in locator[1:].split('/'):
        require(re.search(r'~(?![01])', raw) is None, 'POINTER_ESCAPE')
        part = raw.replace('~1','/').replace('~0','~')
        selector = re.fullmatch(r'([^\[\]]+)\[([^=\[\]]+)=([^\[\]]+)\]', part)
        if selector:
            key, field, wanted = selector.groups()
            require(type(current) is dict and key in current and type(current[key]) is list, 'SOURCE_POINTER_MISSING', part)
            rows = current[key]
            matches = [i for i,row in enumerate(rows) if type(row) is dict and row.get(field) == wanted]
            require(len(matches) == 1, 'SOURCE_SELECTOR_NOT_UNIQUE', part)
            index = matches[0]
            current = rows[index]
            canonical_parts += [key, str(index)]
        elif type(current) is dict:
            require(part in current, 'SOURCE_POINTER_MISSING', part)
            current = current[part]
            canonical_parts.append(part)
        elif type(current) is list:
            require(re.fullmatch(r'0|[1-9][0-9]*', part) is not None, 'SOURCE_ARRAY_INDEX')
            index = int(part)
            require(index < len(current), 'SOURCE_POINTER_MISSING', part)
            current = current[index]
            canonical_parts.append(part)
        else:
            raise VerificationError('SOURCE_POINTER_THROUGH_SCALAR', part)
    return current, '/'+'/'.join(p.replace('~','~0').replace('/','~1') for p in canonical_parts)


class BoundSources:
    def __init__(self, root, allowed_inputs):
        self.root = Path(root).resolve()
        self.allowed = {}
        self.read_receipts = []
        for row in allowed_inputs:
            relative = row['path']
            require(relative not in self.allowed, 'DUPLICATE_SOURCE_PATH')
            self.allowed[relative] = dict(row)

    def resolve(self, evidence):
        relative = evidence['artifact_path']
        require(relative in self.allowed, 'SOURCE_NOT_ALLOWLISTED', relative)
        require(not PurePosixPath(relative).is_absolute() and '\\' not in relative and ':' not in relative and '..' not in PurePosixPath(relative).parts,
                'SOURCE_PATH_ESCAPE')
        path = (self.root/relative).resolve(strict=True)
        require(self.root in path.parents, 'SOURCE_PATH_ESCAPE')
        row = self.allowed[relative]
        raw = path.read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        require(len(raw) == row['byte_size'] and actual == row['sha256'] == evidence['artifact_sha256'], 'SOURCE_HASH_MISMATCH')
        value, pointer = resolve_locator(read_json(raw), evidence['semantic_locator'])
        self.read_receipts.append(dict(path=relative, sha256=actual, canonical_pointer=pointer,
                                      value_sha256=hashlib.sha256(canonical(value).encode()).hexdigest()))
        return value


def graph_structure(graph, contract):
    rows = graph['nodes']
    require(type(rows) is list, 'NODE_LIST_REQUIRED')
    nodes = {}
    for n in rows:
        require(type(n) is dict and set(contract['node_schema']['required_fields']) <= n.keys(), 'NODE_SCHEMA')
        key = n['node_id']
        require(type(key) is str and key not in nodes, 'DUPLICATE_NODE_ID')
        require(n['kind'] in contract['allowed_node_kinds'], 'UNKNOWN_NODE_KIND', key)
        require(n['operation'] in contract['allowed_operations'], 'UNKNOWN_OPERATION', key)
        require(type(n['parents']) is list and all(type(p) is str for p in n['parents']), 'PARENT_SCHEMA', key)
        require(len(set(n['parents'])) == len(n['parents']), 'DUPLICATE_PARENT', key)
        require(n['domain_status'] == 'IN_DOMAIN', 'NODE_OUT_OF_DOMAIN', key)
        body = {k:v for k,v in n.items() if k != 'recomputation_digest'}
        require(digest(body,'PASS0281_PROVENANCE_NODE_v0') == n['recomputation_digest'], 'NODE_DIGEST_MISMATCH', key)
        nodes[key] = n
    expected = {(p,k) for k,n in nodes.items() for p in n['parents']}
    edges = graph['edges']
    require(type(edges) is list and all(type(e) is list and len(e)==2 and all(type(x) is str for x in e) for e in edges), 'EDGE_SCHEMA')
    require(len({tuple(e) for e in edges}) == len(edges), 'DUPLICATE_EDGE')
    require({tuple(e) for e in edges} == expected, 'PARENT_EDGE_MISMATCH')
    require(all(p in nodes for p,_ in expected), 'MISSING_PARENT')
    require(type(graph['node_count']) is int and graph['node_count']==len(nodes), 'NODE_COUNT_MISMATCH')
    require(type(graph['edge_count']) is int and graph['edge_count']==len(edges), 'EDGE_COUNT_MISMATCH')
    require(graph['canonical_digest'] == digest(dict(nodes=rows, edges=edges),'PASS0281_DAG_v0'), 'GRAPH_DIGEST_MISMATCH')
    pending, order = set(nodes), []
    visited = set()
    while pending:
        ready = sorted(k for k in pending if set(nodes[k]['parents']) <= visited)
        require(ready, 'CYCLIC_GRAPH')
        order += ready
        pending.difference_update(ready)
        visited.update(ready)
    outputs = {k for k,n in nodes.items() if n['kind']=='OUTPUT_ROOT'}
    require(outputs == set(contract['output_roots_required']), 'OUTPUT_ROOT_COVERAGE')
    required_dag = contract.get('c03_physical_required_dag', {})
    require({tuple(e) for e in required_dag.get('edges',[])} <= expected, 'MANDATORY_EDGE_MISSING')
    for row in required_dag.get('nodes',[]):
        require(row['node_id'] in nodes and nodes[row['node_id']]['kind']==row['kind'], 'MANDATORY_NODE_MISMATCH')
        if 'operation' in row:
            require(nodes[row['node_id']]['operation']==row['operation'], 'MANDATORY_OPERATION_MISMATCH')
    ancestors = set(outputs)
    queue = list(outputs)
    while queue:
        for p in nodes[queue.pop()]['parents']:
            if p not in ancestors:
                ancestors.add(p)
                queue.append(p)
    require(ancestors==set(nodes), 'DECORATIVE_OR_DISCONNECTED_NODE')
    return nodes, order


def arithmetic(operation, parents, parameters=None):
    """Small exact algebra subset. No claimed node value is an operand."""
    parameters = parameters or {}
    require(not parameters, 'OPERATION_PARAMETERS_REQUIRE_IMPLEMENTED_SIGNATURE', operation)
    if operation == 'OUTPUT_BIND':
        require(len(parents)==1, 'OUTPUT_BIND_ARITY')
        return parents[0]
    if operation == 'PRODUCT':
        require(parents and all(isinstance(x,sp.Basic) for x in parents), 'PRODUCT_SIGNATURE')
        return sp.cancel(sp.prod(parents))
    if operation in ('TENSOR_SUM','TENSOR_DIFFERENCE'):
        require(len(parents)==2 and all(isinstance(x,tuple) for x in parents) and len(parents[0])==len(parents[1]), 'TENSOR_SIGNATURE')
        return tuple(sp.cancel(a+b if operation=='TENSOR_SUM' else a-b) for a,b in zip(*parents))
    if operation == 'LINEAR_COMBINATION':
        require(len(parents)==4, 'LINEAR_COMBINATION_SIGNATURE')
        a,x,b,y = parents
        require(isinstance(a,sp.Basic) and isinstance(b,sp.Basic) and isinstance(x,tuple) and isinstance(y,tuple) and len(x)==len(y), 'LINEAR_COMBINATION_SIGNATURE')
        return tuple(sp.cancel(a*u+b*v) for u,v in zip(x,y))
    if operation == 'EXACT_MATRIX_PROJECTION':
        require(len(parents)==2 and isinstance(parents[0],sp.MatrixBase) and isinstance(parents[1],tuple), 'MATRIX_PROJECTION_SIGNATURE')
        require(parents[0].cols==len(parents[1]), 'MATRIX_DIMENSION_MISMATCH')
        return tuple(sp.cancel(x) for x in parents[0]*sp.Matrix(parents[1]))
    if operation == 'INVERTIBLE_NORMALIZATION':
        require(len(parents)==3 and all(isinstance(x,sp.Basic) for x in parents), 'NORMALIZATION_SIGNATURE_REQUIRES_VALUE_SCALE_INVERSE')
        value, scale, inverse = parents
        require(scale!=0 and inverse!=0 and sp.cancel(scale*inverse-1)==0, 'NORMALIZATION_INVERSE_MISMATCH')
        return sp.cancel(value*scale)
    if operation == 'PERMUTATION_PARITY':
        require(len(parents)==1 and isinstance(parents[0],tuple), 'PERMUTATION_SIGNATURE')
        p = parents[0]
        require(all(x.is_Integer is True for x in p) and sorted(p)==list(range(len(p))), 'PERMUTATION_DOMAIN')
        return sp.Integer((-1)**sum(bool(p[i]>p[j]) for i in range(len(p)) for j in range(i+1,len(p))))
    raise VerificationError('OPERATION_NOT_IMPLEMENTED', operation)


def evaluate_graph(graph, contract, sources, output_values):
    nodes, order = graph_structure(graph, contract)
    computed, receipts, ancestry = {}, [], {}
    for key in order:
        n = nodes[key]
        claimed = typed_decode(n['semantic_type'], n['typed_value'])
        if n['kind'] == 'SOURCE_FACT':
            require(n['operation']=='SOURCE_DECODE' and not n['parents'] and len(n['evidence_refs'])==1 and not n.get('operation_parameters'), 'SOURCE_DECODE_SIGNATURE', key)
            resolved = sources.resolve(n['evidence_refs'][0])
            try:
                actual = typed_decode(n['semantic_type'], resolved)
            except VerificationError as exc:
                raise VerificationError('EXPLICIT_SOURCE_DECODER_REQUIRED', key+': '+exc.code) from exc
            ancestry[key] = {key}
        elif n['kind'] == 'UNIVERSAL_ALGEBRA_PRIMITIVE':
            raise VerificationError('UNIVERSAL_PRIMITIVE_REGISTRY_REQUIRED', key)
        else:
            require(n['parents'], 'DERIVED_PARENTS_REQUIRED', key)
            require((n['kind']=='OUTPUT_ROOT') == (n['operation']=='OUTPUT_BIND'), 'OUTPUT_KIND_OPERATION_MISMATCH', key)
            if n['operation']=='OUTPUT_BIND':
                require(len(n['parents'])==1, 'OUTPUT_BIND_ARITY', key)
                require(nodes[n['parents'][0]]['semantic_type']==n['semantic_type'], 'OUTPUT_BIND_TYPE_MISMATCH', key)
            actual = arithmetic(n['operation'], [computed[p] for p in n['parents']], n.get('operation_parameters'))
            ancestry[key] = set().union(*(ancestry[p] for p in n['parents']))
        require(exact_equal(actual,claimed), 'RECOMPUTED_VALUE_MISMATCH', key)
        computed[key] = actual
        receipts.append(dict(node_id=key, status='RECOMPUTED_AND_EQUAL'))
    require(set(output_values)==set(contract['output_roots_required']), 'EMITTED_ROOT_SET_MISMATCH')
    for key,value in output_values.items():
        require(ancestry[key], 'OUTPUT_HAS_NO_SOURCE_ANCESTRY', key)
        require(exact_equal(computed[key],typed_decode(nodes[key]['semantic_type'],value)), 'EMITTED_VALUE_MISMATCH', key)
    return dict(status='PASS_SUPPORTED_EXACT_ALGEBRA_PROFILE_ONLY', receipts=receipts,
                source_read_receipts=sources.read_receipts,
                scientific_requalification=False, ast_dataflow_audit='NOT_IMPLEMENTED',
                full_pass0280_contract='NOT_ESTABLISHED')
