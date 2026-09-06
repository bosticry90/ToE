"""Small fail-closed evaluator for explicit, finite provenance expressions.

Not a physics runner, an anti-oracle proof, or a replacement acceptance contract.
Opaque physics operations must not be accepted merely because their claimed
values match a target. Unsupported operations fail until independently supplied.
The caller, not a candidate payload, supplies the frozen profile and primitives.
"""
from __future__ import annotations
import ast
from collections import deque
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from typing import Any

import sympy as sp


class ProvenanceError(ValueError):
    def __init__(self, code: str, node: str = ''):
        self.code, self.node = code, node
        super().__init__(code + (':' + node if node else ''))


def require(test: bool, code: str, node: str = '') -> None:
    if not test:
        raise ProvenanceError(code, node)


def strict_json(raw: bytes) -> Any:
    def obj(pairs):
        output = {}
        for key, value in pairs:
            require(key not in output, 'DUPLICATE_JSON_KEY', key)
            output[key] = value
        return output
    return json.loads(raw.decode('utf-8'), object_pairs_hook=obj,
                      parse_constant=lambda value: (_ for _ in ()).throw(ProvenanceError('NONFINITE_JSON', value)))


def node_digest(node: dict) -> str:
    value = {k: v for k, v in node.items() if k != 'recomputation_digest'}
    body = json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)
    return hashlib.sha256(('PASS0281_PROVENANCE_NODE_v0\0' + body).encode()).hexdigest()


def scalar(value: Any) -> sp.Expr:
    """Parse exact arithmetic without sympify/eval of an arbitrary string."""
    require(not isinstance(value, bool), 'BOOLEAN_IS_NOT_SCALAR')
    if isinstance(value, int):
        require(value.bit_length() <= 256, 'INTEGER_LIMIT')
        return sp.Integer(value)
    require(isinstance(value, str) and 0 < len(value) <= 2048, 'SCALAR_SYNTAX')
    try:
        tree = ast.parse(value.replace('^', '**'), mode='eval')
    except (SyntaxError, ValueError) as exc:
        raise ProvenanceError('SCALAR_SYNTAX') from exc
    require(sum(1 for _ in ast.walk(tree)) <= 256, 'EXPRESSION_LIMIT')
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return scalar(node.value)
        if isinstance(node, ast.Name):
            require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]{0,63}', node.id) is not None, 'SYMBOL_SYNTAX')
            return sp.I if node.id == 'I' else sp.Symbol(node.id)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            item = visit(node.operand)
            return item if isinstance(node.op, ast.UAdd) else -item
        if isinstance(node, ast.BinOp):
            left, right = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return left + right
            if isinstance(node.op, ast.Sub): return left - right
            if isinstance(node.op, ast.Mult): return left * right
            if isinstance(node.op, ast.Div):
                require(right != 0, 'ZERO_DIVISOR')
                return left / right
            if isinstance(node.op, ast.Pow):
                require(right.is_Integer and abs(int(right)) <= 32, 'POWER_LIMIT')
                require(left != 0 or right >= 0, 'ZERO_DIVISOR')
                return left ** right
        raise ProvenanceError('NON_ARITHMETIC_EXPRESSION')
    return visit(tree.body)


def arithmetic(value: Any) -> Any:
    if isinstance(value, list):
        require(len(value) <= 4096, 'VECTOR_LIMIT')
        return [arithmetic(v) for v in value]
    return scalar(value)


def exact_equal(left: Any, right: Any, *, arithmetic_type: bool = False) -> bool:
    if arithmetic_type:
        if isinstance(left, list) or isinstance(right, list):
            return isinstance(left, list) and isinstance(right, list) and len(left) == len(right) and all(
                exact_equal(a, b, arithmetic_type=True) for a, b in zip(left, right))
        if isinstance(left, sp.Basic) and isinstance(right, sp.Basic):
            return sp.cancel(left - right) == 0
        return sp.cancel(scalar(left) - scalar(right)) == 0
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(exact_equal(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(exact_equal(a, b) for a, b in zip(left, right))
    return left == right


ARITHMETIC_TYPES = {'INTEGER', 'SIGN', 'RATIONAL', 'SYMBOL', 'SYMBOLIC_SCALAR',
    'SYMBOLIC_COEFFICIENT', 'INVERTIBLE_SCALE', 'BASIS_VECTOR_XY', 'BASIS_TENSOR',
    'PAIR_OF_RATIONALS', 'SYMBOLIC_VECTOR_14', 'SYMBOLIC_VECTOR_38', 'SYMBOLIC_MATRIX'}


def source_pointer(document: Any, pointer: str) -> Any:
    """Strict JSON Pointer; selector strings/compound locators are not guessed."""
    require(isinstance(pointer, str), 'SOURCE_LOCATOR_SYNTAX')
    if pointer == '':
        return document
    require(pointer.startswith('/'), 'SOURCE_LOCATOR_SYNTAX')
    value = document
    for part in pointer[1:].split('/'):
        require(re.search(r'~(?![01])', part) is None, 'SOURCE_LOCATOR_ESCAPE')
        key = part.replace('~1', '/').replace('~0', '~')
        if isinstance(value, dict):
            require(key in value, 'SOURCE_LOCATOR_NOT_FOUND', pointer)
            value = value[key]
        elif isinstance(value, list):
            require(re.fullmatch(r'0|[1-9][0-9]*', key) is not None, 'SOURCE_ARRAY_INDEX', pointer)
            index = int(key)
            require(index < len(value), 'SOURCE_LOCATOR_NOT_FOUND', pointer)
            value = value[index]
        else:
            raise ProvenanceError('SOURCE_LOCATOR_NOT_FOUND', pointer)
    return value


class SourceStore:
    def __init__(self, root: Path, allowlist: dict):
        self.root = root.resolve(strict=True)
        self.rows = {}
        self.documents = {}
        self.read_receipts = []
        for row in allowlist['allowed_inputs']:
            relative = row['path']
            posix = PurePosixPath(relative)
            require(not posix.is_absolute() and '..' not in posix.parts and '\\' not in relative
                    and ':' not in relative, 'SOURCE_PATH_ESCAPE', relative)
            require(relative not in self.rows, 'DUPLICATE_SOURCE_PATH', relative)
            path = (self.root / relative).resolve(strict=True)
            require(self.root in path.parents, 'SOURCE_PATH_ESCAPE', relative)
            raw = path.read_bytes()
            require(len(raw) == row['byte_size'] and hashlib.sha256(raw).hexdigest() == row['sha256'],
                    'SOURCE_IDENTITY_MISMATCH', relative)
            self.rows[relative] = row
            self.documents[relative] = strict_json(raw)
            self.read_receipts.append(dict(path=relative, bytes=len(raw), sha256=row['sha256']))

    def resolve(self, reference: dict) -> Any:
        require(set(reference) == {'artifact_path', 'artifact_sha256', 'semantic_locator'}, 'SOURCE_REFERENCE_FIELDS')
        path = reference['artifact_path']
        require(path in self.rows, 'SOURCE_NOT_ALLOWLISTED', path)
        require(reference['artifact_sha256'] == self.rows[path]['sha256'], 'SOURCE_REFERENCE_HASH', path)
        return source_pointer(self.documents[path], reference['semantic_locator'])


def add(left, right):
    if isinstance(left, list) or isinstance(right, list):
        require(isinstance(left, list) and isinstance(right, list) and len(left) == len(right), 'TENSOR_SHAPE')
        return [add(a, b) for a, b in zip(left, right)]
    return left + right


def multiply(left, right):
    require(not (isinstance(left, list) and isinstance(right, list)), 'AMBIGUOUS_TENSOR_PRODUCT')
    if isinstance(left, list): return [multiply(v, right) for v in left]
    if isinstance(right, list): return [multiply(left, v) for v in right]
    return left * right


def render(value):
    if isinstance(value, sp.Basic): return sp.sstr(sp.cancel(value))
    if isinstance(value, list): return [render(v) for v in value]
    if isinstance(value, dict): return {k: render(v) for k, v in value.items()}
    return value


def operation(node: dict, parents: list[Any], source: SourceStore, primitives: dict) -> Any:
    op, params = node['operation'], node.get('operation_parameters', {})
    if op == 'SOURCE_DECODE':
        require(not parents and node['kind'] == 'SOURCE_FACT' and len(node['evidence_refs']) == 1
                and not params, 'SOURCE_DECODE_NEEDS_EXACT_VALUE_LOCATOR', node['node_id'])
        value = source.resolve(node['evidence_refs'][0])
        return arithmetic(value) if node['semantic_type'] in ARITHMETIC_TYPES else value
    if node['kind'] == 'UNIVERSAL_ALGEBRA_PRIMITIVE':
        require(not parents and not params and not node['evidence_refs'] and node['node_id'] in primitives,
                'UNAPPROVED_UNIVERSAL_PRIMITIVE')
        return arithmetic(primitives[node['node_id']])
    if op == 'OUTPUT_BIND':
        require(len(parents) == 1 and not params, 'OUTPUT_BIND_ARITY')
        return parents[0]
    if op == 'PRODUCT':
        require(parents and not params, 'PRODUCT_REQUIRES_EXPLICIT_PARENTS')
        result = sp.Integer(1)
        for value in parents: result = multiply(result, value)
        return result
    if op in ('TENSOR_SUM', 'TENSOR_DIFFERENCE'):
        require(parents and not params, 'SUM_REQUIRES_EXPLICIT_PARENTS')
        if op == 'TENSOR_DIFFERENCE':
            require(len(parents) == 2, 'DIFFERENCE_ARITY')
            return add(parents[0], multiply(-1, parents[1]))
        result = parents[0]
        for value in parents[1:]: result = add(result, value)
        return result
    if op == 'PERMUTATION_PARITY':
        require(len(parents) == 1 and not params and isinstance(parents[0], list), 'PARITY_REQUIRES_SOURCE_PERMUTATION')
        values = parents[0]
        require(sorted(values) == list(range(len(values))), 'NOT_A_PERMUTATION')
        return sp.Integer((-1) ** sum(values[i] > values[j] for i in range(len(values)) for j in range(i + 1, len(values))))
    if op == 'INVERTIBLE_NORMALIZATION':
        require(len(parents) == 2 and not params and not isinstance(parents[1], list), 'NORMALIZATION_REQUIRES_VALUE_AND_SCALE')
        scale = parents[1]
        require(scale != 0, 'NONINVERTIBLE_NORMALIZATION')
        result = multiply(parents[0], scale)
        return result
    if op == 'EXACT_MATRIX_PROJECTION':
        require(len(parents) == 2 and not params, 'MATRIX_PROJECTION_REQUIRES_MATRIX_AND_VECTOR')
        matrix, vector = parents
        require(isinstance(matrix, list) and matrix and isinstance(vector, list), 'MATRIX_SHAPE')
        require(all(isinstance(row, list) and len(row) == len(vector) for row in matrix), 'MATRIX_SHAPE')
        return [sum(a * b for a, b in zip(row, vector)) for row in matrix]
    # No return of the candidate's claimed value as an implementation fallback.
    raise ProvenanceError('INDEPENDENT_OPERATION_NOT_IMPLEMENTED', node['node_id'])


def verify(payload: dict, profile: dict, sources: SourceStore, *, primitives: dict | None = None) -> dict:
    nodes = payload['provenance_dag']['nodes']
    edges = payload['provenance_dag']['edges']
    require(isinstance(nodes, list) and 0 < len(nodes) <= 4096, 'NODE_COUNT')
    by_id = {}
    derived_edges = []
    fields = set(profile['node_schema']['required_fields'])
    for node in nodes:
        identity = node.get('node_id', '')
        require(fields <= set(node) and set(node) <= fields | {'operation_parameters'}, 'NODE_FIELDS', identity)
        require(identity not in by_id and isinstance(identity, str) and identity, 'DUPLICATE_NODE', identity)
        require(node['kind'] in profile['allowed_node_kinds'], 'UNKNOWN_NODE_KIND', identity)
        require(node['operation'] in profile['allowed_operations'], 'UNKNOWN_OPERATION', identity)
        require(node_digest(node) == node['recomputation_digest'], 'NODE_DIGEST', identity)
        require(node['domain_status'] == 'IN_DOMAIN', 'NODE_NOT_ADMITTED', identity)
        require(isinstance(node['parents'], list) and len(set(node['parents'])) == len(node['parents']), 'PARENT_LIST', identity)
        by_id[identity] = node
        derived_edges += [(p, identity) for p in node['parents']]
    require(all(isinstance(e, list) and len(e) == 2 and all(isinstance(v, str) for v in e) for e in edges), 'EDGE_SCHEMA')
    actual_edges = [tuple(e) for e in edges]
    require(len(set(actual_edges)) == len(actual_edges), 'DUPLICATE_EDGE')
    require(set(actual_edges) == set(derived_edges), 'PARENT_EDGE_DISAGREEMENT')
    require(all(a in by_id and b in by_id for a, b in actual_edges), 'MISSING_PARENT')
    roots = {n['node_id'] for n in nodes if n['kind'] == 'OUTPUT_ROOT'}
    require(roots == set(profile['output_roots_required']), 'OUTPUT_ROOT_SET')
    mandatory = profile.get('c03_physical_required_dag', {})
    require(all(row['node_id'] in by_id for row in mandatory.get('nodes', [])), 'MANDATORY_NODE_ABSENT')
    for row in mandatory.get('nodes', []):
        for field in ('kind', 'operation'):
            if field in row:
                require(by_id[row['node_id']][field] == row[field], 'MANDATORY_NODE_ROLE', row['node_id'])
    require(set(map(tuple, mandatory.get('edges', []))) <= set(actual_edges), 'MANDATORY_EDGE_ABSENT')
    active = set()
    for root in roots:
        ancestry, pending = set(), [root]
        while pending:
            key = pending.pop()
            if key in ancestry: continue
            ancestry.add(key)
            pending.extend(by_id[key]['parents'])
        require(any(by_id[key]['kind'] == 'SOURCE_FACT' for key in ancestry), 'UNDERIVED_OUTPUT', root)
        active.update(ancestry)
    require(set(by_id) - active <= set(profile.get('diagnostic_nodes_allowed', [])), 'DECORATIVE_NODE')
    indegree = {key: len(n['parents']) for key, n in by_id.items()}
    children = {key: [] for key in by_id}
    for a, b in actual_edges: children[a].append(b)
    ready = deque(sorted(key for key, degree in indegree.items() if degree == 0))
    order = []
    while ready:
        key = ready.popleft()
        order.append(key)
        for child in children[key]:
            indegree[child] -= 1
            if indegree[child] == 0: ready.append(child)
    require(len(order) == len(nodes), 'CYCLIC_DAG')
    computed, receipts = {}, []
    for identity in order:
        node = by_id[identity]
        value = operation(node, [computed[p] for p in node['parents']], sources, primitives or {})
        claimed = arithmetic(node['typed_value']) if node['semantic_type'] in ARITHMETIC_TYPES else node['typed_value']
        require(exact_equal(value, claimed, arithmetic_type=node['semantic_type'] in ARITHMETIC_TYPES), 'RECOMPUTATION_MISMATCH', identity)
        computed[identity] = value
        receipts.append(dict(node_id=identity, operation=node['operation'], computed_value=render(value), comparison='EXACT_MATCH'))
    require(set(payload['output_bindings']) == roots, 'PAYLOAD_BINDING_SET')
    for identity, pointer in payload['output_bindings'].items():
        # Bindings are supplied by a trusted profile, not selected by the candidate.
        require(profile.get('output_bindings', {}).get(identity) == pointer, 'UNAUTHORIZED_PAYLOAD_BINDING', identity)
        emitted = source_pointer(payload, pointer)
        require(exact_equal(render(computed[identity]), emitted,
                            arithmetic_type=by_id[identity]['semantic_type'] in ARITHMETIC_TYPES), 'EMITTED_ROOT_MISMATCH', identity)
    return dict(status='EXPLICIT_FINITE_GRAPH_RECOMPUTED', recomputed_nodes=len(receipts), roots=len(roots), receipts=receipts,
                full_physics_profile_qualification=False, code_dataflow_or_os_io_audit='NOT_ESTABLISHED')
