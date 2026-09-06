"""Six-record source/group/spinor calculation component, not activation.

IDs select source records and tensor decoders, never target coefficients or
evanescent answers. The absence method is restricted to one scalar spinor
chain with the declared two-current/two-propagator, simple-pole profile.
"""
from __future__ import annotations

import ast
import itertools as it
import re

import sympy as sp

from formal.python.toe.generic_runner import c03_source_derivation_v1 as p

require, E, exact = p.require, p.E, p.exact
RECORDS = {
    'RV01': 'D6-P2P3-QQ-HDAG-X-RHO8::C4',
    'RV02': 'D6-P2P3-QQ-HDAG-X-RHO3::C3',
    'RV03': 'D5-QQ-X-HDAG-A',
    'RV04': 'D6-PSI4-DUQL',
    'RV05': 'D5-DD-X-H-A',
    'RV06': 'D6-P2P3-UBAR-Q-X3::C1',
}


def radical(value):
    """Exact arithmetic plus sqrt of positive small integers, without eval."""
    require(type(value) in (int, str) and len(str(value)) < 512, 'RADICAL_DOMAIN')
    try:
        tree = ast.parse(str(value), mode='eval')
    except SyntaxError as exc:
        raise exact.VerificationError('RADICAL_SYNTAX') from exc
    require(sum(1 for _ in ast.walk(tree)) < 64, 'RADICAL_SIZE')
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int and abs(node.value) < 100000:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name) and node.id == 'I':
            return sp.I
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            result = visit(node.operand)
            return -result if isinstance(node.op, ast.USub) else result
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'sqrt' and len(node.args) == 1 and not node.keywords:
            result = visit(node.args[0])
            require(result.is_Integer is True and 0 < result <= 100, 'RADICAL_ARGUMENT')
            return sp.sqrt(result)
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return a+b
            if isinstance(node.op, ast.Sub): return a-b
            if isinstance(node.op, ast.Mult): return a*b
            if isinstance(node.op, ast.Div):
                require(b != 0, 'RADICAL_ZERO_DENOMINATOR')
                return a/b
        raise exact.VerificationError('RADICAL_CAPABILITY_FORBIDDEN')
    return sp.simplify(visit(tree.body))


def load_inputs(root=p.norm.ROOT):
    src = p.Sources(root)
    allowed = src.profile['allowed_inputs']
    def by_suffix(suffix, pointer):
        found = [r for r in allowed if r['path'].endswith(suffix)]
        require(len(found) == 1, 'RV_SOURCE_BINDING')
        row = found[0]
        return src.bound.resolve(dict(artifact_path=row['path'], artifact_sha256=row['sha256'], semantic_locator=pointer))
    topologies = by_suffix('/source_only_topology_extract.json', '/rows')
    d5 = by_suffix('t_first_r2_active_bnv_d5_reconciliation_pass_0002_v0.json', '/candidate_reconciliation')
    d6 = src.get('d6', '/normalized_nonderivative_records')
    targets = src.get('targets', '/target_vertex_bindings')
    components = src.get('components', '/channel_component_registry')
    records = []
    for record_id, operator in RECORDS.items():
        def unique(rows, key, value):
            matches = [r for r in rows if r.get(key) == value]
            require(len(matches) == 1, 'RV_ROW_NOT_UNIQUE', operator)
            return matches[0]
        topology = unique(topologies, 'source_insertion_id', operator)
        target = unique(targets, 'target_operator_id', operator)
        gauge = topology['coupling_monomial'][0]
        vertices = [src.get('action', '/feynman_rule_registry/gauge_matter_three_point[rule_id='+v.replace('VTX-GAUGE-', 'FR-')+']') for v in topology['renormalizable_vertex_ids']]
        endpoints = [v['functional_derivative_order'][1] for v in vertices]
        fields = [src.get('action', '/field_registry[field='+f+']') for f in endpoints]
        source, registered, tensor = None, None, None
        if operator.startswith('D5-'):
            source = unique([r for g in d5 for r in g['representatives']], 'family_id', operator)
        elif operator == 'D6-PSI4-DUQL':
            source = unique(d6['inherited_psi4_warsaw_rows'], 'id', 'D6-PSI4-Q-DUQL')
        elif operator == 'D6-P2P3-UBAR-Q-X3::C1':
            orientation = 't_first_r2_active_bnv_d6_clean_room_field_orientation_and_component_reconstruction_audit_pass_0018_v0.json'
            directed_rows = by_suffix(orientation, '/mixed_conjugation_psi_bar_psi_phi3_reconstruction/rows')
            matches = [r for r in directed_rows if r['fields'] == target['ordered_fields']]
            require(len(matches) == 1 and matches[0]['multiplicity']['total'] == 1, 'DIRECTED_SOURCE_MULTIPLICITY')
            source = dict(matches[0], witness=by_suffix(orientation, '/mixed_conjugation_psi_bar_psi_phi3_reconstruction/explicit_component_witnesses/baruR_qL_X3'))
        else:
            base, ordinal = operator.split('::C')
            group = unique(d6['psi2_phi3_channel_groups'], 'multiset_id', base)
            require(0 < int(ordinal) <= len(group['channels']), 'RV_CHANNEL_INDEX')
            source = group['channels'][int(ordinal)-1]
            registered = unique(components, 'id', base+'::'+source['id'])
            tensor = src.get('components', '/deduplicated_sparse_component_tensor_table/'+registered['component_tensor_fingerprint'])
        generators = src.get('action', '/generator_registry/'+('SU3_fundamental' if gauge == 'g3' else 'SU2_fundamental')) if gauge != 'g1' else None
        records.append(dict(record_id=record_id, operator=operator, topology=topology, target=target,
                            source=source, registered=registered, tensor=tensor, vertices=vertices,
                            fields=fields, generators=generators))
    return dict(records=records, regularization=src.get('scheme', '/regularization_and_subtraction'),
                dirac=src.get('scheme', '/bmhv_dirac_contract'),
                gauge_parameters=src.get('scheme', '/gauge_fixing_and_ghosts/gauge_parameters'),
                source_reads=src.bound.read_receipts)


def domain(record):
    t, target = record['topology'], record['target']
    require(type(t['source_derivative_count']) is int and t['source_derivative_count'] == 0 and target['derivative_count'] == 0, 'RV_DERIVATIVE_DOMAIN')
    require(t['loop_count'] == 1 and t['one_particle_irreducible'] is True, 'RV_LOOP_DOMAIN')
    require(t['source_insertion_id'] == record['operator'] == target['target_operator_id'], 'RV_OPERATOR_BINDING')
    require(len(t['renormalizable_vertex_ids']) == len(record['vertices']) == 2, 'RV_VERTEX_DOMAIN')
    require(len(t['coupling_monomial']) == 2 and t['coupling_monomial'][0] == t['coupling_monomial'][1], 'RV_COUPLING_DOMAIN')
    fermions = [edge for edge in t['internal_edges'] if not edge[1].startswith('G')]
    require(len(t['internal_edges']) == 3 and len(fermions) == 2 and all(edge[0] == 0 for edge in fermions), 'RV_PROPAGATOR_DOMAIN')
    kinds = [field['kind'] for field in record['fields']]
    require(all(kind in ('LEFT_WEYL', 'RIGHT_WEYL') for kind in kinds), 'RV_FERMION_TYPE')
    directed = any(edge[1].startswith('bar') for edge in fermions)
    if directed:
        require(sorted(kinds) == ['LEFT_WEYL', 'RIGHT_WEYL'] and 'baruR' in t['target_external_fields'], 'RV_DIRECTED_PROFILE')
        require(record['source']['fields'] == target['ordered_fields'], 'RV_DIRECTED_SOURCE_FIELDS')
        require(any(radical(r['coefficient']) != 0 for r in record['source']['witness']['sparse_entries']), 'RV_DIRECTED_SOURCE_ZERO')
    else:
        require(len(set(kinds)) == 1, 'RV_CHIRALITY_MISMATCH')
    for vi, vertex in zip(t['renormalizable_vertex_ids'], record['vertices']):
        require(vertex['rule_id'] == vi.replace('VTX-GAUGE-', 'FR-') and vertex['rule_kind'] == 'FERMION_FERMION_QUANTUM_GAUGE', 'RV_RULE_BINDING')
        require('gamma^mu' in vertex['exact_rule'], 'RV_CURRENT_GAMMA_DOMAIN')
    # Four-fermion sources need an explicit same-bilinear incidence check.
    # Other admitted records have exactly two fermion slots in the operator.
    fermion_fields = [f for f in target['ordered_fields'] if f in ('qL','lL','uR','dR','eR','baruR')]
    if len(fermion_fields) == 4:
        text = record['source'].get('operator', '')
        require('(q_s^{CiT} C l_t^j)' in text and sorted(f['field'] for f in record['fields']) == ['lL','qL'], 'SINGLE_CHAIN_NOT_SOURCE_BOUND')
    else:
        require(len(fermion_fields) == 2, 'SINGLE_CHAIN_NOT_SOURCE_BOUND')
    return dict(directed=directed, right=all(k == 'RIGHT_WEYL' for k in kinds),
                source_spinor_chain_count=len(fermion_fields)//2, touched_spinor_chains=1,
                current_count=len(record['vertices']), fermion_propagators=len(fermions),
                source_derivatives=t['source_derivative_count'], target_derivatives=target['derivative_count'])


def tensor_and_generators(record):
    operator, source = record['operator'], record['source']
    generators = [sp.Matrix([[radical(x) for x in row] for row in matrix]) for matrix in record['generators']]
    size = generators[0].rows
    require(all(g.shape == (size, size) and g == g.conjugate().T and sp.trace(g) == 0 for g in generators), 'GENERATOR_DOMAIN')
    for i, a in enumerate(generators):
        for j, b in enumerate(generators):
            require(sp.simplify(sp.trace(a*b)-sp.Rational(i == j, 2)) == 0, 'GENERATOR_NORMALIZATION')
    if record['tensor'] is not None:
        tensor = {}
        for row in record['tensor']['sparse_entries']:
            index = tuple(row['index'])
            require(index not in tensor, 'RV_DUPLICATE_TENSOR_ENTRY')
            tensor[index] = radical(row['coefficient'])
        axes = record['registered']['component_axis_order']
        pair = axes.index('qL[1].color3'), axes.index('qL[2].color3')
        channel = 'EXACT_REGISTERED_COMPONENT_TENSOR'
    elif 'H_dagger_i epsilon_jk X^{C k}+H_dagger_j epsilon_ik X^{C k}' in source.get('operator',''):
        require(source['flavor_exchange'] == 'O_pr=-O_rp' and source['same_flavor_survives'] is False and size == 2, 'WEAK_SOURCE_PROFILE')
        epsilon = sp.Matrix([[0, 1], [-1, 0]])
        tensor = {(i,j,h,x): sp.Integer(h == i)*epsilon[j,x]+sp.Integer(h == j)*epsilon[i,x] for i,j,h,x in it.product(range(size),repeat=4)}
        pair, channel = (0,1), 'WEAK_TRIPLET_A_FLAVOR'
        require(all(v == tensor[j,i,h,x] for (i,j,h,x),v in tensor.items()), 'WEAK_PAIR_NOT_SYMMETRIC')
    elif source.get('operator') == 'epsilon_ABC (d_R,p^{A T} C d_R,r^B)(H^i epsilon_ij X^{C j})':
        require(size == 3 and source['flavor_exchange'] == 'O_pr=-O_rp', 'COLOR_EPSILON_PROFILE')
        tensor = {i: sp.LeviCivita(*i) for i in it.product(range(size),repeat=3)}
        pair, channel = (0,1), 'SOURCE_EPSILON_COLOR_TENSOR'
    else:
        raise exact.VerificationError('NONABELIAN_SOURCE_CHANNEL_UNSUPPORTED', operator)
    tensor = {k:v for k,v in tensor.items() if v != 0}
    require(tensor, 'SOURCE_TENSOR_ZERO')
    image = {}
    for index, value in tensor.items():
        for g in generators:
            for i,j in it.product(range(size),repeat=2):
                factor = g[i,index[pair[0]]]*g[j,index[pair[1]]]
                if factor != 0:
                    key = list(index)
                    key[pair[0]],key[pair[1]] = i,j
                    key = tuple(key)
                    image[key] = image.get(key,0)+value*factor
    norm2 = sum(sp.conjugate(v)*v for v in tensor.values())
    eigenvalue = sp.simplify(sum(sp.conjugate(v)*image.get(k,0) for k,v in tensor.items())/norm2)
    require(all(sp.simplify(image.get(k,0)-eigenvalue*tensor.get(k,0)) == 0 for k in tensor.keys()|image.keys()), 'GROUP_ACTION_RESIDUAL')
    return eigenvalue, dict(channel=channel, source_nonzero_count=len(tensor), generator_count=len(generators), residual='0')


def group_action(record):
    if record['topology']['coupling_monomial'][0] != 'g1':
        return tensor_and_generators(record)
    charges=[]
    for field, rule in zip(record['fields'],record['vertices']):
        charge=E(field['hypercharge'])
        require(charge == E(rule['generator_representation']) and charge.is_Rational is True, 'RV_CHARGE_RULE_MISMATCH')
        require(rule['exact_rule'] == '+i*g1*gamma^mu*T_'+field['hypercharge'], 'RV_U1_RULE_PROFILE')
        charges.append(charge)
    return sp.prod(charges), dict(channel='ABELIAN_ENDPOINT_CHARGE_PRODUCT',charges=charges,
                                 directed_orientation_in_spinor_kernel=True)


def spinor_action(profile, conventions):
    require(conventions['regularization']['metric_signature'] == '+---', 'RV_METRIC_PROFILE')
    require('C=i*gamma^2*gamma^0_IN_THE_FOUR_DIMENSIONAL_PHYSICAL_SUBSPACE' in conventions['dirac']['charge_conjugation'], 'RV_CHARGE_CONJUGATION_PROFILE')
    identity,zero=sp.eye(2),sp.zeros(2)
    pauli=[sp.Matrix([[0,1],[1,0]]),sp.Matrix([[0,-sp.I],[sp.I,0]]),sp.diag(1,-1)]
    block=lambda a,b,c,d: sp.Matrix.vstack(sp.Matrix.hstack(a,b),sp.Matrix.hstack(c,d))
    gamma=[block(identity,zero,zero,-identity)]+[block(zero,m,-m,zero) for m in pauli]
    eta=(1,-1,-1,-1)
    for i,j in it.product(range(4),repeat=2):
        require(gamma[i]*gamma[j]+gamma[j]*gamma[i] == 2*(eta[i] if i==j else 0)*sp.eye(4),'RV_CLIFFORD')
    g5=sp.I*gamma[0]*gamma[1]*gamma[2]*gamma[3]
    proj=(sp.eye(4)+(1 if profile['right'] else -1)*g5)/2
    c=sp.I*gamma[2]*gamma[0]
    tree=proj if profile['directed'] else c*proj
    metric=sp.zeros(4)
    for mu,rho in it.product(range(4),repeat=2):
        word=gamma[rho]*gamma[mu]
        term=gamma[mu]*gamma[rho]*tree*gamma[rho]*gamma[mu] if profile['directed'] else -word.T*tree*word
        metric+=sp.Rational(eta[mu]*eta[rho],len(eta))*term
    # Evaluate the Ward contraction with an explicit generic momentum word.
    ps=sp.symbols('p0:4')
    slash=sum((ps[i]*gamma[i] for i in range(4)),sp.zeros(4))
    p2=sum(eta[i]*ps[i]**2 for i in range(4))
    square=(slash*slash).applyfunc(sp.expand)
    require(square==p2*sp.eye(4),'RV_WARD')
    longitudinal=(square*tree*square if profile['directed'] else -square.T*tree*square).applyfunc(lambda v:sp.cancel(v/p2**2))
    norm2=sp.trace(tree.conjugate().T*tree)
    metric_coefficient=sp.simplify(sp.trace(tree.conjugate().T*metric)/norm2)
    longitudinal_coefficient=sp.simplify(sp.trace(tree.conjugate().T*longitudinal)/norm2)
    require(metric==metric_coefficient*tree and longitudinal==longitudinal_coefficient*tree,'RV_SPINOR_PROJECTION_RESIDUAL')
    return dict(metric=metric_coefficient,longitudinal=longitudinal_coefficient,tree_norm=norm2)


def absence_certificate(profile, conventions):
    require(profile['touched_spinor_chains']==1 and profile['current_count']==2 and profile['fermion_propagators']==2 and
            profile['source_derivatives']==profile['target_derivatives']==0,'ABSENCE_DOMAIN_REJECTED')
    require(conventions['regularization']['uv_poles_retained_for_closure']==['1/epsilon'],'ABSENCE_POLE_ORDER')
    h=sp.Symbol('h')
    d=4+h
    # Pairings of four gamma indices on a single scalar chain. No open index.
    pairings=((0,0,1,1),(0,1,0,1),(0,1,1,0))
    witnesses=[]
    for word in pairings:
        for a,b in it.product((sp.Integer(4),h),repeat=2):
            scalar=a*(2-a) if word==(0,1,0,1) and a==b else (-a*b if word==(0,1,0,1) else a*b)
            require(d.subs(h,0)!=0 and (d*(d+2)).subs(h,0)!=0,'ABSENCE_DENOMINATOR')
            if h in (a,b):
                require(sp.rem(scalar,h)==0,'ABSENCE_HAT_FACTOR')
            witnesses.append(dict(word=list(word),sectors=[p.serial(a),p.serial(b)],scalar=p.serial(scalar)))
    return dict(method='ANALYTIC_ABSENCE',evidence_profile='SINGLE_SCALAR_CHAIN',evaluated=True,
                state='EVALUATED_ZERO',value='0',witnesses=witnesses,
                domain=profile,finite_continuation_terms='NOT_DETERMINED')


def calculate(inputs):
    outputs=[]
    for record in inputs['records']:
        profile=domain(record)
        group,group_receipt=group_action(record)
        spin=spinor_action(profile,inputs)
        gauge=record['topology']['coupling_monomial'][0]
        require(any(s.startswith('xi_'+gauge[1:]+'_') for s in inputs['gauge_parameters']),'RV_GAUGE_PARAMETER')
        coupling,xi=sp.Symbol(gauge),sp.Symbol('xi'+gauge[1:])
        raw=sp.cancel(coupling**2*group*(spin['metric']-(1-xi)*spin['longitudinal']))
        # The source/tree identity map transports the coefficient, not 1.
        normalized=exact.arithmetic('INVERTIBLE_NORMALIZATION',[raw,sp.Integer(1),sp.Integer(1)])
        outputs.append(dict(record_id=record['record_id'],operator=record['operator'],physical_coefficient=normalized,
                            group=group,group_receipt=group_receipt,spinor=spin,profile=profile,
                            normalization=dict(input=raw,scale=sp.Integer(1),inverse=sp.Integer(1),output=normalized),
                            evanescent=absence_certificate(profile,inputs)))
    require({r['record_id'] for r in outputs}==set(RECORDS) and len(outputs)==6,'RV_RECORD_SET')
    return outputs
