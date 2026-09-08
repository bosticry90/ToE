"""Trusted C03 physical operation implementation.

No imports of candidate, source calculator, old result packet or oracle. Uses
the same exact-algebra library and admitted source assumptions. This is an
author-written independent algorithm, NOT non-author physics peer review.
"""
from __future__ import annotations

import itertools
import re
import sympy as sp

from . import c03_rv_operation_support as x

E, require = x.exact_expr, x.require


def scalar_text(value):
    return sp.sstr(sp.cancel(value))


def encode(value):
    if isinstance(value, sp.Basic): return scalar_text(value)
    if isinstance(value, tuple): return [encode(v) for v in value]
    if isinstance(value, sp.MatrixBase): return [[encode(value[i, j]) for j in range(value.cols)] for i in range(value.rows)]
    return value


def field_permutation(context, exchange):
    target = context['target']
    fields = target['ordered_fields']
    require(fields == ['dR', 'uR', 'uR', 'eR'] and context['component_order'] == fields, 'ORDERED_FIELD_DOMAIN')
    require(target['fermionic_labeled_slot_orbit_size'] == 2, 'ORBIT_DOMAIN')
    require(type(target['derivative_count']) is int and target['derivative_count'] == 0
            and target['dimension'] == 6 and target['lorentz_class'] == 'FOUR_FERMION_BMHV', 'TARGET_SOURCE_DOMAIN')
    positions = [i for i, name in enumerate(fields) if name == 'uR']
    permutation = sp.eye(len(fields))
    if exchange:
        permutation.row_swap(*positions)
    # Determinant is a distinct parity implementation from the producer's
    # inversion count. It does not read the producer's claimed sign.
    return permutation.det()


def color_eigenvalue(context):
    axes = context['axes']
    require(len(set(axes)) == len(axes), 'COLOR_AXIS_DUPLICATE')
    a, b = axes.index('uR[1].color3'), axes.index('uR[2].color3')
    entries = {}
    for row in context['tensor']['sparse_entries']:
        index = tuple(row['index'])
        require(len(index) == len(axes) and all(type(i) is int and 0 <= i < 3 for i in index)
                and index not in entries, 'COLOR_ENTRY_DOMAIN')
        entries[index] = E(row['coefficient'])
    require(entries and any(entries.values()), 'COLOR_TENSOR_ZERO')
    ratios = set()
    for index in itertools.product(range(3), repeat=len(axes)):
        changed = list(index)
        changed[a], changed[b] = changed[b], changed[a]
        before, after = entries.get(index, 0), entries.get(tuple(changed), 0)
        if before:
            ratios.add(sp.cancel(after / before))
        else:
            require(after == 0, 'COLOR_EXCHANGE_RESIDUAL')
    require(len(ratios) == 1 and next(iter(ratios)) in (-1, 1), 'COLOR_EXCHANGE_NOT_SIGN')
    return next(iter(ratios))


def spinor_vector(context):
    operator, target, rows = context['operator'], context['target'], context['occurrences']
    require(operator['operator'] == 'Q_duue[p,r,s,t]=epsilon_ABC (d_p^{AT} C u_r^B)(u_s^{CT} C e_t)', 'BILINEAR_SOURCE_DOMAIN')
    require(operator['normalization'] == 'DISPLAYED_WARSAW_TENSOR_WITH_NO_EXTRA_SYMMETRY_FACTOR', 'BILINEAR_NORMALIZATION')
    require(target['ordered_fields'] == ['dR', 'uR', 'uR', 'eR'], 'BILINEAR_FIELD_ORDER')
    require(type(target['derivative_count']) is int and target['derivative_count'] == 0, 'TARGET_SOURCE_DOMAIN')
    require(rows and len({r['occurrence_id'] for r in rows}) == len(rows), 'BILINEAR_OCCURRENCE_DOMAIN')
    fields = ['dR', 'uR_1', 'uR_2', 'eR']
    partitions, orbit_ids = set(), set()
    for row in rows:
        require(row['field_order'] == fields, 'OCCURRENCE_FIELD_ORDER')
        orbit = row['source_orbit']
        chains = orbit['chain_fields']
        require(set(chains) == {'LEFT_DU', 'RIGHT_UE'}, 'CHAIN_FIELD_DOMAIN')
        partition = tuple(tuple(fields.index(f) for f in chains[k]) for k in row['chain_order'])
        require(sorted(i for pair in partition for i in pair) == list(range(4)), 'BILINEAR_PARTITION')
        partitions.add(partition)
        orbit_ids.add(orbit['orbit_id'])
        words = {word['chain_id']: word for word in row['gamma_chains']}
        require(set(words) == {'LEFT_DU', 'RIGHT_UE'}, 'GAMMA_CHAIN_DOMAIN')
        for name, slots in [('LEFT_DU', ['G_L', 'P_L']), ('RIGHT_UE', ['P_R', 'G_R'])]:
            word = words[name]
            require(word['chirality_projector'] == 'RIGHT', 'CHIRALITY_DOMAIN')
            require([f['lorentz_slot'] for f in word['source_factors']] == slots and
                    all(f['kind'] == 'GAMMA' and f['sector'] in ('BAR', 'HAT') for f in word['source_factors']), 'GAMMA_WORD_DOMAIN')
        angular = row['angular_average']
        require(len(angular['pairing_terms']) == 1 and angular['master_rank'] in (2, 4), 'ANGULAR_DOMAIN')
        term = angular['pairing_terms'][0]
        require(len(term['metric_pairs']) == 2 and sorted(s for pair in term['metric_pairs']
                for s in (pair['left_slot'], pair['right_slot'])) == ['G_L', 'G_R', 'P_L', 'P_R'], 'METRIC_PAIRING_DOMAIN')
        dimension = sp.Symbol('d')
        denominator = sp.prod(dimension + i for i in range(0, angular['master_rank'], 2))
        require(sp.cancel(E(term['exact_weight']) * denominator - 1) == 0, 'ANGULAR_WEIGHT_DOMAIN')
    require(len(partitions) == len(orbit_ids) == 1, 'ORBIT_PAIRING_CONTRADICTION')
    epsilon = lambda i, j: j - i  # epsilon_01=+1, epsilon_10=-1
    partition = next(iter(partitions))
    vector = sp.Matrix([sp.prod(epsilon(index[a], index[b]) for a, b in partition)
                        for index in itertools.product(range(2), repeat=4)])
    return vector, next(iter(orbit_ids))


def spinor_action(primary, other, domain, ward=False):
    require(domain['regularization']['metric_signature'] == '+---' and
            domain['regularization']['dimension'] == 'd=4-2*epsilon', 'CLIFFORD_METRIC_DOMAIN')
    require(domain['dirac']['projector_traces']['bar_g_mu_nu_bar_g^nu_mu'] == '4', 'PHYSICAL_DIMENSION_DOMAIN')
    require(domain['lift']['projection_coefficients'] == 'EVALUATED_EXACTLY_AT_d=4_AND_INDEPENDENT_OF_EPSILON', 'P4_DOMAIN')
    first, first_id = spinor_vector(primary)
    second, second_id = spinor_vector(other)
    by_id = {first_id: first, second_id: second}
    require(set(by_id) == {'IDENTITY', 'IDENTICAL_UR_EXCHANGE'}, 'SPINOR_ORBIT_SET')
    basis = sp.Matrix.hstack(by_id['IDENTITY'], by_id['IDENTICAL_UR_EXCHANGE'])
    require(basis.rank() == 2, 'DEGENERATE_TREE_BASIS')
    sigma = [sp.eye(2), sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.diag(1, -1)]
    metric = [1, -1, -1, -1]
    bar = [metric[i] * sigma[i] for i in range(4)]
    zero = sp.zeros(2)
    gamma = [zero.row_join(sigma[i]).col_join(bar[i].row_join(zero)) for i in range(4)]
    for i, j in itertools.product(range(4), repeat=2):
        require(gamma[i] * gamma[j] + gamma[j] * gamma[i] == 2 * (metric[i] if i == j else 0) * sp.eye(4), 'CLIFFORD_ALGEBRA')
    momenta = sp.symbols('k0:4')
    slash = sum((momenta[i] * gamma[i] for i in range(4)), sp.zeros(4))
    square = (slash * slash).applyfunc(sp.expand)
    k2 = sum(metric[i] * momenta[i] ** 2 for i in range(4))
    require(square == k2 * sp.eye(4), 'WARD_IDENTITY')
    if ward:
        image = (sp.trace(square) / (len(gamma) * k2)) * first
    else:
        endpoints = [r['functional_derivative_order'][1] for r in primary['vertices']]
        require(len(endpoints) == 2 and set(endpoints) == {'dR', 'eR'}, 'CROSS_BILINEAR_ENDPOINTS')
        require(primary['vertices'] == other['vertices'], 'ENDPOINT_SOURCE_CONFLICT')
        axes = [primary['target']['ordered_fields'].index(f) for f in endpoints]
        # Full tensor-product operator, rather than the producer's component
        # index loop. The XY coordinates are solved from the entire image.
        action = sp.zeros(first.rows)
        for rho, mu in itertools.product(range(4), repeat=2):
            factors = [sp.eye(2) for _ in range(4)]
            for axis in axes:
                factors[axis] = (bar[rho] * sigma[mu]).T
            action += sp.Rational(metric[rho] * metric[mu], len(gamma)) * sp.kronecker_product(*factors)
        image = action * first
    coordinates, parameters = basis.gauss_jordan_solve(image)
    require(parameters.rows == 0 and basis * coordinates == image, 'TREE_PROJECTION_RESIDUAL')
    return tuple(sp.cancel(v) for v in coordinates)


def phase_product(ledger):
    topology = ledger['topology']
    require(ledger['fourier']['path_integral_phase'] == 'exp(+i*S)' and
            ledger['fourier']['all_vertex_momenta'] == 'INCOMING_AND_SUM_TO_ZERO', 'FOURIER_DOMAIN')
    require(ledger['regularization']['metric_signature'] == '+---' and
            ledger['regularization']['dimension'] == 'd=4-2*epsilon', 'REGULATOR_DOMAIN')
    edges = topology['internal_edges']
    require(topology['loop_count'] == 1 and topology['vertex_count_including_insertion'] == 3 and len(edges) == 3, 'PHASE_TOPOLOGY_DOMAIN')
    incidence = sp.zeros(3)
    gauge, fermions = [], []
    for i, edge in enumerate(edges):
        a, field, b, conjugate = edge
        require(type(a) is int and type(b) is int and 0 <= a < 3 and 0 <= b < 3 and a != b, 'EDGE_DOMAIN')
        incidence[a, i], incidence[b, i] = -1, 1
        if field.startswith('G'):
            require(field == conjugate, 'GAUGE_ORIENTATION')
            gauge.append(i)
        else:
            require(conjugate == 'bar' + field, 'FERMION_ORIENTATION')
            fermions.append(i)
    require(len(gauge) == 1 and len(fermions) == 2 and incidence.rank() == 2, 'LOOP_ROUTING_DOMAIN')
    unit = sp.zeros(1, len(edges))
    unit[0, gauge[0]] = 1
    route, parameters = incidence.col_join(unit).gauss_jordan_solve(sp.Matrix([0, 0, 0, 1]))
    require(parameters.rows == 0 and all(v in (-1, 1) for v in route), 'ROUTING_SOLUTION_DOMAIN')
    rules = {r['id']: r['rule'] for r in ledger['propagators']}
    f, g = rules['PROP-FERMION'], rules['PROP-QUANTUM-GAUGE']
    require(re.fullmatch(r'[+-]i\*slash\(k\)/\(k\^2-m_f\^2\+i\*0\)', f) is not None, 'FERMION_PRESCRIPTION')
    require(g[:1] in ('+', '-') and g[1:] == 'i*delta_ab*(g_munu-(1-xi)*k_mu*k_nu/(k^2+i*0))/(k^2+i*0)', 'GAUGE_PRESCRIPTION')
    phase = lambda s: sp.I if s.startswith('+i*') else -sp.I if s.startswith('-i*') else None
    vertex_phases = []
    fields = {r['field']: r for r in ledger['fields']}
    require(len(ledger['vertices']) == len(topology['renormalizable_vertex_ids']) == 2, 'VERTEX_COUNT')
    for source_id, vertex in zip(topology['renormalizable_vertex_ids'], ledger['vertices']):
        require(vertex['rule_id'] == source_id.replace('VTX-GAUGE-', 'FR-'), 'VERTEX_SOURCE_BINDING')
        require(vertex['all_momenta_incoming'] is True and vertex['rule_kind'] == 'FERMION_FERMION_QUANTUM_GAUGE', 'VERTEX_DOMAIN')
        order = vertex['functional_derivative_order']
        require(len(order) == 3 and order[0] == 'bar' + order[1] and order[2] == 'G1', 'VERTEX_FIELD_ORDER')
        charge = fields[order[1]]['hypercharge']
        require(E(charge).is_Rational and E(vertex['generator_representation']) == E(charge), 'VERTEX_CHARGE_BINDING')
        require(vertex['exact_rule'][3:] == 'g1*gamma^mu*T_' + charge and phase(vertex['exact_rule']) is not None, 'VERTEX_RULE_SYNTAX')
        vertex_phases.append(phase(vertex['exact_rule']))
    power = len(edges) - len(fermions) // 2
    require(power == 2, 'MASTER_DOMAIN')
    epsilon = sp.Symbol('epsilon')
    # The same declared analytic master identity, independently evaluated as
    # a Laurent residue, not the producer's epsilon*Gamma limiting route.
    master = sp.I * (-1) ** power * sp.residue(sp.gamma(power - 2 + epsilon) / sp.gamma(power), epsilon, 0)
    factors = vertex_phases + [phase(f)] * len(fermions) + [phase(g), master] + [route[i] for i in fermions]
    require(all(v is not None for v in factors), 'PHASE_FACTOR_DOMAIN')
    return sp.simplify(sp.prod(factors)), dict(routing=encode(route), factors=[encode(v) for v in factors],
                                             master_identity='FEYNMAN_PLUS_I0_WICK_ROTATED_N2_SIMPLE_POLE')


def operation(key, parents):
    suffix = key.removeprefix("C03.")
    detail = {}
    if suffix == 'DERIVED.GRASSMANN_EXCHANGE_SIGN': result = field_permutation(parents[0], True)
    elif suffix == 'DERIVED.COLOR_EXCHANGE_SIGN': result = color_eigenvalue(parents[0])
    elif suffix == 'DERIVED.IDENTITY_OCCURRENCE_WEIGHT': result = field_permutation(parents[0], False)
    elif suffix in ('DERIVED.EXCHANGE_OCCURRENCE_WEIGHT', 'DERIVED.CHARGE_PRODUCT'): result = sp.prod(parents)
    elif suffix in ('DERIVED.G_X', 'DERIVED.G_Y', 'DERIVED.L_X', 'DERIVED.L_Y'):
        result = spinor_action(*parents, ward=suffix.startswith('DERIVED.L_'))
    elif suffix in ('DERIVED.G_SUM', 'DERIVED.L_SUM'):
        a, b, v, w = parents
        result = tuple(sp.cancel(a * i + b * j) for i, j in zip(v, w))
    elif suffix == 'DERIVED.PT_SUM': result = tuple(a - b for a, b in zip(*parents))
    elif suffix == 'DERIVED.COVARIANT_NUMERATOR':
        transverse, longitudinal, context = parents
        require(context['monomial'] == ['g1', 'g1'] and 'xi_1_FOR_U1Y' in context['parameters'], 'GAUGE_SYMBOL_BINDING')
        gauge_symbol = sp.Symbol('xi' + context['monomial'][0][1:])
        result = tuple(a + gauge_symbol * b for a, b in zip(transverse, longitudinal))
    elif suffix == 'DERIVED.RAW_GRAPH':
        vector, ledger, charge = parents
        phase, detail = phase_product(ledger)
        result = tuple(phase * charge * v for v in vector)
    elif suffix == 'DERIVED.REMOVED_MONOMIAL':
        gauge, wilson = parents
        symbols = [E(v) for v in gauge]
        require(len(symbols) == 2 and all(isinstance(s, sp.Symbol) for s in symbols) and symbols[0] == symbols[1]
                and isinstance(wilson, sp.Symbol) and wilson not in symbols, 'NORMALIZATION_MONOMIAL_DOMAIN')
        result = sp.prod(symbols) * wilson
    elif suffix == 'DERIVED.REFERENCE_SCALAR':
        prefactor, removed, domain = parents
        topology = domain['topology']
        require(topology['source_insertion_id'] == 'D6-PSI4-DUUE' and topology['source_derivative_count'] == 0
                and topology['target_derivative_count'] == 0 and topology['loop_count'] == 1
                and topology['one_particle_irreducible'] is True, 'NORMALIZATION_SOURCE_DOMAIN')
        require(domain['prefactors'] and all(sp.cancel(E(v) - prefactor) == 0 for v in domain['prefactors']), 'REPEATED_PREFACTOR_CONFLICT')
        result = sp.cancel(prefactor / removed)
        require(result.is_Rational and result != 0, 'REFERENCE_SCALAR_DOMAIN')
    elif suffix == 'DERIVED.TARGET_NORMALIZATION_SCALE':
        require(parents[0] != 0, 'REFERENCE_ZERO')
        result = 1 / parents[0]
    elif suffix == 'DERIVED.COMMON_NORMALIZED_COEFFICIENT':
        raw, scale, inverse = parents
        require(scale != 0 and inverse != 0 and sp.cancel(scale * inverse - 1) == 0, 'NORMALIZATION_INVERSE')
        # Coefficient extraction requires the entire vector to lie along the
        # source tree X+Y. No ignored remainder or selected-component shortcut.
        require(len(raw) == 2 and sp.cancel(raw[0] - raw[1]) == 0, 'TARGET_DIRECTION_RESIDUAL')
        result = raw[0] * scale
    elif suffix == 'OUTPUT.PHYSICAL_COEFFICIENT': result = parents[0]
    else: raise x.VerificationError('PHYSICS_OPERATION_NOT_IMPLEMENTED', key)
    return result, detail
