"""Inactive C03 source calculation, with explicit evaluated intermediates.

No import of a historical runner, comparison oracle, or old result packet.
The authorized source profile is inherited unchanged. This is a calculation
component, not a claim that every Pass-0280 qualification gate is established.
"""
from __future__ import annotations

import argparse
import itertools as it
import re

import sympy as sp

from formal.python.toe.generic_runner import c03_normalization_v1 as norm
from formal.python.toe.generic_runner import provenance_verifier_v4 as exact

require = exact.require
E = exact.exact_expr
OPERATOR = 'D6-PSI4-DUUE'
SUFFIXES = {
    'action': 't_first_r2_active_phase3a_executable_renormalizable_action_and_feynman_rule_contract_pass_0030_v0.json',
    'scheme': 't_first_r2_active_bnv_one_loop_renormalization_convention_contract_phase_0_v0.json',
    'targets': 't_first_r2_active_bnv_target_vertex_semantics_and_scope_pass_0078_v0.json',
    'd6': 't_first_r2_active_bnv_d6_normalized_tensor_flavor_and_pre_eom_reduction_pass_0010_v0.json',
    'components': 't_first_r2_active_bnv_d6_component_cg_phase_and_eom_target_closure_pass_0017_v0.json',
    'universe': 'duue_d1_v2_raw_typed_tensor_universe.json',
}


def serial(value):
    if isinstance(value, sp.MatrixBase):
        return [[serial(value[i, j]) for j in range(value.cols)] for i in range(value.rows)]
    if isinstance(value, sp.Basic):
        return sp.sstr(sp.cancel(value))
    if isinstance(value, dict):
        return {str(k): serial(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [serial(v) for v in value]
    return value


class Sources:
    def __init__(self, root=norm.ROOT):
        self.contract, self.profile = norm.load_contract(root)
        self.bound = exact.BoundSources(root, self.profile['allowed_inputs'])

    def get(self, label, locator):
        rows = [r for r in self.profile['allowed_inputs'] if r['path'].endswith(SUFFIXES[label])]
        require(len(rows) == 1, 'SOURCE_LABEL_NOT_UNIQUE', label)
        row = rows[0]
        return self.bound.resolve(dict(artifact_path=row['path'], artifact_sha256=row['sha256'], semantic_locator=locator))


def load_inputs(root=norm.ROOT):
    sources = Sources(root)
    normalization = norm.load_inputs(root)
    topology = normalization['topology']
    target = sources.get('targets', '/target_vertex_bindings[target_operator_id='+OPERATOR+']')
    operator = sources.get('d6', '/normalized_nonderivative_records/inherited_psi4_warsaw_rows[id=D6-PSI4-Q-DUUE]')
    component = sources.get('components', '/channel_component_registry[id=D6-PSI4-Q-DUUE]')
    color = sources.get('components', '/deduplicated_sparse_component_tensor_table/'+component['component_tensor_fingerprint'])
    vertices = [sources.get('action', '/feynman_rule_registry/gauge_matter_three_point[rule_id='+v.replace('VTX-GAUGE-', 'FR-')+']')
                for v in topology['renormalizable_vertex_ids']]
    fields = [sources.get('action', '/field_registry[field='+field+']') for field in ('dR', 'eR')]
    return dict(normalization=normalization, topology=topology, target=target, operator=operator,
                component=component, color=color, vertices=vertices, fields=fields,
                propagators=[sources.get('action', '/propagator_registry[id='+key+']')
                             for key in ('PROP-FERMION', 'PROP-QUANTUM-GAUGE')],
                fourier=sources.get('action', '/space_time_and_fourier_contract'),
                regularization=sources.get('scheme', '/regularization_and_subtraction'),
                dirac=sources.get('scheme', '/bmhv_dirac_contract'),
                lift=sources.get('scheme', '/physical_operator_lift'),
                gauge_parameters=sources.get('scheme', '/gauge_fixing_and_ghosts/gauge_parameters'),
                occurrences=sources.get('universe', '/typed_tensor_occurrences'),
                source_reads=sources.bound.read_receipts + normalization['field_reads'])


def parity(p):
    require(sorted(p) == list(range(len(p))), 'INVALID_PERMUTATION')
    return sp.Integer((-1)**sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p))))


def sparse_color(blob):
    result = {}
    for row in blob['sparse_entries']:
        index = tuple(row['index'])
        require(index not in result and all(type(i) is int and 0 <= i < 3 for i in index), 'COLOR_INDEX')
        result[index] = E(row['coefficient'])
    require(result and any(v != 0 for v in result.values()), 'COLOR_TENSOR_ZERO')
    return result


def orbit_weights(inputs):
    ordered = inputs['target']['ordered_fields']
    require(ordered == ['dR', 'uR', 'uR', 'eR'], 'C03_FIELD_ORDER_DOMAIN')
    require(inputs['component']['field_order'] == ordered, 'COLOR_FIELD_ORDER_MISMATCH')
    positions = [i for i, field in enumerate(ordered) if field == 'uR']
    require(len(positions) == 2 and inputs['target']['fermionic_labeled_slot_orbit_size'] == 2, 'C03_ORBIT_DOMAIN')
    permutation = list(range(len(ordered)))
    permutation[positions[0]], permutation[positions[1]] = permutation[positions[1]], permutation[positions[0]]
    grassmann = parity(permutation)
    axes = inputs['component']['component_axis_order']
    a, b = axes.index('uR[1].color3'), axes.index('uR[2].color3')
    tensor = sparse_color(inputs['color'])
    swapped = {}
    for index, value in tensor.items():
        transformed = list(index)
        transformed[a], transformed[b] = transformed[b], transformed[a]
        swapped[tuple(transformed)] = value
    norm2 = sum(sp.conjugate(v)*v for v in tensor.values())
    color = sp.cancel(sum(sp.conjugate(v)*swapped.get(k, 0) for k, v in tensor.items())/norm2)
    require(color in (-1, 1), 'COLOR_EXCHANGE_NOT_SIGN')
    require(all(sp.cancel(swapped.get(k, 0)-color*tensor.get(k, 0)) == 0 for k in tensor.keys() | swapped.keys()), 'COLOR_EXCHANGE_RESIDUAL')
    return dict(permutation=permutation, grassmann=grassmann, color=color,
                IDENTITY=parity(list(range(len(ordered)))), IDENTICAL_UR_EXCHANGE=grassmann*color)


def leading_phase(rule):
    require(type(rule) is str, 'PHASE_RULE_TYPE')
    match = re.match(r'^([+-])i\*', rule)
    require(match is not None, 'UNSUPPORTED_PHASE_RULE')
    return sp.I if match[1] == '+' else -sp.I


def phase_and_charge(inputs):
    """Feynman phases plus graph-derived routing and a stated master identity.

    The master phase is the Wick-rotated n=2 massive UV integral, with +i0:
    i*(-1)^n Gamma(n-d/2)/Gamma(n). Its simple-pole residue is calculated,
    not taken from the C03 result. This implements that analytic primitive;
    its physical use remains subject to scientific review.
    """
    topology, fourier = inputs['topology'], inputs['fourier']
    require(fourier['path_integral_phase'] == 'exp(+i*S)' and fourier['all_vertex_momenta'] == 'INCOMING_AND_SUM_TO_ZERO', 'FOURIER_PHASE_DOMAIN')
    require(inputs['regularization']['metric_signature'] == '+---', 'METRIC_SIGNATURE_DOMAIN')
    require(inputs['regularization']['dimension'] == 'd=4-2*epsilon', 'DIMENSION_CONVENTION_DOMAIN')
    edges = topology['internal_edges']
    count = topology['vertex_count_including_insertion']
    require(type(count) is int and count == 3 and len(edges) == 3 and topology['loop_count'] == 1, 'PHASE_TOPOLOGY_DOMAIN')
    incidence = sp.zeros(count, len(edges))
    fermion_indices, gauge_indices = [], []
    for index, (start, field, end, conjugate) in enumerate(edges):
        require(type(start) is int and type(end) is int and 0 <= start < count and 0 <= end < count and start != end, 'INCIDENCE_VERTEX_DOMAIN')
        incidence[start, index], incidence[end, index] = -1, 1
        if field.startswith('G'):
            require(field == conjugate, 'GAUGE_EDGE_CONJUGATION')
            gauge_indices.append(index)
        else:
            require(conjugate == 'bar'+field, 'FERMION_EDGE_ORIENTATION')
            fermion_indices.append(index)
    nullspace = incidence.nullspace()
    require(len(nullspace) == 1 and len(fermion_indices) == 2 and len(gauge_indices) == 1, 'PHASE_LOOP_ROUTING_DOMAIN')
    route = nullspace[0]/nullspace[0][gauge_indices[0]]
    require(all(v in (-1, 1) for v in route), 'NONUNIT_ROUTING')
    reversal = sp.prod(route[i] for i in fermion_indices)
    registry = {r['id']: r for r in inputs['propagators']}
    fermion_rule, gauge_rule = registry['PROP-FERMION']['rule'], registry['PROP-QUANTUM-GAUGE']['rule']
    require(re.fullmatch(r'[+-]i\*slash\(k\)/\(k\^2-m_f\^2\+i\*0\)', fermion_rule) is not None,
            'FEYNMAN_PRESCRIPTION_DOMAIN')
    require(gauge_rule[1:] == 'i*delta_ab*(g_munu-(1-xi)*k_mu*k_nu/(k^2+i*0))/(k^2+i*0)' and gauge_rule[0] in '+-',
            'FEYNMAN_PRESCRIPTION_DOMAIN')
    field_rows = {r['field']: r for r in inputs['fields']}
    vertices, charges = [], []
    for source_id, rule in zip(topology['renormalizable_vertex_ids'], inputs['vertices']):
        require(rule['rule_id'] == source_id.replace('VTX-GAUGE-', 'FR-'), 'GAUGE_RULE_BINDING')
        require(rule['all_momenta_incoming'] is True and rule['rule_kind'] == 'FERMION_FERMION_QUANTUM_GAUGE', 'GAUGE_RULE_DOMAIN')
        order = rule['functional_derivative_order']
        require(len(order) == 3 and order[0] == 'bar'+order[1] and order[2] == 'G1', 'VERTEX_FIELD_ORDER')
        field = field_rows[order[1]]
        charge = E(field['hypercharge'])
        require(charge.is_Rational is True and E(rule['generator_representation']) == charge, 'CHARGE_RULE_MISMATCH')
        require(rule['exact_rule'][3:] == 'g1*gamma^mu*T_'+str(field['hypercharge']), 'GAUGE_RULE_CHARGE_MISMATCH')
        charges.append(charge)
        vertices.append(leading_phase(rule['exact_rule']))
    require(len(vertices) == 2 and len(inputs['vertices']) == 2, 'VERTEX_COUNT_DOMAIN')
    epsilon = sp.Symbol('epsilon', positive=True)
    # Numerator degree two cancels one of the three UV denominator powers.
    power = len(edges) - len(fermion_indices)//2
    require(power == 2, 'MASTER_POLE_DOMAIN')
    residue = sp.limit(epsilon*sp.gamma(power-2+epsilon)/sp.gamma(power), epsilon, 0)
    master_phase = sp.I*(-1)**power*residue
    factors = vertices + [leading_phase(fermion_rule) for _ in fermion_indices] + [leading_phase(gauge_rule), master_phase, reversal]
    phase = sp.simplify(sp.prod(factors))
    return dict(phase=phase, charges=charges, charge_product=sp.prod(charges),
                incidence=incidence, routing=route, momentum_reversal=reversal,
                phase_factors=factors, uv_master_residue=residue, uv_master_phase=master_phase,
                primitive='FEYNMAN_PLUS_I0_WICK_ROTATED_N2_SIMPLE_POLE',
                raw_integrand_rebuilt_from_action=False)


def clifford(inputs):
    require(inputs['regularization']['metric_signature'] == '+---', 'METRIC_SIGNATURE_DOMAIN')
    require(inputs['dirac']['projector_traces']['bar_g_mu_nu_bar_g^nu_mu'] == '4', 'BAR_DIMENSION_DOMAIN')
    require(inputs['lift']['projection_coefficients'] == 'EVALUATED_EXACTLY_AT_d=4_AND_INDEPENDENT_OF_EPSILON', 'P4_DOMAIN')
    identity = sp.eye(2)
    sigma = [identity, sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.diag(1, -1)]
    barsigma = [sigma[0]]+[-m for m in sigma[1:]]
    eta = (1, -1, -1, -1)
    for i, j in it.product(range(len(eta)), repeat=2):
        require(sigma[i]*barsigma[j]+sigma[j]*barsigma[i] == 2*(eta[i] if i == j else 0)*identity, 'CLIFFORD_IDENTITY_FAILED')
    p = sp.symbols('p0:4')
    left = sum((p[i]*barsigma[i] for i in range(4)), sp.zeros(2))
    right = sum((p[i]*sigma[i] for i in range(4)), sp.zeros(2))
    p2 = sum(eta[i]*p[i]**2 for i in range(4))
    ward = (left*right).applyfunc(sp.expand)
    require(ward == p2*identity, 'WARD_IDENTITY_FAILED')
    ward_factor = sp.cancel(sp.trace(ward)/(identity.rows*p2))
    return sigma, barsigma, eta, ward_factor


def spinor_basis(inputs):
    operator = inputs['operator']
    require(operator['operator'] == 'Q_duue[p,r,s,t]=epsilon_ABC (d_p^{AT} C u_r^B)(u_s^{CT} C e_t)', 'SOURCE_BILINEAR_DECODER_DOMAIN')
    require(operator['normalization'] == 'DISPLAYED_WARSAW_TENSOR_WITH_NO_EXTRA_SYMMETRY_FACTOR', 'SOURCE_SYMMETRY_FACTOR_DOMAIN')
    require(inputs['target']['ordered_fields'] == ['dR', 'uR', 'uR', 'eR'], 'SPINOR_FIELD_ORDER')
    fields = ['dR', 'uR_1', 'uR_2', 'eR']
    orbits = {}
    for row in inputs['occurrences']:
        require(row['field_order'] == fields, 'OCCURRENCE_FIELD_ORDER')
        orbit = row['source_orbit']
        chains = orbit['chain_fields']
        require(set(chains) == {'LEFT_DU', 'RIGHT_UE'}, 'SOURCE_CHAIN_SET')
        pairs = tuple(tuple(fields.index(f) for f in chains[key]) for key in row['chain_order'])
        require(sorted(i for pair in pairs for i in pair) == list(range(4)), 'BILINEAR_PARTITION')
        oid = orbit['orbit_id']
        require(oid not in orbits or orbits[oid] == pairs, 'ORBIT_PAIRING_CONTRADICTION')
        orbits[oid] = pairs
        require(all(c['chirality_projector'] == 'RIGHT' for c in row['gamma_chains']), 'SOURCE_CHIRALITY_DOMAIN')
        chains_by_id = {c['chain_id']: c for c in row['gamma_chains']}
        require(set(chains_by_id) == {'LEFT_DU', 'RIGHT_UE'}, 'SOURCE_GAMMA_CHAIN_SET')
        for key, slots in [('LEFT_DU', ['G_L','P_L']), ('RIGHT_UE', ['P_R','G_R'])]:
            factors = chains_by_id[key]['source_factors']
            require([f['lorentz_slot'] for f in factors] == slots and
                    all(f['kind'] == 'GAMMA' and f['sector'] in ('BAR','HAT') for f in factors),
                    'SOURCE_GAMMA_WORD_DOMAIN')
        angular = row['angular_average']
        require(len(angular['pairing_terms']) == 1, 'SOURCE_ANGULAR_DOMAIN')
        pairs = angular['pairing_terms'][0]['metric_pairs']
        require(len(pairs) == 2 and sorted(x for pair in pairs for x in (pair['left_slot'],pair['right_slot'])) == ['G_L','G_R','P_L','P_R'], 'SOURCE_METRIC_PAIRING_DOMAIN')
        rank = angular['master_rank']
        d = sp.Symbol('d')
        expected_weight = 1/d if rank == 2 else 1/(d*(d+2)) if rank == 4 else None
        require(expected_weight is not None and sp.cancel(E(angular['pairing_terms'][0]['exact_weight'])-expected_weight) == 0, 'SOURCE_ANGULAR_WEIGHT_DOMAIN')
    require(set(orbits) == {'IDENTITY', 'IDENTICAL_UR_EXCHANGE'}, 'SOURCE_ORBIT_SET')
    epsilon = sp.Matrix([[0, 1], [-1, 0]])
    indices = list(it.product(range(2), repeat=4))
    vectors = []
    for oid in ('IDENTITY', 'IDENTICAL_UR_EXCHANGE'):
        pairs = orbits[oid]
        vectors.append(sp.Matrix([sp.prod(epsilon[index[a], index[b]] for a, b in pairs) for index in indices]))
    basis = sp.Matrix.hstack(*vectors)
    require(basis.rank() == 2, 'SPINOR_BASIS_DEGENERATE')
    return indices, basis, orbits


def physical_numerator(inputs, weights):
    sigma, barsigma, eta, ward = clifford(inputs)
    indices, basis, pairs = spinor_basis(inputs)
    index_of = {index: i for i, index in enumerate(indices)}
    # Source gauge vertices attach to dR and eR, the two outer spinor slots.
    endpoint_fields = [row['functional_derivative_order'][1] for row in inputs['vertices']]
    require(set(endpoint_fields) == {'dR', 'eR'}, 'CROSS_BILINEAR_ENDPOINT_DOMAIN')
    a_axis, b_axis = [inputs['target']['ordered_fields'].index(f) for f in endpoint_fields]
    def action(vector):
        output = sp.zeros(len(indices), 1)
        for oi, index in enumerate(indices):
            value = 0
            for rho, mu in it.product(range(len(eta)), repeat=2):
                chain = barsigma[rho]*sigma[mu]
                for a, b in it.product(range(2), repeat=2):
                    source = list(index)
                    source[a_axis], source[b_axis] = a, b
                    value += sp.Rational(eta[rho]*eta[mu], len(eta))*chain[a, index[a_axis]]*chain[b, index[b_axis]]*vector[index_of[tuple(source)]]
            output[oi] = sp.simplify(value)
        return output
    gram = basis.T*basis
    columns = []
    for column in range(basis.cols):
        image = action(basis[:, column])
        coordinates = gram.inv()*basis.T*image
        require(image == basis*coordinates, 'PHYSICAL_PROJECTION_RESIDUAL')
        columns.append(coordinates)
    orbit_vector = sp.Matrix([weights['IDENTITY'], weights['IDENTICAL_UR_EXCHANGE']])
    gsum = sp.Matrix.hstack(*columns)*orbit_vector
    lsum = ward*orbit_vector
    ptsum = gsum-lsum
    gauge = inputs['topology']['coupling_monomial']
    require(gauge == ['g1', 'g1'] and 'xi_1_FOR_U1Y' in inputs['gauge_parameters'], 'GAUGE_PARAMETER_BINDING')
    xi = sp.Symbol('xi'+gauge[0][1:])
    covariant = ptsum+xi*lsum
    # Projection onto the source tree X+Y, with a residual check.
    tree = sp.ones(basis.cols, 1)
    coefficient = sp.cancel((tree.T*covariant)[0]/(tree.T*tree)[0])
    require(covariant == coefficient*tree, 'C03_NOT_SOURCE_TARGET_DIRECTION')
    return dict(basis=basis, orbit_pairings=pairs, G_X=columns[0], G_Y=columns[1],
                L_X=sp.eye(basis.cols)[:, 0]*ward, L_Y=sp.eye(basis.cols)[:, 1]*ward,
                G_SUM=gsum, L_SUM=lsum, PT_SUM=ptsum, gauge_parameter=xi,
                covariant=covariant, coefficient=coefficient, ward_factor=ward)


def calculate(inputs):
    require(inputs['topology'] == inputs['normalization']['topology'], 'TOPOLOGY_REFERENCE_MISMATCH')
    weights = orbit_weights(inputs)
    phase = phase_and_charge(inputs)
    numerator = physical_numerator(inputs, weights)
    reference = norm.derive_reference(inputs['normalization'])
    norm.verify_reference(inputs['normalization'], reference)
    raw = sp.cancel(numerator['coefficient']*phase['phase']*phase['charge_product'])
    common = norm.map_raw(serial(raw), inputs['normalization'], reference)
    return dict(weights=weights, phase=phase, numerator=numerator, reference=reference,
                raw_full_graph_coefficient=raw, common_kernel_coefficient=common)


def check_receipt(inputs, claimed):
    """Re-executes this component, not an independent physics implementation."""
    actual = serial(calculate(inputs))
    require(exact.canonical(actual) == exact.canonical(claimed), 'C03_RECOMPUTATION_MISMATCH')
    return dict(status='COMPONENT_RECOMPUTED_FROM_BOUND_INPUTS', independent_physics_route=False)


def receipt(root=norm.ROOT):
    inputs = load_inputs(root)
    calculation = serial(calculate(inputs))
    return dict(schema_id='C03_SOURCE_PHYSICAL_CALCULATION_v1',
                calculation=calculation, source_reads=inputs['source_reads'],
                normalization_policy='FIXED_SOURCE_RECORDED_PREFACTOR',
                execution_class='ANSWER_AWARE_IMPLEMENTATION__COMPARISON_BLIND_SOURCE_EXECUTION',
                full_pass0280_dag=False, native_evanescent_evaluated=False,
                full_seven_record_execution=False, scientific_requalification=False,
                complete_io_audit='NOT_PERFORMED', candidate_activation=False)


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(exact.canonical(receipt()))


if __name__ == '__main__':
    main()
