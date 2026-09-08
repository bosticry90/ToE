"""Tests of the C03 fragment, not a claim of full seven-record qualification."""
from copy import deepcopy

import pytest
import sympy as sp

from formal.python.toe.generic_runner import c03_physical_dag_candidate_v1 as candidate
from formal.python.toe.generic_runner import c03_physical_dag_profile_v1 as p
from formal.python.toe.generic_runner import c03_physical_dag_verifier_v1 as check
from formal.python.toe.generic_runner import c03_source_derivation_v1 as c


@pytest.fixture(scope='module')
def source(): return c.load_inputs()


@pytest.fixture(scope='module')
def material(): return p.source_material()[0]


@pytest.fixture(scope='module')
def packet(): return candidate.compute()


def node(packet, suffix):
    return next(n for n in packet['graph']['nodes'] if n['node_id'] == p.PREFIX + suffix)


def test_positive_fragment_recomputed_from_sources(packet):
    receipt = check.verify(packet)
    assert receipt['node_count'] == len(packet['graph']['nodes'])
    assert len(receipt['receipts']) == receipt['node_count']
    assert receipt['candidate_routines_called'] is False
    assert receipt['full_seven_record_dag'] is receipt['scientific_requalification'] is False
    assert sp.cancel(c.E(packet['outputs'][p.ROOT_ID]) - (sp.Symbol('xi1') - 1)) == 0


def test_checker_does_not_call_candidate_calculations(packet, monkeypatch):
    def prohibited(*a, **k): raise AssertionError('Producer call')
    for name in ('calculate', 'physical_numerator', 'orbit_weights', 'phase_and_charge', 'clifford', 'spinor_basis'):
        monkeypatch.setattr(c, name, prohibited)
    for name in ('derive_reference', 'verify_reference', 'map_raw'):
        monkeypatch.setattr(c.norm, name, prohibited)
    monkeypatch.setattr(candidate, 'compute', prohibited)
    assert check.verify(packet)['candidate_routines_called'] is False


@pytest.mark.parametrize('suffix', [key.removeprefix(p.PREFIX) for key in p.derived_specs()])
def test_every_false_derived_value_rejected_even_with_correct_final_output(packet, suffix):
    bad = deepcopy(packet)
    target = node(bad, suffix)
    if isinstance(target['typed_value'], list):
        target['typed_value'][0] = '999'
    else:
        target['typed_value'] = '999'
    p.seal_graph(bad['graph'])
    with pytest.raises(c.exact.VerificationError): check.verify(bad)


@pytest.mark.parametrize('mutation,code', [
    ('unknown_operation', 'UNKNOWN_OPERATION'),
    ('unknown_parameter', 'UNDECLARED_NODE_FIELD'),
    ('missing_source', 'SOURCE_BINDING_OR_VALUE_MISMATCH'),
    ('same_value_other_source', 'SOURCE_BINDING_OR_VALUE_MISMATCH'),
    ('parent_bypass', 'OPERATION_SIGNATURE_MISMATCH'),
    ('stale_edge', 'PARENT_EDGE_MISMATCH'),
    ('unrelated_node', 'DECORATIVE_OR_DISCONNECTED_NODE'),
    ('claim_certified', 'DERIVED_EVIDENCE_OR_STATUS'),
    ('output_corruption', 'EMITTED_COEFFICIENT_MISMATCH'),
])
def test_historical_false_acceptance_patterns_rejected(packet, mutation, code):
    bad = deepcopy(packet)
    target = node(bad, 'DERIVED.G_X')
    if mutation == 'unknown_operation': target['operation'] = 'UNDECLARED_TARGET_LOOKUP'
    elif mutation == 'unknown_parameter': target['operation_parameters'] = {'target': [2, -2]}
    elif mutation in ('missing_source', 'same_value_other_source'):
        ref = node(bad, 'SOURCE.HYPERCHARGE_D')['evidence_refs'][0]
        if mutation == 'missing_source': ref['artifact_path'] = 'missing/source.json'
        else: ref['semantic_locator'] = '/another_container_with_same_number'
    elif mutation in ('parent_bypass', 'stale_edge'):
        node(bad, 'OUTPUT.PHYSICAL_COEFFICIENT')['parents'] = ['C03.SOURCE.HYPERCHARGE_D']
        if mutation == 'parent_bypass':
            # Keep original derivation connected, so rejection tests the exact
            # signature and does not rely solely on disconnected-node checks.
            node(bad, 'OUTPUT.PHYSICAL_COEFFICIENT')['parents'].append('C03.DERIVED.COMMON_NORMALIZED_COEFFICIENT')
            bad['graph']['edges'] = [[a, n['node_id']] for n in bad['graph']['nodes'] for a in n['parents']]
    elif mutation == 'unrelated_node':
        extra = deepcopy(node(bad, 'SOURCE.HYPERCHARGE_D'))
        extra['node_id'] = 'C03.SOURCE.DECORATION'
        bad['graph']['nodes'].append(extra)
    elif mutation == 'claim_certified': target['epistemic_status'] = 'CERTIFIED'
    elif mutation == 'output_corruption': bad['outputs'][p.ROOT_ID] = '999'
    p.seal_graph(bad['graph'])
    with pytest.raises(c.exact.VerificationError, match=code): check.verify(bad)


@pytest.mark.parametrize('suffix', [
    'SOURCE.ORDERED_FIELDS', 'SOURCE.COLOR_TENSOR', 'SOURCE.SPINOR_X', 'SOURCE.SPINOR_Y',
    'SOURCE.CLIFFORD_DOMAIN', 'SOURCE.GAUGE_PARAMETER', 'SOURCE.HYPERCHARGE_D',
    'SOURCE.HYPERCHARGE_E', 'SOURCE.DIAGRAM_PHASE', 'SOURCE.COMMON_PREFACTOR',
    'SOURCE.COUPLING_MONOMIAL', 'SOURCE.NORMALIZATION_DOMAIN', 'CONVENTION.WILSON_SYMBOL',
])
def test_claimed_source_cannot_override_bound_bytes(packet, suffix):
    bad = deepcopy(packet)
    target = node(bad, suffix)
    target['typed_value'] = {'invented': True}
    p.seal_graph(bad['graph'])
    with pytest.raises(c.exact.VerificationError, match='SOURCE_BINDING_OR_VALUE_MISMATCH'): check.verify(bad)


def test_independent_matrix_route_agrees_with_candidate(source, material):
    result = c.calculate(source)
    a = material['C03.SOURCE.SPINOR_X']['typed_value']
    b = material['C03.SOURCE.SPINOR_Y']['typed_value']
    domain = material['C03.SOURCE.CLIFFORD_DOMAIN']['typed_value']
    for label, first, other in [('X', a, b), ('Y', b, a)]:
        assert check.spinor_action(first, other, domain) == tuple(result['numerator']['G_' + label])
        assert check.spinor_action(first, other, domain, ward=True) == tuple(result['numerator']['L_' + label])


def test_phase_route_independent_residue_and_routing(source, material):
    ledger = material['C03.SOURCE.DIAGRAM_PHASE']['typed_value']
    phase, detail = check.phase_product(ledger)
    assert phase == c.phase_and_charge(source)['phase']
    assert len(detail['factors']) == 8


@pytest.mark.parametrize('index', [0, 1])
def test_phase_decoded_input_change_recomputed(material, index):
    ledger = deepcopy(material['C03.SOURCE.DIAGRAM_PHASE']['typed_value'])
    before = check.phase_product(ledger)[0]
    ledger['vertices'][index]['exact_rule'] = ledger['vertices'][index]['exact_rule'].replace('+i*', '-i*')
    assert check.phase_product(ledger)[0] == -before


@pytest.mark.parametrize('field,value', [('dimension', 'd=3'), ('metric_signature', '-+++')])
def test_bad_regulator_domain_rejected(material, field, value):
    ledger = deepcopy(material['C03.SOURCE.DIAGRAM_PHASE']['typed_value'])
    ledger['regularization'][field] = value
    with pytest.raises(c.exact.VerificationError, match='REGULATOR_DOMAIN'): check.phase_product(ledger)


def test_opposite_i0_rejected(material):
    ledger = deepcopy(material['C03.SOURCE.DIAGRAM_PHASE']['typed_value'])
    ledger['propagators'][0]['rule'] = ledger['propagators'][0]['rule'].replace('+i*0', '-i*0')
    with pytest.raises(c.exact.VerificationError, match='FERMION_PRESCRIPTION'): check.phase_product(ledger)


def test_non_target_direction_cannot_be_projected_away():
    with pytest.raises(c.exact.VerificationError, match='TARGET_DIRECTION_RESIDUAL'):
        check.operation('C03.DERIVED.COMMON_NORMALIZED_COEFFICIENT',
                        [(sp.Integer(1), sp.Integer(2)), sp.Integer(3), sp.Rational(1, 3)])


def test_wrong_inverse_cannot_be_claimed():
    with pytest.raises(c.exact.VerificationError, match='NORMALIZATION_INVERSE'):
        check.operation('C03.DERIVED.COMMON_NORMALIZED_COEFFICIENT',
                        [(sp.Integer(1), sp.Integer(1)), sp.Integer(3), sp.Integer(1)])


@pytest.mark.parametrize('count', [1, 7, True])
def test_target_derivative_domain_is_actually_checked(material, count):
    context = deepcopy(material['C03.SOURCE.ORDERED_FIELDS']['typed_value'])
    context['target']['derivative_count'] = count
    with pytest.raises(c.exact.VerificationError, match='TARGET_SOURCE_DOMAIN'):
        check.field_permutation(context, True)


def test_charge_perturbation_changes_producer_and_independent_chain(source, material):
    # Explicit decoded-input test. This is not a rebinding of the frozen input
    # manifest and does not claim full clean-zone source mutation custody.
    changed_source = deepcopy(source)
    changed_source['fields'][0]['hypercharge'] = '-2/3'
    changed_source['vertices'][0]['generator_representation'] = '-2/3'
    changed_source['vertices'][0]['exact_rule'] = '+i*g1*gamma^mu*T_-2/3'
    base = c.calculate(source)
    changed = c.calculate(changed_source)
    changed_material = deepcopy(material)
    changed_material['C03.SOURCE.HYPERCHARGE_D']['typed_value'] = '-2/3'
    for suffix in ('SOURCE.SPINOR_X', 'SOURCE.SPINOR_Y', 'SOURCE.DIAGRAM_PHASE'):
        changed_material[p.PREFIX + suffix]['typed_value']['vertices'] = changed_source['vertices']
    changed_material['C03.SOURCE.DIAGRAM_PHASE']['typed_value']['fields'] = changed_source['fields']
    packet = candidate.from_calculation(changed_material, changed)
    result = check.verify_material(packet, changed_material, [])
    assert result['candidate_routines_called'] is False
    assert c.E(packet['outputs'][p.ROOT_ID]) == 2 * base['common_kernel_coefficient']
    assert changed['reference'] == base['reference']
