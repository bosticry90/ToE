"""Source bindings and executable interface, not an answer-bearing oracle.

Both implementations may share these I/O and interface definitions. No physics
operation or expected coefficient is supplied here. Full seven-record gates
remain outside this physical-fragment profile.
"""
from __future__ import annotations

from formal.python.toe.generic_runner import c03_normalization_v1 as norm
from formal.python.toe.generic_runner import provenance_verifier_v4 as x

PREFIX = 'C03.'
ROOT_ID = PREFIX + 'OUTPUT.PHYSICAL_COEFFICIENT'
SCHEMA = 'C03_FINE_PHYSICAL_DAG_v1'
SUFFIXES = {
    'action': 't_first_r2_active_phase3a_executable_renormalizable_action_and_feynman_rule_contract_pass_0030_v0.json',
    'scheme': 't_first_r2_active_bnv_one_loop_renormalization_convention_contract_phase_0_v0.json',
    'targets': 't_first_r2_active_bnv_target_vertex_semantics_and_scope_pass_0078_v0.json',
    'd6': 't_first_r2_active_bnv_d6_normalized_tensor_flavor_and_pre_eom_reduction_pass_0010_v0.json',
    'components': 't_first_r2_active_bnv_d6_component_cg_phase_and_eom_target_closure_pass_0017_v0.json',
    'universe': 'duue_d1_v2_raw_typed_tensor_universe.json',
}


def source_material(root=norm.ROOT):
    contract, profile = norm.load_contract(root)
    sources = x.BoundSources(root, profile['allowed_inputs'])
    # Selection comes from the pre-existing pinned source profile, never from
    # candidate evidence_refs. The candidate cannot redirect an equal value.
    refs = {}

    def get(label, pointer, key):
        rows = [r for r in profile['allowed_inputs'] if r['path'].endswith(SUFFIXES[label])]
        x.require(len(rows) == 1, 'SOURCE_LABEL_NOT_UNIQUE', label)
        row = rows[0]
        ref = dict(artifact_path=row['path'], artifact_sha256=row['sha256'], semantic_locator=pointer)
        value = sources.resolve(ref)
        ref['semantic_locator'] = sources.read_receipts[-1]['canonical_pointer']
        refs[key] = ref
        return value

    topology_ref = contract['source_bindings']['topologies']
    ref = dict(artifact_path=topology_ref['path'], artifact_sha256=topology_ref['sha256'],
               semantic_locator=contract['semantic_locators']['topology'])
    topology = sources.resolve(ref)
    ref['semantic_locator'] = sources.read_receipts[-1]['canonical_pointer']
    refs['topology'] = ref
    target = get('targets', '/target_vertex_bindings[target_operator_id=D6-PSI4-DUUE]', 'target')
    x.require(type(target['derivative_count']) is int and target['derivative_count'] == 0
              and target['dimension'] == 6 and target['lorentz_class'] == 'FOUR_FERMION_BMHV',
              'TARGET_SOURCE_DOMAIN')
    operator = get('d6', '/normalized_nonderivative_records/inherited_psi4_warsaw_rows[id=D6-PSI4-Q-DUUE]', 'operator')
    component = get('components', '/channel_component_registry[id=D6-PSI4-Q-DUUE]', 'component')
    color = get('components', '/deduplicated_sparse_component_tensor_table/' + component['component_tensor_fingerprint'], 'color')
    occurrences = get('universe', '/typed_tensor_occurrences', 'occurrences')
    vertices = [get('action', '/feynman_rule_registry/gauge_matter_three_point[rule_id=' +
                    v.replace('VTX-GAUGE-', 'FR-') + ']', 'vertex' + str(i))
                for i, v in enumerate(topology['renormalizable_vertex_ids'])]
    fields = [get('action', '/field_registry[field=' + f + ']', 'field' + f) for f in ('dR', 'eR')]
    propagators = [get('action', '/propagator_registry[id=' + p + ']', p)
                   for p in ('PROP-FERMION', 'PROP-QUANTUM-GAUGE')]
    fourier = get('action', '/space_time_and_fourier_contract', 'fourier')
    regularization = get('scheme', '/regularization_and_subtraction', 'regularization')
    dirac = get('scheme', '/bmhv_dirac_contract', 'dirac')
    lift = get('scheme', '/physical_operator_lift', 'lift')
    parameters = get('scheme', '/gauge_fixing_and_ghosts/gauge_parameters', 'parameters')
    prefactor = get('universe', '/common_prefactor_factored', 'prefactor')
    projection_flags = [get('universe', '/' + k, k) for k in
                        ('disputed_projection_consumed', 'four_dimensional_projection_performed')]
    x.require(projection_flags == [False, False], 'SOURCE_PROJECTION_ADMISSION')
    material = {}

    def add(key, kind, semantic_type, value, names, operation='SOURCE_DECODE'):
        material[PREFIX + key] = dict(kind=kind, operation=operation, semantic_type=semantic_type,
                                     typed_value=value, evidence_refs=[refs[name] for name in names])

    add('SOURCE.ORDERED_FIELDS', 'SOURCE_FACT', 'LABELLED_FIELD_CONTEXT',
        dict(target=target, component_order=component['field_order']), ['target', 'component'])
    add('SOURCE.COLOR_TENSOR', 'SOURCE_FACT', 'COLOR_EXCHANGE_CONTEXT',
        dict(tensor=color, axes=component['component_axis_order']), ['color', 'component'])
    for label, orbit in [('X', 'IDENTITY'), ('Y', 'IDENTICAL_UR_EXCHANGE')]:
        selected = [r for r in occurrences if r['source_orbit']['orbit_id'] == orbit]
        x.require(selected, 'SOURCE_ORBIT_MISSING')
        add('SOURCE.SPINOR_' + label, 'SOURCE_FACT', 'SOURCE_BILINEAR_CONTEXT',
            dict(operator=operator, target=target, occurrences=selected, vertices=vertices),
            ['operator', 'target', 'occurrences', 'vertex0', 'vertex1'])
    add('SOURCE.CLIFFORD_DOMAIN', 'SOURCE_FACT', 'CLIFFORD_DOMAIN_CONTEXT',
        dict(regularization=regularization, dirac=dirac, lift=lift), ['regularization', 'dirac', 'lift'])
    add('SOURCE.GAUGE_PARAMETER', 'SOURCE_FACT', 'GAUGE_SYMBOL_CONTEXT',
        dict(monomial=topology['coupling_monomial'], parameters=parameters), ['topology', 'parameters'])
    for suffix, field in [('D', 'dR'), ('E', 'eR')]:
        row = next(f for f in fields if f['field'] == field)
        field_ref = dict(refs['field' + field])
        field_ref['semantic_locator'] += '/hypercharge'
        refs['charge' + suffix] = field_ref
        add('SOURCE.HYPERCHARGE_' + suffix, 'SOURCE_FACT', 'RATIONAL', row['hypercharge'], ['charge' + suffix])
    # This source value is the RAW factor ledger, not a derived phase relabeled
    # as a parentless fact. PRODUCT recomputes its routing and phase factors.
    add('SOURCE.DIAGRAM_PHASE', 'SOURCE_FACT', 'RAW_FEYNMAN_LEDGER',
        dict(topology=topology, vertices=vertices, fields=fields, propagators=propagators,
             fourier=fourier, regularization=regularization),
        ['topology', 'vertex0', 'vertex1', 'fielddR', 'fieldeR', 'PROP-FERMION',
         'PROP-QUANTUM-GAUGE', 'fourier', 'regularization'])
    add('SOURCE.COMMON_PREFACTOR', 'SOURCE_FACT', 'SYMBOLIC_SCALAR', prefactor, ['prefactor'])
    refs['coupling'] = dict(refs['topology'])
    refs['coupling']['semantic_locator'] += '/coupling_monomial'
    add('SOURCE.COUPLING_MONOMIAL', 'SOURCE_FACT', 'GAUGE_MONOMIAL', topology['coupling_monomial'], ['coupling'])
    add('SOURCE.NORMALIZATION_DOMAIN', 'SOURCE_FACT', 'NORMALIZATION_DOMAIN_CONTEXT',
        dict(topology=topology, prefactors=[r['factored_scientific_prefactors']['common'] for r in occurrences]),
        ['topology', 'occurrences'])
    refs['notation'] = dict(artifact_path=profile['contract']['path'],
                           artifact_sha256=profile['contract']['sha256'],
                           semantic_locator='/reference_policy/wilson_symbol')
    add('CONVENTION.WILSON_SYMBOL', 'DECLARED_NOTATION_CONVENTION', 'SYMBOL',
        contract['reference_policy']['wilson_symbol'], ['notation'], 'CONTRACT_DECODE')
    return material, sources.read_receipts


def derived_specs():
    """Operation signatures and ordered parents; no expected output values."""
    specs = {}

    def add(key, op, parents, typ='BASIS_VECTOR_XY', kind='DERIVED_FACT'):
        specs[PREFIX + key] = dict(kind=kind, operation=op, semantic_type=typ,
                                  parents=[PREFIX + p for p in parents])

    add('DERIVED.GRASSMANN_EXCHANGE_SIGN', 'PERMUTATION_PARITY', ['SOURCE.ORDERED_FIELDS'], 'SIGN')
    add('DERIVED.COLOR_EXCHANGE_SIGN', 'TENSOR_EXCHANGE_EIGENVALUE', ['SOURCE.COLOR_TENSOR'], 'SIGN')
    add('DERIVED.IDENTITY_OCCURRENCE_WEIGHT', 'PRODUCT', ['SOURCE.ORDERED_FIELDS'], 'SIGN')
    add('DERIVED.EXCHANGE_OCCURRENCE_WEIGHT', 'PRODUCT',
        ['DERIVED.GRASSMANN_EXCHANGE_SIGN', 'DERIVED.COLOR_EXCHANGE_SIGN'], 'SIGN')
    for label in ('X', 'Y'):
        add('DERIVED.G_' + label, 'EXACT_CLIFFORD_ACTION',
            ['SOURCE.SPINOR_' + label, 'SOURCE.SPINOR_' + ('Y' if label == 'X' else 'X'), 'SOURCE.CLIFFORD_DOMAIN'])
        add('DERIVED.L_' + label, 'WARD_REDUCTION',
            ['SOURCE.SPINOR_' + label, 'SOURCE.SPINOR_' + ('Y' if label == 'X' else 'X'), 'SOURCE.CLIFFORD_DOMAIN'])
    for label in ('G', 'L'):
        add('DERIVED.' + label + '_SUM', 'TENSOR_SUM',
            ['DERIVED.IDENTITY_OCCURRENCE_WEIGHT', 'DERIVED.EXCHANGE_OCCURRENCE_WEIGHT',
             'DERIVED.' + label + '_X', 'DERIVED.' + label + '_Y'])
    add('DERIVED.PT_SUM', 'TENSOR_DIFFERENCE', ['DERIVED.G_SUM', 'DERIVED.L_SUM'])
    add('DERIVED.COVARIANT_NUMERATOR', 'LINEAR_COMBINATION',
        ['DERIVED.PT_SUM', 'DERIVED.L_SUM', 'SOURCE.GAUGE_PARAMETER'])
    add('DERIVED.CHARGE_PRODUCT', 'PRODUCT', ['SOURCE.HYPERCHARGE_D', 'SOURCE.HYPERCHARGE_E'], 'RATIONAL')
    add('DERIVED.RAW_GRAPH', 'PRODUCT',
        ['DERIVED.COVARIANT_NUMERATOR', 'SOURCE.DIAGRAM_PHASE', 'DERIVED.CHARGE_PRODUCT'])
    add('DERIVED.REMOVED_MONOMIAL', 'NORMALIZATION_MONOMIAL',
        ['SOURCE.COUPLING_MONOMIAL', 'CONVENTION.WILSON_SYMBOL'], 'SYMBOLIC_SCALAR')
    add('DERIVED.REFERENCE_SCALAR', 'NORMALIZATION_REFERENCE_SCALAR',
        ['SOURCE.COMMON_PREFACTOR', 'DERIVED.REMOVED_MONOMIAL', 'SOURCE.NORMALIZATION_DOMAIN'], 'RATIONAL')
    add('DERIVED.TARGET_NORMALIZATION_SCALE', 'NORMALIZATION_RECIPROCAL', ['DERIVED.REFERENCE_SCALAR'],
        'INVERTIBLE_SCALE', 'NORMALIZATION_MAP')
    add('DERIVED.COMMON_NORMALIZED_COEFFICIENT', 'INVERTIBLE_NORMALIZATION',
        ['DERIVED.RAW_GRAPH', 'DERIVED.TARGET_NORMALIZATION_SCALE', 'DERIVED.REFERENCE_SCALAR'],
        'SYMBOLIC_COEFFICIENT', 'NORMALIZATION_MAP')
    add('OUTPUT.PHYSICAL_COEFFICIENT', 'OUTPUT_BIND', ['DERIVED.COMMON_NORMALIZED_COEFFICIENT'],
        'SYMBOLIC_COEFFICIENT', 'OUTPUT_ROOT')
    return specs


def seal_node(node):
    node['recomputation_digest'] = x.digest({k: v for k, v in node.items() if k != 'recomputation_digest'},
                                           'PASS0281_PROVENANCE_NODE_v0')


def seal_graph(graph):
    for node in graph['nodes']:
        seal_node(node)
    graph['node_count'] = len(graph['nodes'])
    graph['edge_count'] = len(graph['edges'])
    graph['canonical_digest'] = x.digest(dict(nodes=graph['nodes'], edges=graph['edges']), 'PASS0281_DAG_v0')


def structural_contract():
    # A fragment-specific structural policy, explicitly NOT an alteration of
    # the full seven-record acceptance contract or its required root count.
    derived = derived_specs()
    return dict(node_schema=dict(required_fields=['node_id', 'kind', 'semantic_type', 'typed_value',
        'parents', 'operation', 'domain_status', 'epistemic_status', 'evidence_refs', 'recomputation_digest']),
        allowed_node_kinds=['SOURCE_FACT', 'DECLARED_NOTATION_CONVENTION', 'DERIVED_FACT',
                            'NORMALIZATION_MAP', 'OUTPUT_ROOT'],
        allowed_operations=sorted({r['operation'] for r in derived.values()} | {'SOURCE_DECODE', 'CONTRACT_DECODE'}),
        output_roots_required=[ROOT_ID])
