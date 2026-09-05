"""Fine-grained C03 physical transcript from the existing source calculator.

The candidate never imports the independent verifier or comparison contract.
This fragment does not stand in for the other fifteen seven-record outputs.
"""
from __future__ import annotations

from formal.python.toe.generic_runner import c03_physical_dag_profile_v1 as p
from formal.python.toe.generic_runner import c03_source_derivation_v1 as c


def from_calculation(material, calculation):
    """Producer transcript; checker must not trust the supplied calculation."""
    weights, phase = calculation['weights'], calculation['phase']
    numerator, reference = calculation['numerator'], calculation['reference']
    values = {
        'DERIVED.GRASSMANN_EXCHANGE_SIGN': weights['grassmann'],
        'DERIVED.COLOR_EXCHANGE_SIGN': weights['color'],
        'DERIVED.IDENTITY_OCCURRENCE_WEIGHT': weights['IDENTITY'],
        'DERIVED.EXCHANGE_OCCURRENCE_WEIGHT': weights['IDENTICAL_UR_EXCHANGE'],
        'DERIVED.COVARIANT_NUMERATOR': numerator['covariant'],
        'DERIVED.CHARGE_PRODUCT': phase['charge_product'],
        'DERIVED.RAW_GRAPH': numerator['covariant'] * phase['phase'] * phase['charge_product'],
        'DERIVED.REMOVED_MONOMIAL': reference['removed_monomial'],
        'DERIVED.REFERENCE_SCALAR': reference['reference_scalar'],
        'DERIVED.TARGET_NORMALIZATION_SCALE': reference['raw_to_common_scale'],
        'DERIVED.COMMON_NORMALIZED_COEFFICIENT': calculation['common_kernel_coefficient'],
        'OUTPUT.PHYSICAL_COEFFICIENT': calculation['common_kernel_coefficient'],
    }
    for name in ('G_X', 'G_Y', 'L_X', 'L_Y', 'G_SUM', 'L_SUM', 'PT_SUM'):
        values['DERIVED.' + name] = numerator[name]
    nodes = []
    for key, source in material.items():
        nodes.append(dict(node_id=key, **source, parents=[], domain_status='IN_DOMAIN',
                          epistemic_status='SOURCE_BOUND'))
    for key, spec in p.derived_specs().items():
        value = values[key.removeprefix(p.PREFIX)]
        if spec['semantic_type'] == 'BASIS_VECTOR_XY':
            value = [c.serial(v) for v in value]
        else:
            value = c.serial(value)
        nodes.append(dict(node_id=key, **spec, typed_value=value, domain_status='IN_DOMAIN',
                          epistemic_status='DERIVED_CHECKABLE', evidence_refs=[]))
    graph = dict(nodes=nodes, edges=[[parent, node['node_id']] for node in nodes for parent in node['parents']])
    p.seal_graph(graph)
    return dict(schema_id=p.SCHEMA, graph=graph, scope='C03_PHYSICAL_FRAGMENT_ONLY',
                outputs={p.ROOT_ID: c.serial(calculation['common_kernel_coefficient'])})


def compute(root=c.norm.ROOT):
    material, _ = p.source_material(root)
    return from_calculation(material, c.calculate(c.load_inputs(root)))


if __name__ == '__main__':
    print(c.exact.canonical(compute()))
