"""C03 native quotient from admitted occurrence and N7/N8 definitions.

Legacy stored orbit signs are not authoritative: external-state weights are
recomputed from ordered fields and the source color tensor. Their replacement
is explicit in the receipt. No coordinate table or comparison packet is read.
"""
from __future__ import annotations

import sympy as sp

from formal.python.toe.generic_runner import c03_source_derivation_v1 as physical

exact, require, E = physical.exact, physical.require, physical.E
SUFFIXES = {
    'census': 'f1_reachable_fierz_request_census.json',
    'fallback': 'native_bmhv_fallback_execution.json',
    'n7': 'native_complete_n7_relation_matrix.json',
    'reps': 'native_n8_14_quotient_representatives.json',
    'dual': 'native_n8_gram_dual_projectors.json',
}


def load_inputs(root=physical.norm.ROOT):
    sources = physical.Sources(root)
    def get(label, pointer):
        rows = [r for r in sources.profile['allowed_inputs'] if r['path'].endswith(SUFFIXES[label])]
        require(len(rows) == 1, 'NATIVE_SOURCE_LABEL')
        row = rows[0]
        return sources.bound.resolve(dict(artifact_path=row['path'], artifact_sha256=row['sha256'], semantic_locator=pointer))
    return dict(requests=get('census', '/request_ledger'), defects=get('fallback', '/typed_defects'),
                columns=get('n7', '/defect_columns'), relations=get('reps', '/rref_matrix'),
                representative=get('dual', '/representative_matrix'), dual=get('dual', '/dual_matrix'),
                quotient=get('dual', '/quotient_projector'), remainder=get('dual', '/relation_remainder_projector'),
                source_reads=sources.bound.read_receipts)


def matrix(spec, row_key, column_key):
    shape = spec['shape']
    require(type(shape) is list and len(shape) == 2 and all(type(n) is int and 0 < n <= 128 for n in shape), 'NATIVE_MATRIX_SHAPE')
    result, seen = sp.zeros(*shape), set()
    for entry in spec['entries']:
        row, col = entry[row_key], entry[column_key]
        require(type(row) is int and type(col) is int and 0 <= row < shape[0] and 0 <= col < shape[1], 'NATIVE_MATRIX_INDEX')
        require((row, col) not in seen, 'NATIVE_DUPLICATE_MATRIX_ENTRY')
        seen.add((row, col))
        result[row, col] = E(entry['coefficient'])
    return result


def structure(row):
    product = sp.Integer(1)
    for chain in row['gamma_chains']:
        source, normal = chain['source_factors'], chain['normal_form_factors']
        key = lambda f: (f['kind'], f['lorentz_slot'], f['sector'], f['source_position'])
        a, b = list(map(key, source)), list(map(key, normal))
        require(len(a) == len(set(a)) and sorted(a) == sorted(b), 'CLIFFORD_SOURCE_MULTISET')
        sign = physical.parity([a.index(f) for f in b])
        require(sign == chain['clifford_reordering_sign'], 'CLIFFORD_REORDERING_RECEIPT')
        product *= sign
    angular = row['angular_average']
    require(len(angular['pairing_terms']) == 1 and angular['master_rank'] in (2, 4), 'ANGULAR_PROFILE')
    pairing = angular['pairing_terms'][0]
    weight = E(pairing['exact_weight'])
    channel = E(angular['channel_prefactor_factored_from_Qd_coefficient'])
    require(sp.cancel(channel-E(row['factored_scientific_prefactors']['channel'])) == 0, 'CHANNEL_PREFACTOR_MISMATCH')
    # The frozen legacy aggregate includes the old external orbit sign.
    # Verify that decomposition, then replace that factor explicitly below.
    legacy = E(row['source_orbit']['grassmann_and_color_parity'])
    require(legacy in (-1, 1), 'LEGACY_ORBIT_SIGN_DOMAIN')
    require(sp.cancel(E(row['exact_coefficient'])-weight*legacy*product) == 0, 'LEGACY_COEFFICIENT_DECOMPOSITION')
    return dict(occurrence_id=row['occurrence_id'], orbit_id=row['source_orbit']['orbit_id'],
                pairing_id=pairing['pairing_id'], clifford_sign=product, angular_weight=weight,
                channel=channel, legacy_external_sign=legacy)


def calculate(source, native, computed_physical):
    rows = [structure(row) for row in source['occurrences']]
    by_id = {r['occurrence_id']: r for r in rows}
    require(len(rows) == len(by_id) == 32, 'NATIVE_SOURCE_OCCURRENCE_SET')
    requests = {r['input_tensor_id']: r for r in native['requests']}
    require(len(requests) == len(native['requests']) == 38, 'NATIVE_REQUEST_SET')
    for oid, row in by_id.items():
        require(oid in requests and requests[oid]['source_orbit'] == row['orbit_id'] and requests[oid]['angular_pairing_id'] == row['pairing_id'], 'NATIVE_REQUEST_SOURCE_JOIN')
    defects = {r['identity_key']['input_tensor_id']: r for r in native['defects']}
    require(len(defects) == len(native['defects']) == 38 and set(defects) == set(requests), 'NATIVE_DEFECT_JOIN')
    columns = sorted(native['columns'], key=lambda r: r['column'])
    require([r['column'] for r in columns] == list(range(38)) and {r['input_tensor_id'] for r in columns} == set(requests), 'NATIVE_COLUMN_JOIN')
    phase_charge = computed_physical['phase']['phase']*computed_physical['phase']['charge_product']
    weights = computed_physical['weights']
    ambient, leakage_row, receipts = sp.zeros(len(columns), 1), sp.zeros(1, len(columns)), []
    for col in columns:
        index, oid = col['column'], col['input_tensor_id']
        if oid in by_id:
            row = by_id[oid]
            require(row['orbit_id'] in ('IDENTITY', 'IDENTICAL_UR_EXCHANGE'), 'ORBIT_UNSUPPORTED')
            weight = weights[row['orbit_id']]
            ambient[index] = sp.cancel(phase_charge*row['channel']*row['angular_weight']*row['clifford_sign']*weight)
            receipts.append(dict(occurrence_id=oid, ambient_index=index,
                                 stored_external_sign=physical.serial(row['legacy_external_sign']),
                                 recomputed_external_sign=physical.serial(weight),
                                 coefficient=physical.serial(ambient[index])))
        defect = defects[oid]
        q = E(defect['physical_q_duue_coefficient'])
        match = physical.re.fullmatch(r'T_open\(d\)-\((.+)\)\*Lift\(Q_duue\)', defect['definition'])
        require(match is not None and sp.cancel(E(match[1])-q) == 0, 'DEFECT_DEFINITION_MISMATCH')
        require(defect['p4_zero_proved_by'] == 'P4_T_MINUS_LIFT_OF_EXACT_F4_P4_T__WITH_P4_COMPOSE_LIFT_EQUALS_ID', 'DEFECT_PROJECTION_DOMAIN')
        # Recompute the consequence of the admitted defining subtraction.
        # This does not newly prove the imported F4 projection coefficient.
        leakage_row[index] = sp.cancel(q-E(match[1]))
        require(sp.cancel(leakage_row[index]-E(defect['p4_of_defect'])) == 0, 'DEFECT_LEAKAGE_RECEIPT_MISMATCH')
    relation = matrix(native['relations'], 'relation_row', 'ambient_column')
    rep = matrix(native['representative'], 'ambient_generator_column', 'quotient_column')
    dual = matrix(native['dual'], 'dual_index', 'ambient_generator_column')
    quotient = matrix(native['quotient'], 'output_ambient_column', 'input_ambient_column')
    remainder = matrix(native['remainder'], 'output_ambient_column', 'input_ambient_column')
    require(relation.cols == 38 and relation.rank() == 24, 'N7_RELATION_RANK')
    require(dual.shape == (14, 38) and rep.shape == (38, 14), 'N8_DIMENSION')
    require(dual*relation.T == sp.zeros(14, relation.rows), 'DUAL_RELATION_ANNIHILATION')
    require(dual*rep == sp.eye(14), 'DUAL_REPRESENTATIVE_IDENTITY')
    require(quotient == rep*dual and quotient+remainder == sp.eye(38), 'PROJECTOR_DECOMPOSITION')
    coordinates = (dual*ambient).applyfunc(sp.cancel)
    projected = (rep*coordinates).applyfunc(sp.cancel)
    residual = (ambient-projected-remainder*ambient).applyfunc(sp.cancel)
    leakage = (leakage_row*projected)[0]
    require(residual == sp.zeros(38, 1) and leakage == 0, 'NATIVE_RESIDUAL_OR_LEAKAGE')
    state = 'EVALUATED_NONZERO' if any(v != 0 for v in coordinates) else 'EVALUATED_ZERO'
    xi = computed_physical['numerator']['gauge_parameter']
    return dict(ambient=ambient, coordinates=coordinates, state=state,
                physical_leakage=leakage, unexplained_residual=residual,
                xi1_equals_1_nonzero_count=sum(sp.cancel(v.subs(xi, 1)) != 0 for v in coordinates),
                occurrence_coefficients=receipts, relation_rank=relation.rank(),
                derived_extension_columns_with_no_original_occurrence=[r['column'] for r in columns if r['input_tensor_id'] not in by_id],
                normalization='RELATIVE_TO_i*C_DUUE*(g1^2/(16*pi^2*epsilon))',
                method='NATIVE_QUOTIENT_PROJECTION',
                admitted_F4_P4_coefficients_independently_rederived=False,
                finite_continuation_terms='NOT_DETERMINED')
