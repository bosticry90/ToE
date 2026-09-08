"""Inactive seven-record source-execution candidate with a stage transcript.

The transcript is recomputable but is NOT the complete fine-grained Pass0280
DAG. Its missing node-level coverage is an explicit qualification blocker.
"""
from __future__ import annotations

import argparse

from formal.python.toe.generic_runner import c03_source_derivation_v1 as c
from formal.python.toe.generic_runner import c03_native_projection_v1 as n
from formal.python.toe.generic_runner import rv_source_derivation_v1 as r


def compute(root=c.norm.ROOT):
    source, native, rv_source = c.load_inputs(root), n.load_inputs(root), r.load_inputs(root)
    physical = c.calculate(source)
    evanescent = n.calculate(source, native, physical)
    rv = r.calculate(rv_source)
    stages=[]
    def stage(key, operation, parents, value):
        encoded=c.serial(value)
        stages.append(dict(node_id=key, operation=operation, parents=parents,
                           value=encoded, value_digest=c.exact.digest(encoded,'SOURCE_STAGE_VALUE_v1')))
    stage('C03.BOUND_SOURCE', 'BOUND_INPUT_DECODING', [], c.exact.digest(source,'DECODED_SOURCE_v1'))
    stage('C03.BOUND_NATIVE_SOURCE', 'BOUND_INPUT_DECODING', [], c.exact.digest(native,'DECODED_SOURCE_v1'))
    stage('RV.BOUND_SOURCE', 'BOUND_INPUT_DECODING', [], c.exact.digest(rv_source,'DECODED_SOURCE_v1'))
    stage('C03.SIGN_DERIVATION', 'PERMUTATION_AND_COLOR_ACTION', ['C03.BOUND_SOURCE'], physical['weights'])
    stage('C03.PHASE_CHARGE_DERIVATION', 'INCIDENCE_AND_FEYNMAN_PHASES', ['C03.BOUND_SOURCE'], physical['phase'])
    stage('C03.SPINOR_DERIVATION', 'CLIFFORD_WARD_SOURCE_PROJECTION', ['C03.BOUND_SOURCE','C03.SIGN_DERIVATION'], physical['numerator'])
    stage('C03.NORMALIZATION_REFERENCE', 'DECODE_RECORDED_REFERENCE', ['C03.BOUND_SOURCE'], physical['reference'])
    stage('C03.RAW_COEFFICIENT', 'PRODUCT', ['C03.SPINOR_DERIVATION','C03.PHASE_CHARGE_DERIVATION'], physical['raw_full_graph_coefficient'])
    stage('C03.NORMALIZED_COEFFICIENT', 'INVERTIBLE_NORMALIZATION', ['C03.RAW_COEFFICIENT','C03.NORMALIZATION_REFERENCE'], physical['common_kernel_coefficient'])
    stage('C03.NATIVE_PROJECTION', 'N7_N8_SOURCE_OCCURRENCE_PROJECTION',
          ['C03.BOUND_SOURCE','C03.BOUND_NATIVE_SOURCE','C03.SIGN_DERIVATION','C03.PHASE_CHARGE_DERIVATION','C03.SPINOR_DERIVATION'], evanescent)
    roots={
        'C03.OUTPUT.PHYSICAL_COEFFICIENT': c.serial(physical['common_kernel_coefficient']),
        'C03.OUTPUT.EVANESCENT_COORDINATES': [c.serial(v) for v in evanescent['coordinates']],
        'C03.OUTPUT.EVANESCENT_STATE': evanescent['state'],
    }
    root_parents={key:'C03.NORMALIZED_COEFFICIENT' if 'PHYSICAL_COEFFICIENT' in key else 'C03.NATIVE_PROJECTION' for key in roots}
    records=[dict(record_id='C03', physical=dict(coefficient=c.serial(physical['common_kernel_coefficient']),
                    raw_full_graph_coefficient=c.serial(physical['raw_full_graph_coefficient']),
                    operator='Q_DUUE',normalization='COMMON_ROUTE_C03_KERNEL_COEFFICIENT',
                    normalization_map=physical['reference']),
                  evanescent=dict(state=evanescent['state'],method=evanescent['method'],
                    normalization=evanescent['normalization'],
                    coordinates=[c.serial(v) for v in evanescent['coordinates']],
                    physical_projection=c.serial(evanescent['physical_leakage']),
                    unexplained_residual='0' if not any(evanescent['unexplained_residual']) else 'NONZERO',
                    xi1_equals_1_nonzero_count=evanescent['xi1_equals_1_nonzero_count']))]
    for row in rv:
        key=row['record_id']
        stage(key+'.GROUP_DERIVATION','SOURCE_GENERATOR_ACTION',['RV.BOUND_SOURCE'],dict(value=row['group'],receipt=row['group_receipt']))
        stage(key+'.SPINOR_DERIVATION','CLIFFORD_WARD_SINGLE_CHAIN',['RV.BOUND_SOURCE'],row['spinor'])
        stage(key+'.COEFFICIENT_DERIVATION','COVARIANT_CONTRACTION_AND_IDENTITY_NORMALIZATION',
              ['RV.BOUND_SOURCE',key+'.GROUP_DERIVATION',key+'.SPINOR_DERIVATION'],row['normalization'])
        stage(key+'.ABSENCE_DERIVATION','BOUNDED_SINGLE_CHAIN_ABSENCE', ['RV.BOUND_SOURCE',key+'.SPINOR_DERIVATION'],row['evanescent'])
        roots[key+'.OUTPUT.PHYSICAL_COEFFICIENT']=c.serial(row['physical_coefficient'])
        root_parents[key+'.OUTPUT.PHYSICAL_COEFFICIENT']=key+'.COEFFICIENT_DERIVATION'
        roots[key+'.OUTPUT.EVANESCENT_STATE']=row['evanescent']['state']
        root_parents[key+'.OUTPUT.EVANESCENT_STATE']=key+'.ABSENCE_DERIVATION'
        if key=='RV03':
            roots[key+'.OUTPUT.SOURCE_CHANNEL']=row['group_receipt']['channel']
            root_parents[key+'.OUTPUT.SOURCE_CHANNEL']=key+'.GROUP_DERIVATION'
        records.append(dict(record_id=key,physical=dict(coefficient=c.serial(row['physical_coefficient']),
            source_channel=row['group_receipt']['channel'],
            normalization='DIRECT_GAMMA_UV_SOURCE_C_O__1_OVER_16PI2EPS_FACTORED',
            normalization_map=c.serial(row['normalization'])),evanescent=dict(state=row['evanescent']['state'],
            value=row['evanescent']['value'],method=row['evanescent']['method'],finite_continuation_terms='NOT_DETERMINED')))
    for key in sorted(roots):
        stage(key,'OUTPUT_BIND',[root_parents[key]],roots[key])
    c.require(len(roots)==16,'AUTHORITATIVE_ROOT_SET')
    return dict(schema_id='SEVEN_RECORD_SOURCE_EXECUTION_COMPONENT_PACKET_v4',
        candidate_status='EXECUTED_COMPONENTS__FULL_QUALIFICATION_INCOMPLETE',records=records,
        authoritative_outputs=roots,stage_dag=dict(nodes=stages,edges=[[p,s['node_id']] for s in stages for p in s['parents']],
            complete_fine_grained_pass0280_dag=False),
        source_reads=source['source_reads']+native['source_reads']+rv_source['source_reads'],
        implementation_answer_awareness='ANSWER_AWARE_IMPLEMENTATION__COMPARISON_BLIND_SOURCE_EXECUTION',
        limitations=['Stage-level recomputation is not full mandatory fine-grained DAG verification.',
                     'Admitted N7/N8/F4 source definitions are not independently rederived here.',
                     'No independent scientific review or complete structural anti-oracle proof.',
                     'Analytic phase primitive and absence-domain implementation remain subject to review.'],
        authority=dict(route_c='2/4',strict_exact_equivalence='1/4',production='76/1188',rows77_to96='CLOSED',
                       scientific_requalification='NOT_EARNED',activation=False))


def verify(packet, root=c.norm.ROOT):
    """Fresh source recomputation. Never use a claimed stage value as input."""
    expected=compute(root)
    c.require(c.exact.canonical(packet)==c.exact.canonical(expected),'SOURCE_RECOMPUTATION_MISMATCH')
    return dict(status='STAGE_TRANSCRIPT_AND_16_OUTPUTS_RECOMPUTED',
                independent_physics_implementation=False,full_pass0280_contract=False)


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(c.exact.canonical(compute()))


if __name__=='__main__': main()
