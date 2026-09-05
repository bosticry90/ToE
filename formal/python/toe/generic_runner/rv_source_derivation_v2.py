"""Versioned RV phase-consistency repair; v1 and its failed probe are retained.

The direct Gamma-UV spinor kernel already carries its fermion-momentum and
transpose orientation. This module supplies the remaining Feynman/master
phases without counting that orientation a second time. Only the frozen
exp(+iS), D=partial-i*g*A, +i0 source profile is admitted.
"""
from __future__ import annotations

import re
import sympy as sp

from formal.python.toe.generic_runner import rv_source_derivation_v1 as v1

p,exact,require,E=v1.p,v1.exact,v1.require,v1.E
RECORDS=v1.RECORDS


def load_inputs(root=p.norm.ROOT):
    result=v1.load_inputs(root)
    sources=p.Sources(root)
    result['fourier']=sources.get('action','/space_time_and_fourier_contract')
    result['propagators']=[sources.get('action','/propagator_registry[id='+key+']')
                           for key in ('PROP-FERMION','PROP-QUANTUM-GAUGE')]
    result['source_reads']+=sources.bound.read_receipts
    return result


def phase_ledger(record, inputs):
    convention=inputs['fourier']
    require(convention['path_integral_phase']=='exp(+i*S)' and convention['all_vertex_momenta']=='INCOMING_AND_SUM_TO_ZERO', 'RV_FOURIER_PHASE_DOMAIN')
    require(convention['covariant_derivative']=='D_mu=partial_mu-i*g3*G_mu^a*T3_R^a-i*g2*W_mu^I*T2_R^I-i*g1*Y_R*B_mu','RV_COVARIANT_DERIVATIVE_DOMAIN')
    require(inputs['regularization']['metric_signature']=='+---' and inputs['regularization']['dimension']=='d=4-2*epsilon','RV_REGULATOR_PHASE_DOMAIN')
    gauge=record['topology']['coupling_monomial'][0]
    require(gauge in ('g1','g2','g3'),'RV_GAUGE_PHASE_DOMAIN')
    phases=[]
    rules=[]
    require(len(record['fields'])==len(record['vertices'])==2,'RV_PHASE_VERTEX_COUNT')
    for field,rule in zip(record['fields'],record['vertices']):
        # For the frozen kinetic/covariant-derivative and exp(+iS) convention,
        # the gauge vertex has +i. A contradictory local rule is rejected;
        # no new physical convention is silently inferred from a mutation.
        representation=field['hypercharge'] if gauge=='g1' else field['su'+gauge[1:]]
        require(rule['generator_representation']==representation,'RV_PHASE_REPRESENTATION_BINDING')
        expected='+i*'+gauge+'*gamma^mu*T_'+representation
        require(rule['exact_rule']==expected,'RV_VERTEX_PHASE_OR_RULE_INCONSISTENT')
        order=rule['functional_derivative_order']
        require(order==['bar'+field['field'],field['field'],'G'+gauge[1:]],'RV_VERTEX_PHASE_FIELD_BINDING')
        phases.append(p.leading_phase(rule['exact_rule']))
        rules.append(rule['rule_id'])
    registry={row['id']:row for row in inputs['propagators']}
    fermion=registry['PROP-FERMION']['rule']
    gauge_rule=registry['PROP-QUANTUM-GAUGE']['rule']
    require(fermion=='+i*slash(k)/(k^2-m_f^2+i*0)' and registry['PROP-FERMION']['orientation']=='FROM_fermion_TO_barfermion','RV_FERMION_PHASE_DOMAIN')
    require(gauge_rule=='-i*delta_ab*(g_munu-(1-xi)*k_mu*k_nu/(k^2+i*0))/(k^2+i*0)','RV_GAUGE_PROPAGATOR_PHASE_DOMAIN')
    topology=record['topology']
    edge_count=len(topology['internal_edges'])
    fermion_count=sum(not row[1].startswith('G') for row in topology['internal_edges'])
    require(edge_count==3 and fermion_count==2 and topology['loop_count']==1,'RV_MASTER_TOPOLOGY_DOMAIN')
    power=edge_count-fermion_count//2
    epsilon=sp.Symbol('epsilon',positive=True)
    master_residue=sp.limit(epsilon*sp.gamma(power-2+epsilon)/sp.gamma(power),epsilon,0)
    master_phase=sp.I*(-1)**power*master_residue
    phases.extend([p.leading_phase(fermion)]*fermion_count+[p.leading_phase(gauge_rule),master_phase])
    return dict(phase=sp.simplify(sp.prod(phases)),factors=phases,gauge_rules=rules,
        uv_master_residue=master_residue,uv_master_phase=master_phase,
        momentum_orientation='ALREADY_INCLUDED_IN_DIRECT_GAMMA_UV_SPINOR_KERNEL__NOT_MULTIPLIED_AGAIN',
        action_consistency='EXACT_FROZEN_SOURCE_PROFILE_CHECKED')


def calculate(inputs):
    # Validate every phase ledger before invoking any value-emitting kernel.
    ledgers={row['record_id']:phase_ledger(row,inputs) for row in inputs['records']}
    results=v1.calculate(inputs)
    for row in results:
        phase=ledgers[row['record_id']]
        raw=sp.cancel(row['normalization']['input']*phase['phase'])
        row['normalization']['input']=raw
        row['normalization']['output']=exact.arithmetic('INVERTIBLE_NORMALIZATION',
            [raw,row['normalization']['scale'],row['normalization']['inverse']])
        row['physical_coefficient']=row['normalization']['output']
        row['phase']=phase
    return results
