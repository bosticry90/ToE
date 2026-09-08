"""Trusted native-E operations relative to the admitted N8/F4 premises.

No native producer, source calculator, oracle or expected coordinate table is
imported. N7 relation provenance and F4 projection facts remain inherited.
"""
import re
import sympy as sp
from . import c03_rv_operation_support as x
from . import c03_rv_c03_operations as pv

E,require=x.exact_expr,x.require


def sparse(spec,rk,ck):
    shape=spec['shape']
    require(type(shape) is list and len(shape)==2 and all(type(v) is int and 0<v<=128 for v in shape),'NATIVE_MATRIX_SHAPE')
    m=sp.zeros(*shape); seen=set()
    for row in spec['entries']:
        i,j=row[rk],row[ck]
        require(type(i) is int and type(j) is int and 0<=i<m.rows and 0<=j<m.cols and (i,j) not in seen,'NATIVE_MATRIX_INDEX_OR_DUPLICATE')
        seen.add((i,j)); m[i,j]=E(row['coefficient'])
    require(len(seen)==spec['nonzero_count'],'NATIVE_MATRIX_ENTRY_COUNT')
    return m


def join(occ,requests,defects,columns,order,ledger):
    orig={o['occurrence_id']:o for o in occ}; req={r['input_tensor_id']:r for r in requests}
    defect={d['identity_key']['input_tensor_id']:d for d in defects}
    require(len(occ)==len(orig)==32 and len(requests)==len(req)==len(defects)==len(defect)==len(columns)==38,'NATIVE_JOIN_COUNTS')
    cols=sorted(columns,key=lambda c:c['column'])
    require([c['column'] for c in cols]==list(range(38)) and order==cols,'NATIVE_COLUMN_ORDER')
    require(set(orig)<=set(req)==set(defect)=={c['input_tensor_id'] for c in cols},'NATIVE_IDENTITY_JOIN')
    require(len(ledger)==30 and sum(r['relation_family']=='IDENTICAL_FIELD_EXCHANGE' for r in ledger)==19,'N7_LEDGER_DOMAIN')
    extensions=[]
    for c in cols:
        oid=c['input_tensor_id']; r=req[oid]; d=defect[oid]
        require(c['defect_id']==d['defect_id'] and r['request_id']==d['request_id'],'NATIVE_DEFECT_REQUEST_JOIN')
        require(r['source_orbit']==d['identity_key']['source_orbit'],'NATIVE_DEFECT_ORBIT')
        if oid in orig:
            o=orig[oid]
            require(r['provenance_class']=='SOURCE_GENERATED' and r['source_orbit']==o['source_orbit']['orbit_id'] and
                    r['angular_pairing_id']==o['angular_average']['pairing_terms'][0]['pairing_id'],'NATIVE_SOURCE_JOIN')
        else:
            require(r['provenance_class'] in ('RELATION_REQUIRED__BMHV_LOWER_RANK','RELATION_REQUIRED__BMHV_ZERO_GAMMA_TREE'),'UNJUSTIFIED_EXTENSION_ZERO')
            extensions.append(c['column'])
    require(len(extensions)==6,'NATIVE_EXTENSION_COUNT')
    return dict(columns=cols,original_ids=[o['occurrence_id'] for o in occ],extension_columns=extensions)


def clifford(occ,domain):
    require(domain['regularization']['dimension']=='d=4-2*epsilon','NATIVE_DIMENSION')
    result=[]
    for o in occ:
        signs=[]
        for c in o['gamma_chains']:
            source=c['source_factors']; normal=c['normal_form_factors']
            require(c['chirality_projector']=='RIGHT' and len(source)==2,'NATIVE_WORD_DOMAIN')
            require(all(f['kind']=='GAMMA' and f['sector'] in ('BAR','HAT') for f in source),'NATIVE_GAMMA_DOMAIN')
            key=lambda f:(f['kind'],f['lorentz_slot'],f['sector'],f['source_position'])
            a=list(map(key,source)); b=list(map(key,normal))
            require(len(set(a))==len(a) and sorted(a)==sorted(b),'NATIVE_WORD_MULTISET')
            # Stable ordering preserves same-sector relative order. Only
            # anticommuting bar/hat crossings contribute a permutation sign.
            expected=sorted(source,key=lambda f:f['sector']!='HAT')
            require(normal==expected,'NATIVE_UNSUPPORTED_CLIFFORD_INTERCHANGE')
            permutation=sp.zeros(len(a))
            for i,f in enumerate(b): permutation[i,a.index(f)]=1
            sign=permutation.det()
            require(sign==c['clifford_reordering_sign'],'NATIVE_STORED_CLIFFORD_SIGN')
            signs.append(sign)
        require(len(signs)==2,'NATIVE_CHAIN_COUNT')
        result.append(dict(occurrence_id=o['occurrence_id'],chain_signs=signs,product=sp.prod(signs)))
    return result


def angular(occ,domain):
    require(domain['dirac']['projector_traces']['bar_g_mu_nu_bar_g^nu_mu']=='4','NATIVE_BAR_DIMENSION')
    d=sp.Symbol('d'); rows=[]
    for o in occ:
        a=o['angular_average']; rank=a['master_rank']; terms=a['pairing_terms']
        require(rank in (2,4) and len(terms)==1 and len(a['momentum_slots'])==rank,'NATIVE_ANGULAR_DOMAIN')
        weight=1/sp.prod(d+2*i for i in range(rank//2))
        pairs=terms[0]['metric_pairs']
        factors={f['lorentz_slot']:f for c in o['gamma_chains'] for f in c['source_factors']}
        require(len(factors)==4 and sorted(s for pair in pairs for s in (pair['left_slot'],pair['right_slot']))==sorted(factors),'NATIVE_ANGULAR_SLOT_COVERAGE')
        for pair in pairs:
            require(pair['metric_sector']==factors[pair['left_slot']]['sector']==factors[pair['right_slot']]['sector'],'NATIVE_METRIC_SECTOR')
        require(sum(pair['metric_origin']=='ANGULAR_AVERAGE' for pair in pairs)==rank//2,'NATIVE_ANGULAR_PAIR_COUNT')
        require(sp.cancel(weight-E(terms[0]['exact_weight']))==0,'NATIVE_ANGULAR_WEIGHT')
        rows.append(dict(occurrence_id=o['occurrence_id'],weight=weight,rank=rank))
    return rows


def witness(r,target):
    solution,params=r.T.gauss_jordan_solve(target)
    solution=solution.subs({s:0 for s in params}).applyfunc(sp.cancel)
    require(x.exact_equal(r.T*solution,target),'NATIVE_RELATION_WITNESS')
    return list(solution)


def operation(key,parents):
    suffix=key.removeprefix('C03.NATIVE.')
    if suffix=='JOIN': return join(*parents)
    if suffix=='CLIFFORD': return clifford(parents[0],parents[2])
    if suffix=='ANGULAR': return angular(parents[0],parents[2])
    if suffix=='CHANNEL':
        occ,gauge,ledger=parents
        require(gauge['monomial']==['g1','g1'] and 'xi_1_FOR_U1Y' in gauge['parameters'],'NATIVE_GAUGE')
        rule=next(r['rule'] for r in ledger['propagators'] if r['id']=='PROP-QUANTUM-GAUGE')
        require('g_munu-(1-xi)*k_mu*k_nu' in rule,'NATIVE_PROPAGATOR_CHANNELS')
        xi=sp.Symbol('xi'+gauge['monomial'][0][1:]); rows=[]
        for o in occ:
            rank=o['angular_average']['master_rank']; name=o['source_term_id']
            require((rank==2 and name=='ROUTE_C03_AT_GAUGE_AND_PROPAGATOR') or
                    (rank==4 and name in ('ROUTE_C03_AL_WITHIN_CHAINS','ROUTE_C03_AL_PARALLEL_ACROSS_CHAINS','ROUTE_C03_AL_CROSSED_ACROSS_CHAINS')),'NATIVE_SOURCE_CHANNEL_DOMAIN')
            value=sp.Integer(1) if rank==2 else -(1-xi)
            require(all(sp.cancel(E(v)-value)==0 for v in (o['factored_scientific_prefactors']['channel'],o['angular_average']['channel_prefactor_factored_from_Qd_coefficient'])),'NATIVE_SOURCE_CHANNEL_MISMATCH')
            rows.append(dict(occurrence_id=o['occurrence_id'],factor=value))
        return rows
    if suffix=='LEGACY':
        occ,signs,angles=parents; result=[]
        for o,s,a in zip(occ,signs,angles):
            old=E(o['source_orbit']['grassmann_and_color_parity'])
            require(old in (-1,1),'NATIVE_LEGACY_SIGN')
            value=old*s['product']*a['weight']
            require(sp.cancel(value-E(o['exact_coefficient']))==0,'NATIVE_LEGACY_AGGREGATE')
            result.append(dict(occurrence_id=o['occurrence_id'],old_sign=old,aggregate=sp.cancel(value)))
        return result
    if suffix=='WEIGHTS':
        occ,identity,exchange=parents
        return [dict(occurrence_id=o['occurrence_id'],weight={'IDENTITY':identity,'IDENTICAL_UR_EXCHANGE':exchange}[o['source_orbit']['orbit_id']]) for o in occ]
    if suffix=='PHASE': return pv.phase_product(parents[0])[0]
    if suffix=='AMBIENT':
        j,signs,angles,channels,legacy,weights,phase,charge=parents
        arrays=[{r['occurrence_id']:r for r in rs} for rs in (signs,angles,channels,legacy,weights)]
        require(all(set(a)==set(j['original_ids']) for a in arrays),'NATIVE_INTERMEDIATE_JOIN')
        out=[]
        for c in j['columns']:
            oid=c['input_tensor_id']
            out.append(sp.cancel(phase*charge*arrays[0][oid]['product']*arrays[1][oid]['weight']*arrays[2][oid]['factor']*arrays[4][oid]['weight']) if oid in arrays[0] else sp.Integer(0))
        return tuple(out)
    if suffix=='RELATIONS':
        r=sparse(parents[0],'relation_row','ambient_column')
        require(r.shape==(30,len(parents[1]['columns'])) and r.rank()==24,'NATIVE_RELATION_DIMENSION')
        return r
    if suffix=='REPRESENTATIVE':
        rows,cache,j=parents; u=sp.zeros(len(j['columns']),len(rows)); indices=set()
        for row in rows:
            q,a=row['quotient_index'],row['ambient_generator_column']
            require(type(q) is int and 0<=q<len(rows) and q not in indices and type(a) is int and 0<=a<u.rows,'NATIVE_REPRESENTATIVE_INDEX')
            indices.add(q); col=j['columns'][a]
            require(row['defect_id']==col['defect_id'] and row['input_tensor_id']==col['input_tensor_id'] and row['representative_vector']['ambient_column']==a,'NATIVE_REPRESENTATIVE_LABEL')
            u[a,q]=E(row['representative_vector']['coefficient'])
        require(u.shape==(38,14) and u==sparse(cache,'ambient_generator_column','quotient_column'),'NATIVE_REPRESENTATIVE_CACHE')
        return u
    if suffix=='DUAL':
        r,u,cache=parents; basis=sp.Matrix.hstack(*r.nullspace())
        require(basis.shape==(38,14),'NATIVE_NULLSPACE_DOMAIN')
        d=((basis.T*u).inv()*basis.T).applyfunc(sp.cancel)
        require(d==sparse(cache,'dual_index','ambient_generator_column'),'NATIVE_DUAL_CACHE')
        return d
    if suffix=='QUOTIENT':
        u,d,cache=parents; result=u*d
        require(result==sparse(cache,'output_ambient_column','input_ambient_column'),'NATIVE_QUOTIENT_CACHE')
        return result
    if suffix=='REMAINDER':
        q,cache=parents; result=sp.eye(q.rows)-q
        require(result==sparse(cache,'output_ambient_column','input_ambient_column'),'NATIVE_REMAINDER_CACHE')
        return result
    if suffix=='RELATION_CERTIFICATE':
        r,d,u,q,k=parents
        require(d*r.T==sp.zeros(d.rows,r.rows) and d*u==sp.eye(u.cols) and d*k==sp.zeros(d.rows,k.cols),'NATIVE_DUAL_IDENTITIES')
        require(q*q==q and k*k==k and r.col_join(k.T).rank()==r.rank(),'NATIVE_RELATION_SPACE')
        return dict(relation_rank=r.rank(),quotient_rank=q.rank(),remainder_rank=k.rank(),
                    dual_annihilation=True,representative_identity=True,remainder_in_relation_space=True)
    if suffix in ('COORDINATES','PROJECTED','RELATION_PART'):
        return tuple(sp.cancel(v) for v in parents[0]*sp.Matrix(parents[1]))
    if suffix=='WITNESS':
        r,a,projected=parents; return dict(coefficients=witness(r,sp.Matrix(a)-sp.Matrix(projected)))
    if suffix=='RESIDUAL':
        a,proj,part,w,r=parents
        remainder=sp.Matrix(a)-sp.Matrix(proj)
        require(x.exact_equal(remainder,r.T*sp.Matrix(w['coefficients'])) and x.exact_equal(remainder,sp.Matrix(part)),'NATIVE_REMAINDER_WITNESS_MISMATCH')
        return tuple(sp.cancel(v) for v in remainder-sp.Matrix(part))
    if suffix=='LEAKAGE_ROW':
        defects,j,domain=parents
        require(domain['lift']['projection_coefficients']=='EVALUATED_EXACTLY_AT_d=4_AND_INDEPENDENT_OF_EPSILON','NATIVE_LIFT_DOMAIN')
        by_id={d['identity_key']['input_tensor_id']:d for d in defects}; out=[]
        for col in j['columns']:
            d=by_id[col['input_tensor_id']]
            match=re.fullmatch(r'T_open\(d\)-\((.+)\)\*Lift\(Q_duue\)',d['definition'])
            require(match is not None and d['p4_zero_proved_by']=='P4_T_MINUS_LIFT_OF_EXACT_F4_P4_T__WITH_P4_COMPOSE_LIFT_EQUALS_ID','NATIVE_ADMITTED_P4_DEFINITION')
            value=sp.cancel(E(d['physical_q_duue_coefficient'])-E(match[1]))
            require(value==0 and value==E(d['p4_of_defect']),'NATIVE_ADMITTED_P4_CONSISTENCY')
            out.append(value)
        return tuple(out)
    if suffix=='LEAKAGE': return sp.cancel(sum(a*b for a,b in zip(*parents)))
    if suffix=='STATE':
        coords,residual,leakage,cert=parents
        require(all(v==0 for v in residual) and leakage==0 and cert['remainder_in_relation_space'],'NATIVE_STATE_EVIDENCE')
        return 'EVALUATED_NONZERO' if any(sp.cancel(v)!=0 for v in coords) else 'EVALUATED_ZERO'
    raise x.VerificationError('NATIVE_OPERATION_NOT_IMPLEMENTED',key)
