"""Trusted operations for the six frozen RV source profiles.

The checker uses tensor-product blocks, exact residuals, incidence routing,
Clifford word contractions and Laurent residues. It imports no RV producer.
"""
import ast
import itertools as it
import math
import sympy as sp
from . import c03_rv_operation_support as x

E,require=x.exact_expr,x.require


def radical(value):
    require(type(value) in (int,str) and len(str(value))<512,'RV_RADICAL_DOMAIN')
    tree=ast.parse(str(value),mode='eval')
    require(sum(1 for _ in ast.walk(tree))<64,'RV_RADICAL_SIZE')
    def parse(n):
        if isinstance(n,ast.Constant) and type(n.value) is int and abs(n.value)<100000: return sp.Integer(n.value)
        if isinstance(n,ast.Name) and n.id=='I': return sp.I
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,(ast.UAdd,ast.USub)):
            v=parse(n.operand); return -v if isinstance(n.op,ast.USub) else v
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='sqrt' and len(n.args)==1 and not n.keywords:
            v=parse(n.args[0]); require(v.is_Integer is True and 0<v<=100,'RV_RADICAL_ARGUMENT'); return sp.sqrt(v)
        if isinstance(n,ast.BinOp):
            a,b=parse(n.left),parse(n.right)
            if isinstance(n.op,ast.Add): return a+b
            if isinstance(n.op,ast.Sub): return a-b
            if isinstance(n.op,ast.Mult): return a*b
            if isinstance(n.op,ast.Div):
                require(b!=0,'RV_RADICAL_ZERO_DENOMINATOR'); return a/b
        raise x.VerificationError('RV_RADICAL_CAPABILITY')
    return sp.simplify(parse(tree.body))


def domain(ctx):
    r=ctx['record']; t=r['topology']; target=r['target']; source=r['source']
    require(t['source_insertion_id']==r['operator']==target['target_operator_id'],'RV_SOURCE_TARGET_IDENTITY')
    require(type(t['source_derivative_count']) is int and type(target['derivative_count']) is int and
            t['source_derivative_count']==target['derivative_count']==t['target_derivative_count']==0,'RV_DERIVATIVE_DOMAIN')
    require(t['one_particle_irreducible'] is True and t['loop_count']==1 and len(t['internal_edges'])==3 and
            len(r['vertices'])==len(t['renormalizable_vertex_ids'])==2,'RV_GRAPH_DOMAIN')
    require(sorted(t['target_external_fields'])==sorted(target['ordered_fields']),'RV_TARGET_FIELDS')
    require(len(t['coupling_monomial'])==2 and len(set(t['coupling_monomial']))==1,'RV_GAUGE_DOMAIN')
    require(ctx['regularization']['dimension']=='d=4-2*epsilon' and ctx['regularization']['metric_signature']=='+---','RV_REGULATOR_DOMAIN')
    fermions=[e for e in t['internal_edges'] if not e[1].startswith('G')]
    require(len(fermions)==2 and all(e[0]==0 for e in fermions),'RV_SOURCE_INCIDENCE')
    kinds=[f['kind'] for f in r['fields']]
    require(all(k in ('LEFT_WEYL','RIGHT_WEYL') for k in kinds),'RV_FERMION_KINDS')
    directed=any(e[1].startswith('bar') for e in fermions)
    if directed:
        require(sorted(kinds)==['LEFT_WEYL','RIGHT_WEYL'] and source['fields']==target['ordered_fields'] and
                source['multiplicity']['total']==1 and 'baruR' in source['fields'],'RV_DIRECTED_SOURCE')
        require(any(radical(e['coefficient'])!=0 for e in source['witness']['sparse_entries']),'RV_DIRECTED_WITNESS_ZERO')
    else: require(len(set(kinds))==1,'RV_SAME_CHIRALITY')
    field_names={'qL','lL','dR','uR','eR','baruR'}
    ordered=[f for f in target['ordered_fields'] if f in field_names]
    endpoints=[f['field'] for f in r['fields']]
    if len(ordered)==4:
        require(source.get('operator')=='Q_duql[p,r,s,t]=epsilon_ABC epsilon_ij (d_p^{AT} C u_r^B)(q_s^{CiT} C l_t^j)' and
                sorted(endpoints)==['lL','qL'],'RV_CROSS_BILINEAR_NOT_ADMITTED')
        touched=['qL','lL']
    else:
        require(len(ordered)==2,'RV_CHAIN_COUNT'); touched=ordered
    for vi,v,f in zip(t['renormalizable_vertex_ids'],r['vertices'],r['fields']):
        require(v['rule_id']==vi.replace('VTX-GAUGE-','FR-') and v['rule_kind']=='FERMION_FERMION_QUANTUM_GAUGE' and
                v['functional_derivative_order'][1]==f['field'],'RV_CURRENT_SOURCE_BINDING')
    return dict(directed=directed,right=all(k=='RIGHT_WEYL' for k in kinds),
        source_spinor_chain_count=len(ordered)//2,touched_spinor_chains=1,touched_fields=touched,
        current_count=len(r['vertices']),fermion_propagators=len(fermions),source_derivatives=0,target_derivatives=0)


def tensor(ctx,admission):
    r=ctx['record']; src=r['source']; blob=r['tensor']; pair=[]
    if blob is not None:
        dims=blob['dims']; entries=blob['sparse_entries']; axes=r['registered']['component_axis_order']
        pair=[axes.index('qL[1].color3'),axes.index('qL[2].color3')]
    elif admission['directed']:
        blob=src['witness']; dims=blob['dims']; entries=blob['sparse_entries']
    elif 'H_dagger_i epsilon_jk X^{C k}+H_dagger_j epsilon_ik X^{C k}' in src.get('operator',''):
        require(src['flavor_exchange']=='O_pr=-O_rp' and src['same_flavor_survives'] is False,'RV_WEAK_FLAVOR')
        dims=[2]*4; pair=[0,1]
        entries=[dict(index=[i,j,h,z],coefficient=(h==i)*(z-j)+(h==j)*(z-i)) for i,j,h,z in it.product(range(2),repeat=4)]
    elif src.get('operator')=='epsilon_ABC (d_R,p^{A T} C d_R,r^B)(H^i epsilon_ij X^{C j})':
        require(src['flavor_exchange']=='O_pr=-O_rp','RV_COLOR_FLAVOR')
        dims=[3]*3; pair=[0,1]
        entries=[dict(index=list(idx),coefficient=str(sp.LeviCivita(*idx))) for idx in it.product(range(3),repeat=3)]
    elif admission['source_spinor_chain_count']==2:
        require(src['normalization']=='DISPLAYED_WARSAW_TENSOR_WITH_NO_EXTRA_SYMMETRY_FACTOR','RV_WARSAW_SOURCE_NORMALIZATION')
        dims=[3,3,3,2,2]
        entries=[dict(index=[a,b,c,i,j],coefficient=str(sp.LeviCivita(a,b,c)*(j-i))) for a,b,c,i,j in it.product(range(3),range(3),range(3),range(2),range(2))]
    else: raise x.VerificationError('RV_TENSOR_PROFILE_UNSUPPORTED')
    require(type(dims) is list and all(type(d) is int and 0<d<=8 for d in dims) and math.prod(dims)<=10000,'RV_TENSOR_DIMENSIONS')
    data={}; seen=set()
    for e in entries:
        idx=tuple(e['index']); require(len(idx)==len(dims) and idx not in seen and all(type(v) is int and 0<=v<d for v,d in zip(idx,dims)),'RV_TENSOR_ENTRY')
        seen.add(idx); v=radical(e['coefficient'])
        if v!=0: data[idx]=v
    require(data,'RV_SOURCE_TENSOR_ZERO')
    return dict(dims=dims,pair=pair,entries=[dict(index=list(i),coefficient=data[i]) for i in sorted(data)])


def channel(ctx,admission,t):
    r=ctx['record']; gauge=r['topology']['coupling_monomial'][0]
    if gauge=='g1': return 'ABELIAN_ENDPOINT_CHARGE_PRODUCT'
    if r['registered'] is not None: return 'EXACT_REGISTERED_COMPONENT_TENSOR'
    # The frozen profile uses the canonical representation label rather than
    # the historical shorthand "2".  Match the source contract exactly so a
    # spelling alias cannot silently select this scientific channel.
    if r['fields'][0]['su2']=='FUNDAMENTAL_2' and t['dims']==[2]*4:
        data={tuple(e['index']):e['coefficient'] for e in t['entries']}
        require(all(v==data.get((idx[1],idx[0],idx[2],idx[3]),0) for idx,v in data.items()),'RV_SOURCE_NOT_WEAK_TRIPLET')
        return 'WEAK_TRIPLET_A_FLAVOR'
    if t['dims']==[3]*3: return 'SOURCE_EPSILON_COLOR_TENSOR'
    raise x.VerificationError('RV_CHANNEL_UNSUPPORTED')


def group_image(ctx,t,dispatch):
    r=ctx['record']; gauge=r['topology']['coupling_monomial'][0]
    data={tuple(e['index']):e['coefficient'] for e in t['entries']}
    if gauge=='g1':
        charges=[]
        for f,v in zip(r['fields'],r['vertices']):
            q=E(f['hypercharge']); require(q.is_Rational and q==E(v['generator_representation']) and v['exact_rule']=='+i*g1*gamma^mu*T_'+f['hypercharge'],'RV_CHARGE_RULE')
            charges.append(q)
        out={i:sp.simplify(v*sp.prod(charges)) for i,v in data.items()}
    else:
        gs=[sp.Matrix([[radical(v) for v in row] for row in g]) for g in r['generators']]
        size=gs[0].rows
        require(all(g.shape==(size,size) and g==g.conjugate().T and sp.trace(g)==0 for g in gs),'RV_GENERATOR_DOMAIN')
        require(all(sp.simplify(sp.trace(a*b)-sp.Rational(i==j,2))==0 for i,a in enumerate(gs) for j,b in enumerate(gs)),'RV_GENERATOR_NORMALIZATION')
        pair=t['pair']; require(len(pair)==2 and pair[0]!=pair[1] and all(t['dims'][a]==size for a in pair),'RV_GROUP_AXES')
        # The producer scatters each generator coefficient. This path builds
        # a two-index operator and acts on blocks at fixed spectator indices.
        action=sum((sp.kronecker_product(g,g) for g in gs),sp.zeros(size**2))
        others=[i for i in range(len(t['dims'])) if i not in pair]
        blocks={}
        for idx,value in data.items():
            spectator=tuple(idx[i] for i in others)
            blocks.setdefault(spectator,sp.zeros(size**2,1))[idx[pair[0]]*size+idx[pair[1]]]=value
        out={}
        for spectator,vector in blocks.items():
            image=(action*vector).applyfunc(sp.simplify)
            for k,v in enumerate(image):
                if v!=0:
                    idx=[0]*len(t['dims'])
                    for axis,val in zip(others,spectator): idx[axis]=val
                    idx[pair[0]],idx[pair[1]]=divmod(k,size)
                    out[tuple(idx)]=v
    return dict(dims=t['dims'],pair=t['pair'],entries=[dict(index=list(i),coefficient=out[i]) for i in sorted(out) if out[i]!=0])


def group_projection(t,image):
    before={tuple(e['index']):e['coefficient'] for e in t['entries']}; after={tuple(e['index']):e['coefficient'] for e in image['entries']}
    first=next(iter(before)); scalar=sp.simplify(after.get(first,0)/before[first])
    require(all(sp.simplify(after.get(i,0)-scalar*before.get(i,0))==0 for i in set(before)|set(after)),'RV_GROUP_FULL_RESIDUAL')
    return scalar


def gammas(ctx):
    require('C=i*gamma^2*gamma^0_IN_THE_FOUR_DIMENSIONAL_PHYSICAL_SUBSPACE' in ctx['dirac']['charge_conjugation'],'RV_CHARGE_CONJUGATION')
    sigma=[sp.Matrix([[0,1],[1,0]]),sp.Matrix([[0,-sp.I],[sp.I,0]]),sp.diag(1,-1)]
    gamma=[sp.kronecker_product(sigma[2],sp.eye(2))]+[sp.kronecker_product(sp.I*sigma[1],s) for s in sigma]
    eta=(1,-1,-1,-1)
    require(all(a*b+b*a==2*(eta[i] if i==j else 0)*sp.eye(4) for i,a in enumerate(gamma) for j,b in enumerate(gamma)),'RV_CLIFFORD_ALGEBRA')
    return gamma,eta


def tree(ctx,d):
    g,_=gammas(ctx); g5=sp.I*g[0]*g[1]*g[2]*g[3]
    projection=(sp.eye(4)+(1 if d['right'] else -1)*g5)/2
    return projection if d['directed'] else sp.I*g[2]*g[0]*projection


def words(ctx,d,t):
    top=ctx['record']['topology']; edges=top['internal_edges']; inc=sp.zeros(3)
    gauge=[]; ferm=[]
    for i,(a,f,b,fb) in enumerate(edges):
        require(type(a) is int and type(b) is int and 0<=a<3 and 0<=b<3 and a!=b,'RV_INCIDENCE_INDEX')
        inc[a,i]=-1; inc[b,i]=1
        (gauge if f.startswith('G') else ferm).append(i)
    require(len(gauge)==1 and len(ferm)==2 and inc.rank()==2,'RV_ROUTING_DOMAIN')
    unit=sp.zeros(1,3); unit[0,gauge[0]]=1
    routing,params=inc.col_join(unit).gauss_jordan_solve(sp.Matrix([0,0,0,1]))
    require(params.rows==0 and all(v in (-1,1) for v in routing),'RV_ROUTING_SOLUTION')
    barred=sum(edges[i][1].startswith('bar') for i in ferm)
    sign=sp.prod(routing[i] for i in ferm)*(-1)**barred
    return dict(directed=d['directed'],right=d['right'],routing=list(routing),orientation_sign=sign,
        gamma_count=d['current_count']+d['fermion_propagators'],
        current_fields=[v['functional_derivative_order'] for v in ctx['record']['vertices']],
        fermion_edges=[edges[i] for i in ferm],open_lorentz_indices=0)


def spinor_image(ctx,w,t,ward=False):
    g,eta=gammas(ctx); orientation=w['orientation_sign']
    require(w['gamma_count']==4 and w['open_lorentz_indices']==0,'RV_WORD_DOMAIN')
    if ward:
        k=sp.symbols('k0:4'); slash=sum((a*v for a,v in zip(k,g)),sp.zeros(4))
        square=(slash*slash).applyfunc(sp.expand); k2=sum(eta[i]*k[i]**2 for i in range(4))
        require(square==k2*sp.eye(4),'RV_WARD_IDENTITY')
        action=sp.kronecker_product(square if w['directed'] else square.T,square.T)
        result=(orientation*action*sp.Matrix(list(t))).reshape(4,4)/k2**2
    else:
        action=sp.zeros(16)
        for mu,rho in it.product(range(4),repeat=2):
            left=g[mu]*g[rho] if w['directed'] else (g[rho]*g[mu]).T
            right=g[rho]*g[mu]
            action+=sp.Rational(eta[mu]*eta[rho],4)*sp.kronecker_product(left,right.T)
        result=(orientation*action*sp.Matrix(list(t))).reshape(4,4)
    return result.applyfunc(sp.simplify)


def proportional(tree_value,image):
    i=next(i for i,v in enumerate(tree_value) if v!=0)
    scalar=sp.simplify(image[i]/tree_value[i])
    require(image==scalar*tree_value,'RV_SPINOR_FULL_RESIDUAL')
    return scalar


def phase(ctx,w):
    r=ctx['record']; f=ctx['fourier']; gauge=r['topology']['coupling_monomial'][0]
    require(f['path_integral_phase']=='exp(+i*S)' and f['all_vertex_momenta']=='INCOMING_AND_SUM_TO_ZERO' and
        f['covariant_derivative']=='D_mu=partial_mu-i*g3*G_mu^a*T3_R^a-i*g2*W_mu^I*T2_R^I-i*g1*Y_R*B_mu','RV_PHASE_CONVENTION')
    factors=[]
    for field,v in zip(r['fields'],r['vertices']):
        rep=field['hypercharge'] if gauge=='g1' else field['su'+gauge[1:]]
        require(v['generator_representation']==rep and v['exact_rule']=='+i*'+gauge+'*gamma^mu*T_'+rep and
                v['functional_derivative_order']==['bar'+field['field'],field['field'],'G'+gauge[1:]],'RV_PHASE_RULE_CONFLICT')
        factors.append(sp.I)
    props={v['id']:v for v in ctx['propagators']}
    require(props['PROP-FERMION']['rule']=='+i*slash(k)/(k^2-m_f^2+i*0)' and props['PROP-FERMION']['orientation']=='FROM_fermion_TO_barfermion','RV_PHASE_FERMION')
    require(props['PROP-QUANTUM-GAUGE']['rule']=='-i*delta_ab*(g_munu-(1-xi)*k_mu*k_nu/(k^2+i*0))/(k^2+i*0)','RV_PHASE_GAUGE')
    power=len(r['topology']['internal_edges'])-len(w['fermion_edges'])//2
    eps=sp.Symbol('epsilon'); master=sp.I*(-1)**power*sp.residue(sp.gamma(power-2+eps)/sp.gamma(power),eps,0)
    factors += [sp.I]*len(w['fermion_edges'])+[-sp.I,master]
    return dict(factors=factors,phase=sp.simplify(sp.prod(factors)),master_phase=master,
        orientation_already_in_spinor_words=True)


def normalization(ctx,t,spin):
    r=ctx['record']; target=r['target']; top=r['topology']
    require(top['source_insertion_id']==target['target_operator_id']==r['operator'],'RV_TREE_IDENTITY_DOMAIN')
    require(target['ordered_functional_derivative_semantics']=='LABEL_ALL_REPEATED_SLOTS_SUM_ALL_SAME_SPECIES_BIJECTIONS_CANONICALIZE_FERMIONS_WITH_EXACT_GRASSMANN_PARITY_AND_NEVER_ADD_A_MANUAL_FACTORIAL','RV_TREE_DERIVATIVE_SEMANTICS')
    require(target['target_component_basis_binding']=='PHASE1_PHYSICAL_NODE_PLUS_PASS0020_BMHV_LIFT_AND_WHERE_APPLICABLE_PASS0017_EXACT_COMPONENT_TENSOR','RV_TREE_BASIS_BINDING')
    source_fields=sorted(top['target_external_fields']); target_fields=sorted(target['ordered_fields'])
    require(source_fields==target_fields,'RV_TREE_FIELD_MAP')
    # Same named source/target tree under the admitted coefficient convention.
    # No independent new target normalization convention is introduced.
    source_norm=sp.simplify(sum(sp.conjugate(e['coefficient'])*e['coefficient'] for e in t['entries'])*sp.trace(spin.conjugate().T*spin))
    require(source_norm!=0,'RV_TREE_SINGULAR')
    target_norm=source_norm
    scale=sp.cancel(source_norm/target_norm)
    return dict(scale=scale,inverse=sp.cancel(target_norm/source_norm),source_tree_norm=source_norm,target_tree_norm=target_norm,
        scope='DECLARED_SAME_NAMED_SOURCE_TARGET_TREE_IDENTITY')


def coverage(ctx,d,w):
    require(d['touched_spinor_chains']==1 and d['current_count']==d['fermion_propagators']==2 and
            d['source_derivatives']==d['target_derivatives']==0 and w['gamma_count']==4 and w['open_lorentz_indices']==0,'RV_ABSENCE_PROFILE')
    # Enumerate perfect matchings of the four actual contracted word slots.
    result=[]
    for mate in range(1,w['gamma_count']):
        rest=[i for i in range(1,w['gamma_count']) if i!=mate]
        word=[None]*4; word[0]=word[mate]=0; word[rest[0]]=word[rest[1]]=1
        for sectors in it.product(('BAR','HAT'),repeat=2):
            result.append(dict(word=word,sectors=list(sectors)))
    return result


def word_reduce(items):
    h=sp.Symbol('h'); out=[]
    # Clifford contraction expansion: each pairing imposes index equalities;
    # connected index loops contribute their sector dimension. This does not
    # use the producer's crossing/non-crossing coefficient formula.
    pairings=[([(0,1),(2,3)],1), ([(0,2),(1,3)],-1), ([(0,3),(1,2)],1)]
    for row in items:
        word,sectors=row['word'],row['sectors']
        require(sorted(word)==[0,0,1,1] and set(sectors)<= {'BAR','HAT'},'RV_CONTRACTED_WORD_DOMAIN')
        total=0
        for pairs,sign in pairings:
            linked=any(word[i]!=word[j] for i,j in pairs)
            if linked:
                term=0 if sectors[0]!=sectors[1] else (4 if sectors[0]=='BAR' else h)
            else:
                term=sp.prod(4 if s=='BAR' else h for s in sectors)
            total+=sign*term
        out.append(dict(word=word,sectors=sectors,scalar=sp.expand(total)))
    return out


def pole(ctx,reductions,d):
    require(ctx['regularization']['uv_poles_retained_for_closure']==['1/epsilon'],'RV_ABSENCE_POLE_ORDER')
    h=sp.Symbol('h'); eps=sp.Symbol('epsilon'); dimension=4+h
    denominators=[dimension,dimension*(dimension+2)]
    require(all(den.subs(h,0)!=0 for den in denominators),'RV_ABSENCE_DENOMINATOR')
    residues=[]
    for row in reductions:
        if 'HAT' in row['sectors']:
            require(sp.rem(row['scalar'],h)==0,'RV_ABSENCE_HAT_FACTOR')
            for den in denominators:
                residues.append(sp.residue((row['scalar']/den).subs(h,-2*eps)/eps,eps,0))
    require(residues and all(r==0 for r in residues),'RV_EVANESCENT_POLE_RESIDUAL')
    return dict(hat_term_residues=residues,canonical_evanescent_simple_pole=sp.Add(*residues),
        finite_continuation_terms='NOT_DETERMINED',method='ANALYTIC_ABSENCE',scope='SINGLE_TOUCHED_SCALAR_CHAIN_SIMPLE_POLE')


def operation(key,p):
    suffix=key.split('.',1)[1]
    if suffix=='DOMAIN': return domain(p[0])
    if suffix=='TENSOR': return tensor(*p)
    if suffix=='CHANNEL': return channel(*p)
    if suffix=='GROUP_IMAGE': return group_image(*p)
    if suffix=='GROUP': return group_projection(*p)
    if suffix=='TREE': return tree(*p)
    if suffix=='WORDS': return words(*p)
    if suffix=='METRIC_IMAGE': return spinor_image(*p)
    if suffix=='WARD_IMAGE': return spinor_image(*p,ward=True)
    if suffix=='SPINOR_PROJECTION':
        t,m,l=p; return dict(metric=proportional(t,m),longitudinal=proportional(t,l),tree_norm=sp.trace(t.conjugate().T*t))
    if suffix=='PHASE': return phase(*p)
    if suffix=='COVARIANT':
        ctx,spin=p; gauge=ctx['record']['topology']['coupling_monomial'][0]
        require(any(v.startswith('xi_'+gauge[1:]+'_') for v in ctx['gauge_parameters']),'RV_GAUGE_PARAMETER')
        xi=sp.Symbol('xi'+gauge[1:]); return sp.cancel(spin['metric']-(1-xi)*spin['longitudinal'])
    if suffix=='RAW':
        ctx,group,cov,ph=p; coupling=sp.prod(E(s) for s in ctx['record']['topology']['coupling_monomial'])
        return sp.cancel(coupling*group*cov*ph['phase'])
    if suffix=='TREE_MAP': return normalization(*p)
    if suffix=='NORMALIZED':
        value,m=p; return x.arithmetic('INVERTIBLE_NORMALIZATION',[value,m['scale'],m['inverse']])
    if suffix=='ABSENCE_DOMAIN':
        ctx,d,w=p
        require(ctx['regularization']['uv_poles_retained_for_closure']==['1/epsilon'],'RV_ABSENCE_POLE_ORDER')
        coverage(ctx,d,w)
        return d
    if suffix=='WORD_COVERAGE': return coverage(*p)
    if suffix=='WORD_REDUCTIONS': return word_reduce(p[0])
    if suffix=='POLE': return pole(*p)
    if suffix=='STATE':
        value,d,c=p
        require(value['method']=='ANALYTIC_ABSENCE' and len(c)==12 and d['touched_spinor_chains']==1,'RV_STATE_EVIDENCE')
        return 'EVALUATED_ZERO' if value['canonical_evanescent_simple_pole']==0 else 'EVALUATED_NONZERO'
    raise x.VerificationError('RV_OPERATION_NOT_IMPLEMENTED',key)
