"""Shared source I/O and operation signatures; no scientific answer table.

Never reads the review-side map, oracle, or previous result packets. Record
identities select admitted source decoders, not coefficient/state values.
"""
from formal.python.toe.generic_runner import c03_physical_dag_profile_v1 as physical
from formal.python.toe.generic_runner import provenance_verifier_v4 as x

norm=physical.norm
SCHEMA='SEVEN_RECORD_FINE_OPERATION_PACKET_v1'
RECORDS={
    'RV01':'D6-P2P3-QQ-HDAG-X-RHO8::C4','RV02':'D6-P2P3-QQ-HDAG-X-RHO3::C3',
    'RV03':'D5-QQ-X-HDAG-A','RV04':'D6-PSI4-DUQL','RV05':'D5-DD-X-H-A',
    'RV06':'D6-P2P3-UBAR-Q-X3::C1',
}
SUFFIXES=dict(physical.SUFFIXES,
    topology='source_only_topology_extract.json',
    d5='t_first_r2_active_bnv_d5_reconciliation_pass_0002_v0.json',
    orientation='t_first_r2_active_bnv_d6_clean_room_field_orientation_and_component_reconstruction_audit_pass_0018_v0.json',
    census='f1_reachable_fierz_request_census.json',fallback='native_bmhv_fallback_execution.json',
    n7='native_complete_n7_relation_matrix.json',reps='native_n8_14_quotient_representatives.json',
    dual='native_n8_gram_dual_projectors.json')


def source_material(root=norm.ROOT):
    material,reads=physical.source_material(root)
    _,profile=norm.load_contract(root)
    bound=x.BoundSources(root,profile['allowed_inputs'])
    refs=[]
    def get(label,pointer):
        rows=[r for r in profile['allowed_inputs'] if r['path'].endswith(SUFFIXES[label])]
        x.require(len(rows)==1,'SOURCE_LABEL_NOT_UNIQUE',label)
        row=rows[0]
        ref=dict(artifact_path=row['path'],artifact_sha256=row['sha256'],semantic_locator=pointer)
        value=bound.resolve(ref)
        ref['semantic_locator']=bound.read_receipts[-1]['canonical_pointer']
        refs.append(ref)
        return value
    def add(key,value,used,typ='SOURCE_CONTEXT'):
        material[key]=dict(kind='SOURCE_FACT',operation='SOURCE_DECODE',semantic_type=typ,
                           typed_value=value,evidence_refs=used)
    for key,label,pointer in [
        ('OCCURRENCES','universe','/typed_tensor_occurrences'),('REQUESTS','census','/request_ledger'),
        ('DEFECTS','fallback','/typed_defects'),('COLUMNS','n7','/defect_columns'),
        ('LEDGER','n7','/relation_row_ledger'),('RELATIONS','reps','/rref_matrix'),
        ('REPRESENTATIVES','reps','/representatives'),('ORDER','reps','/ambient_generator_order'),
        ('REP_CACHE','dual','/representative_matrix'),('DUAL_CACHE','dual','/dual_matrix'),
        ('Q_CACHE','dual','/quotient_projector'),('K_CACHE','dual','/relation_remainder_projector')]:
        refs=[]; value=get(label,pointer)
        add('C03.NATIVE.SOURCE.'+key,value,list(refs),
            'INHERITED_RELATION_CONTEXT' if key in ('RELATIONS','LEDGER','DEFECTS') else 'SOURCE_CONTEXT')
    def unique(label,pointer,field,wanted):
        # Resolve the selected child separately, so evidence records the exact
        # canonical pointer rather than just a containing list.
        start=len(refs)
        rows=get(label,pointer)
        indices=[i for i,r in enumerate(rows) if r.get(field)==wanted]
        x.require(len(indices)==1,'SOURCE_SELECTION_NOT_UNIQUE',str(wanted))
        del refs[start:]
        return get(label,pointer+'/'+str(indices[0]))
    for rid,operator in RECORDS.items():
        refs=[]
        top=unique('topology','/rows','source_insertion_id',operator)
        target=unique('targets','/target_vertex_bindings','target_operator_id',operator)
        vertices=[unique('action','/feynman_rule_registry/gauge_matter_three_point','rule_id',v.replace('VTX-GAUGE-','FR-')) for v in top['renormalizable_vertex_ids']]
        fields=[unique('action','/field_registry','field',v['functional_derivative_order'][1]) for v in vertices]
        registered=tensor=None
        if operator.startswith('D5-'):
            rows=get('d5','/candidate_reconciliation'); refs.pop()
            found=[(i,j) for i,g in enumerate(rows) for j,r in enumerate(g['representatives']) if r['family_id']==operator]
            x.require(len(found)==1,'D5_SOURCE_SELECTION')
            i,j=found[0]; source=get('d5',f'/candidate_reconciliation/{i}/representatives/{j}')
        elif rid=='RV04':
            source=unique('d6','/normalized_nonderivative_records/inherited_psi4_warsaw_rows','id','D6-PSI4-Q-DUQL')
        elif rid=='RV06':
            source=unique('orientation','/mixed_conjugation_psi_bar_psi_phi3_reconstruction/rows','fields',target['ordered_fields'])
            source=dict(source,witness=get('orientation','/mixed_conjugation_psi_bar_psi_phi3_reconstruction/explicit_component_witnesses/baruR_qL_X3'))
        else:
            base,ordinal=operator.split('::C')
            groups=get('d6','/normalized_nonderivative_records/psi2_phi3_channel_groups'); refs.pop()
            matches=[i for i,g in enumerate(groups) if g['multiset_id']==base]
            x.require(len(matches)==1 and 0<int(ordinal)<=len(groups[matches[0]]['channels']),'CHANNEL_SELECTION')
            source=get('d6',f'/normalized_nonderivative_records/psi2_phi3_channel_groups/{matches[0]}/channels/{int(ordinal)-1}')
            registered=unique('components','/channel_component_registry','id',base+'::'+source['id'])
            tensor=get('components','/deduplicated_sparse_component_tensor_table/'+registered['component_tensor_fingerprint'])
        gauge=top['coupling_monomial'][0]
        generators=None if gauge=='g1' else get('action','/generator_registry/'+('SU3_fundamental' if gauge=='g3' else 'SU2_fundamental'))
        record=dict(record_id=rid,operator=operator,topology=top,target=target,vertices=vertices,fields=fields,
                    source=source,registered=registered,tensor=tensor,generators=generators)
        context=dict(record=record,regularization=get('scheme','/regularization_and_subtraction'),
            dirac=get('scheme','/bmhv_dirac_contract'),gauge_parameters=get('scheme','/gauge_fixing_and_ghosts/gauge_parameters'),
            fourier=get('action','/space_time_and_fourier_contract'),
            propagators=[unique('action','/propagator_registry','id',pid) for pid in ('PROP-FERMION','PROP-QUANTUM-GAUGE')])
        add(rid+'.SOURCE.CONTEXT',context,list(refs))
    return material,reads+bound.read_receipts


def derived_specs():
    specs=physical.derived_specs()
    def add(key,op,parents,typ='EXACT_LEDGER',kind='DERIVED_FACT'):
        specs[key]=dict(kind=kind,operation=op,parents=parents,semantic_type=typ)
    pre='C03.NATIVE.'
    def n(key,op,parents,typ='EXACT_LEDGER',kind='DERIVED_FACT'):
        add(pre+key,op,[p if p.startswith('C03.') else pre+p for p in parents],typ,kind)
    n('JOIN','DOMAIN_PREDICATE',['SOURCE.OCCURRENCES','SOURCE.REQUESTS','SOURCE.DEFECTS','SOURCE.COLUMNS','SOURCE.ORDER','SOURCE.LEDGER'],kind='APPLICABILITY_DECISION')
    n('CLIFFORD','EXACT_CLIFFORD_ACTION',['SOURCE.OCCURRENCES','JOIN','C03.SOURCE.CLIFFORD_DOMAIN'])
    n('ANGULAR','ANGULAR_AVERAGE',['SOURCE.OCCURRENCES','JOIN','C03.SOURCE.CLIFFORD_DOMAIN'])
    n('CHANNEL','LINEAR_COMBINATION',['SOURCE.OCCURRENCES','C03.SOURCE.GAUGE_PARAMETER','C03.SOURCE.DIAGRAM_PHASE'])
    n('LEGACY','PRODUCT',['SOURCE.OCCURRENCES','CLIFFORD','ANGULAR'])
    n('WEIGHTS','PRODUCT',['SOURCE.OCCURRENCES','C03.DERIVED.IDENTITY_OCCURRENCE_WEIGHT','C03.DERIVED.EXCHANGE_OCCURRENCE_WEIGHT'])
    n('PHASE','PRODUCT',['C03.SOURCE.DIAGRAM_PHASE'])
    n('AMBIENT','PRODUCT',['JOIN','CLIFFORD','ANGULAR','CHANNEL','LEGACY','WEIGHTS','PHASE','C03.DERIVED.CHARGE_PRODUCT'],'NATIVE_AMBIENT_VECTOR')
    n('RELATIONS','RELATION_REDUCTION',['SOURCE.RELATIONS','JOIN'],'SYMBOLIC_MATRIX')
    n('REPRESENTATIVE','EXACT_MATRIX_PROJECTION',['SOURCE.REPRESENTATIVES','SOURCE.REP_CACHE','JOIN'],'SYMBOLIC_MATRIX')
    n('DUAL','RELATION_REDUCTION',['RELATIONS','REPRESENTATIVE','SOURCE.DUAL_CACHE'],'SYMBOLIC_MATRIX')
    n('QUOTIENT','EXACT_MATRIX_PROJECTION',['REPRESENTATIVE','DUAL','SOURCE.Q_CACHE'],'SYMBOLIC_MATRIX')
    n('REMAINDER','TENSOR_DIFFERENCE',['QUOTIENT','SOURCE.K_CACHE'],'SYMBOLIC_MATRIX')
    n('RELATION_CERTIFICATE','RELATION_REDUCTION',['RELATIONS','DUAL','REPRESENTATIVE','QUOTIENT','REMAINDER'])
    n('COORDINATES','EXACT_MATRIX_PROJECTION',['DUAL','AMBIENT'],'NATIVE_COORDINATE_VECTOR')
    n('PROJECTED','EXACT_MATRIX_PROJECTION',['REPRESENTATIVE','COORDINATES'],'NATIVE_AMBIENT_VECTOR')
    n('RELATION_PART','EXACT_MATRIX_PROJECTION',['REMAINDER','AMBIENT'],'NATIVE_AMBIENT_VECTOR')
    n('WITNESS','RELATION_REDUCTION',['RELATIONS','AMBIENT','PROJECTED'],'EXACT_LEDGER')
    n('RESIDUAL','TENSOR_DIFFERENCE',['AMBIENT','PROJECTED','RELATION_PART','WITNESS','RELATIONS'],'NATIVE_AMBIENT_VECTOR')
    n('LEAKAGE_ROW','LINEAR_COMBINATION',['SOURCE.DEFECTS','JOIN','C03.SOURCE.CLIFFORD_DOMAIN'],'NATIVE_AMBIENT_VECTOR')
    n('LEAKAGE','EXACT_MATRIX_PROJECTION',['LEAKAGE_ROW','PROJECTED'],'SYMBOLIC_SCALAR')
    n('STATE','EPISTEMIC_CLASSIFICATION',['COORDINATES','RESIDUAL','LEAKAGE','RELATION_CERTIFICATE'],'EVANESCENT_EVALUATION_STATE','EPISTEMIC_STATE')
    add('C03.OUTPUT.EVANESCENT_COORDINATES','OUTPUT_BIND',[pre+'COORDINATES'],'NATIVE_COORDINATE_VECTOR','OUTPUT_ROOT')
    add('C03.OUTPUT.EVANESCENT_STATE','OUTPUT_BIND',[pre+'STATE'],'EVANESCENT_EVALUATION_STATE','OUTPUT_ROOT')
    for rid in RECORDS:
        def r(key,op,parents,typ='EXACT_LEDGER',kind='DERIVED_FACT'):
            add(rid+'.'+key,op,[rid+'.'+p for p in parents],typ,kind)
        r('DOMAIN','DOMAIN_PREDICATE',['SOURCE.CONTEXT'],kind='APPLICABILITY_DECISION')
        r('TENSOR','TENSOR_SUM',['SOURCE.CONTEXT','DOMAIN'])
        r('CHANNEL','DOMAIN_PREDICATE',['SOURCE.CONTEXT','DOMAIN','TENSOR'],'SYMBOL_TEXT','REPRESENTATION_DISPATCH')
        r('GROUP_IMAGE','GAUGE_GENERATOR_ACTION',['SOURCE.CONTEXT','TENSOR','CHANNEL'])
        r('GROUP','EXACT_MATRIX_PROJECTION',['TENSOR','GROUP_IMAGE'],'SYMBOLIC_SCALAR')
        r('TREE','TENSOR_SUM',['SOURCE.CONTEXT','DOMAIN'],'SYMBOLIC_MATRIX')
        r('WORDS','PRODUCT',['SOURCE.CONTEXT','DOMAIN','TREE'])
        r('METRIC_IMAGE','EXACT_CLIFFORD_ACTION',['SOURCE.CONTEXT','WORDS','TREE'],'SYMBOLIC_MATRIX')
        r('WARD_IMAGE','WARD_REDUCTION',['SOURCE.CONTEXT','WORDS','TREE'],'SYMBOLIC_MATRIX')
        r('SPINOR_PROJECTION','EXACT_MATRIX_PROJECTION',['TREE','METRIC_IMAGE','WARD_IMAGE'])
        r('PHASE','PRODUCT',['SOURCE.CONTEXT','WORDS'])
        r('COVARIANT','LINEAR_COMBINATION',['SOURCE.CONTEXT','SPINOR_PROJECTION'],'SYMBOLIC_SCALAR')
        r('RAW','PRODUCT',['SOURCE.CONTEXT','GROUP','COVARIANT','PHASE'],'SYMBOLIC_SCALAR')
        r('TREE_MAP','EXACT_MATRIX_PROJECTION',['SOURCE.CONTEXT','TENSOR','TREE'])
        r('NORMALIZED','INVERTIBLE_NORMALIZATION',['RAW','TREE_MAP'],'SYMBOLIC_SCALAR','NORMALIZATION_MAP')
        r('ABSENCE_DOMAIN','DOMAIN_PREDICATE',['SOURCE.CONTEXT','DOMAIN','WORDS'],kind='APPLICABILITY_DECISION')
        r('WORD_COVERAGE','ANGULAR_AVERAGE',['SOURCE.CONTEXT','ABSENCE_DOMAIN','WORDS'])
        r('WORD_REDUCTIONS','EXACT_CLIFFORD_ACTION',['WORD_COVERAGE'])
        r('POLE','RELATION_REDUCTION',['SOURCE.CONTEXT','WORD_REDUCTIONS','ABSENCE_DOMAIN'])
        r('STATE','EPISTEMIC_CLASSIFICATION',['POLE','ABSENCE_DOMAIN','WORD_COVERAGE'],'EVANESCENT_EVALUATION_STATE','EPISTEMIC_STATE')
        r('OUTPUT.PHYSICAL_COEFFICIENT','OUTPUT_BIND',['NORMALIZED'],'SYMBOLIC_SCALAR','OUTPUT_ROOT')
        r('OUTPUT.EVANESCENT_STATE','OUTPUT_BIND',['STATE'],'EVANESCENT_EVALUATION_STATE','OUTPUT_ROOT')
        if rid=='RV03': r('OUTPUT.SOURCE_CHANNEL','OUTPUT_BIND',['CHANNEL'],'SYMBOL_TEXT','OUTPUT_ROOT')
    return specs


def structural_contract(material):
    specs=derived_specs()
    return dict(node_schema=physical.structural_contract()['node_schema'],
        allowed_node_kinds=sorted({v['kind'] for v in list(material.values())+list(specs.values())}),
        allowed_operations=sorted({v['operation'] for v in list(material.values())+list(specs.values())}),
        output_roots_required=sorted(k for k,v in specs.items() if v['kind']=='OUTPUT_ROOT'))
