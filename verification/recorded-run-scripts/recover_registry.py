"""Strict, named import-origin reconciliation after a successful kernel audit.

The original primary audit and its receipts are immutable. Its Python registry
comparison stopped because filtering a larger import environment by module
discarded two existing helper names. Five further rows choose another existing
origin. No mathematics or axiom requirement is changed here. A fresh companion
checks all seven literal types, exact selected origins, and axiom closures.
"""
import ast
import json
import re
from rebuild import D, SRC, LIB, LOGS, PRIOR, ACCEPTED, sha, read, write
from rebuild import verify_sources, check_accepted

STANDARD = ['Classical.choice', 'Quot.sound', 'propext']
CASES = {
    'KLS.matrixFrobeniusSq.eq_1':
        ('KLS.ExponentialQuadratic', 'KLS.SteinMatrixContraction', 'generated unfolding equation', True),
    'KLS.CenteredExponential.instIsProbabilityMeasureRealExpMeasureOfNat_kLS_1':
        ('KLS.ExponentialQuadratic', 'KLS.ExponentialPoincare', 'generated local probability instance', True),
    'KLS.coordinateDerivative_sq':
        ('KLS.HarmonicBernsteinPointwise', 'KLS.WeightedDiffusionSquare', 'duplicate handwritten theorem with identical type', False),
    'KLS.potentialMeasure.eq_1':
        ('KLS.ConvexPotentialCoercivity', 'KLS.WeightedEigenClassical', 'generated unfolding equation', False),
    'KLS.tiltLogLaplace.eq_1':
        ('KLS.TiltCumulantLowOrders', 'KLS.AdaptiveLogMGFSpatial', 'generated unfolding equation', False),
    'KLS.tiltThirdCumulant.eq_1':
        ('KLS.LogTiltCumulants', 'KLS.CumulantBounds', 'generated unfolding equation', False),
    'KLS.weightedIterationEnergy.congr_simp':
        ('KLS.WeightedEigenSuccessorIteration', 'KLS.WeightedIterationBochner', 'generated congruence theorem', False),
}

for filename, digest in {
    'audit-execution.json':'7305963a08b25d40fc97dd837444aac9e37f15ac732ad22dd50296e20fbb1090',
    'required-declarations.json':'04a4bcf228e18425e53b8482d25d01e69d9919184c601111c196f8b21c85b24f',
    'expected-prior-declarations.json':'64f2d6c5b3fee596aea0169feb39e16f925139b3a8bf98cb70e5e83820f5fd15',
    'generated-unfolding-origin-overlap.json':'ecf8e919fe976b779973ad0df883bc04a6b831ea9208ad540cdfa37305c85aa2',
    'audit.py':'d327ae76701e0087fa96a448233554e618c601249873920e640fbebb287dc34e',
}.items():
    assert sha(D/filename) == digest, filename
execution = read(D/'audit-execution.json')
assert execution['exit_status'] == 0 and execution['fresh_object']
assert execution['source_sha256'] == sha(SRC/'FinalKLS500Audit.lean') == 'a089d8bcbcc15f809bc71a52bafb4c34ce38c5d51b04bf1e45eaf24de0e64e83'
assert execution['log_sha256'] == sha(LOGS/'FinalKLS500Audit.log') == '3fba305fe1d1da12074a8ce67475167b25a6ab82cee3dc11bd2e622bc94deb81'
assert execution['object_sha256'] == sha(LIB/'FinalKLS500Audit.olean') == 'f8b9a87d6156f030ef3f487e2944f3958236b69f7bf83c10f279091814e0d9fd'

completion = read(D/'build-completion.json')
assert completion['success'] and completion['all_scheduler_and_post_build_checks_complete']
for field in ['prepare_receipt', 'build_receipt', 'post_build_input_check']:
    assert completion[field+'_sha256'] == sha(D/completion[field+'_file'])
assert completion['artifact_inventory_sha256'] == sha(D/'fresh-build-artifact-inventory.json')
manifest = read(D/completion['prepare_receipt_file'])
build = read(D/completion['build_receipt_file'])
sources = manifest['source_provenance']
assert build['success'] and build['completed'] == manifest['source_modules'] == len(sources) == 1710
assert not manifest['old_project_objects_in_search_path'] and not build['old_project_objects_imported']
assert len(build['results']) == len({e['module'] for e in build['results']}) == 1710
verify_sources(manifest)
artifacts = read(D/'fresh-build-artifact-inventory.json')
for p, v in artifacts.items():
    assert sha(LIB/p) == v, p
for e in build['results']:
    assert e['exit_status'] == 0 and e['fresh_object'] and e['errors'] == 0
    assert e['source_sha256'] == sources[e['module']]['source_sha256']
    assert sha(e['log']) == e['log_sha256']
    for p, v in e['artifacts'].items():
        assert sha(LIB/p) == v, p
for p, v in completion['repair_and_range_extension_ancestry_sha256'].items():
    assert sha(D/p) == v, p

text = (LOGS/'FinalKLS500Audit.log').read_text()
assert 'warning:' not in text and 'error:' not in text
pattern = r'^ORIGIN_AXIOMS ([^\n|]+)\|([^\n|]+)\|([^\n|]+)\|\[([^\]]*)\]'
rows = [{'name':n, 'module':m, 'kind':k,
         'axioms':sorted(x.strip() for x in a.split(',') if x.strip())}
        for n,m,k,a in re.findall(pattern, text, re.M)]
actual = {e['name']:{k:e[k] for k in ['module','kind','axioms']} for e in rows}
count, theorems = map(int, re.search(r'^ALL_ORIGINS_PASSED (\d+)\|(\d+)$',text,re.M).groups())
assert count == len(rows) == len(actual) == 22017
assert theorems == sum(e['kind']=='theorem' for e in rows) == 19686
assert all(set(e['axioms']) <= set(STANDARD) for e in rows)
assert all(e['module'] in sources for e in rows)
gates = read(D/'required-declarations.json')
assert len(gates) == len({e['name'] for e in gates}) == 3651
assert re.search(r'^GATES_PASSED 3651$', text, re.M)
for e in gates:
    assert actual[e['name']]['module'] == e['module']
    expected_kind = 'definition' if e['kind']=='def' else e['kind']
    assert actual[e['name']]['kind'] == expected_kind
assert not (set(CASES) & {e['name'] for e in gates})

prior_receipt = read(ACCEPTED/'accepted-baseline-receipt.json')
assert sha(PRIOR/'receipt.json') == sha(ACCEPTED/'accepted-baseline-receipt.json')
assert sha(PRIOR/'expected-all-declarations.json') == prior_receipt['evidence_sha256']['expected-all-declarations.json']
old_global = read(PRIOR/'expected-all-declarations.json')
prior = read(D/'expected-prior-declarations.json')
assert len(prior) == 22002
new_names = {e['name'] for e in gates if e['module'] in ['CheegerTwoReverification','FinalKLS500','FinalKLSRange']}
assert len(new_names) == 13
restored = {n for n,e in CASES.items() if e[3]}
assert set(actual)-set(prior)-new_names == restored
assert not (set(prior)-set(actual))
origin_mismatches = {n for n,e in prior.items() if actual[n] != e}
assert origin_mismatches == set(CASES)-restored

companion = read(D/'generated-helper-execution.json')
assert companion['success'] and companion['exit_status'] == 0 and companion['fresh_object']
assert companion['source_sha256'] == sha(SRC/'GeneratedProvenanceAudit.lean')
assert companion['log_sha256'] == sha(LOGS/'GeneratedProvenanceAudit.log')
assert companion['object_sha256'] == sha(LIB/'GeneratedProvenanceAudit.olean')
companion_text = (LOGS/'GeneratedProvenanceAudit.log').read_text()
assert 'warning:' not in companion_text and 'error:' not in companion_text
assert re.search(r'^SELECTED_ORIGIN_GATES_PASSED 7$',companion_text,re.M)
probe_rows = [(n,m,k,sorted(x.strip() for x in a.split(',') if x.strip()))
              for n,m,k,a in re.findall(pattern.replace('ORIGIN_AXIOMS','SELECTED_ORIGIN_OK'),companion_text,re.M)]
assert len(probe_rows) == len({r[0] for r in probe_rows}) == 7
probe = {n:{'module':m,'kind':k,'axioms':a} for n,m,k,a in probe_rows}
assert set(probe) == set(CASES)
assert (SRC/'GeneratedProvenanceAudit.lean').read_text().count('#check (') == 7
reconciled = dict(prior)
case_rows = []
for n,(old_origin,new_origin,classification,was_filtered) in CASES.items():
    old = old_global[n]
    old_row = {'module':old['origin'],'kind':old['kind'],'axioms':sorted(old['axioms'])}
    assert old_row == {'module':old_origin,'kind':'theorem','axioms':STANDARD}
    if was_filtered:
        assert n not in prior and old_origin not in sources
    else:
        assert prior[n] == old_row and old_origin in sources
    selected = {'module':new_origin,'kind':'theorem','axioms':STANDARD}
    assert actual[n] == probe[n] == selected and new_origin in sources
    reconciled[n] = selected
    case_rows.append({'name':n,'baseline':old_row,'selected_final':selected,
                      'classification':classification,
                      'excluded_by_old_origin_filter':was_filtered,
                      'literal_type_and_exact_origin_checked_in_companion':True})
assert len(reconciled) == 22004
assert set(actual) == set(reconciled)|new_names
for n,e in reconciled.items():
    assert actual[n] == e, (n,actual[n],e)
tree = ast.parse((D/'audit.py').read_text())
endpoints = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)
                 and any(isinstance(t,ast.Name) and t.id=='endpoints' for t in n.targets))
assert len(endpoints) == 23
for n in endpoints:
    assert actual[n]['kind']=='theorem' and actual[n]['axioms']==STANDARD

overlap = read(D/'generated-unfolding-origin-overlap.json')
assert len(overlap)==1 and overlap[0]['name']=='KLS.hessianSquare.eq_1'
assert actual[overlap[0]['name']] == overlap[0]['accepted_final']
write(D/'selected-origin-reconciliation.json', {
    'success':True,'finite_named_cases':case_rows,
    'existing_hessian_overlap':overlap,
    'prior_registry_names_preserved':True,
    'all_other_prior_rows_preserved_exactly':True,
    'companion_execution_sha256':sha(D/'generated-helper-execution.json'),
    'total_documented_selected_origin_cases':8})
write(D/'all-declaration-axioms.json',rows)
printed = text.split('ALL_ORIGINS_PASSED '+str(count)+'|'+str(theorems)+'\n',1)[1]
(D/'actual-endpoint-types.txt').write_text(printed)
verify_sources(manifest)
for p,v in artifacts.items():
    assert sha(LIB/p)==v,p
post=check_accepted()
write(D/'post-audit-input-check.json',post)
write(D/'registry-comparison-recovery.json', {
    'success':True,'reason':'The primary Lean kernel audit passed. Its original Python registry comparison stopped on two names excluded by filtering old module origins. The complete comparison additionally found five exact origin-only differences.',
    'original_primary_execution_sha256':sha(D/'audit-execution.json'),
    'primary_audit_source_log_and_object_unchanged':True,
    'old_filtered_registry_sha256':sha(D/'expected-prior-declarations.json'),
    'old_full_registry_sha256':sha(PRIOR/'expected-all-declarations.json'),
    'new_public_names':sorted(new_names),'restored_existing_names':sorted(restored),
    'origin_only_replacements':sorted(origin_mismatches),
    'selected_origin_reconciliation_sha256':sha(D/'selected-origin-reconciliation.json'),
    'companion_execution_sha256':sha(D/'generated-helper-execution.json'),
    'recovery_runner_sha256':sha(D/'recover_registry.py'),
    'no_blanket_name_origin_or_axiom_allowance':True,
    'mathematical_sources_and_objects_unchanged':True})
warnings=read(D/'warning-review.json')
assert warnings['all_warning_lines_unchanged'] and warnings['new_proof_module_warnings']==0
summary = {
    'success':True,'kernel_trust_level':0,'fresh_math_modules':1710,
    'baseline_math_modules':manifest['baseline_modules'],
    'additional_math_modules':manifest['additional_modules'],
    'fresh_audit_modules':2,'all_project_objects_fresh':True,
    'old_project_object_search_paths':[], 'external_pinned_dependency_cache_reused':True,
    'checked_declarations':count,'checked_theorems':theorems,
    'strict_name_origin_kind_gates':3658,'primary_strict_gates':3651,
    'companion_strict_gates':7,'literal_companion_type_checks':7,
    'exact_prior_declaration_names_kinds_and_axioms_preserved':True,
    'prior_origins_preserved_except_eight_individually_reviewed_cases':True,
    'selected_origin_reconciliation_sha256':sha(D/'selected-origin-reconciliation.json'),
    'registry_recovery_receipt_sha256':sha(D/'registry-comparison-recovery.json'),
    'all_declaration_axioms_subset_standard_three':True,
    'all_endpoint_axioms_exactly_standard_three':True,
    'endpoint_names':endpoints,'poincare_bound':500,
    'cheeger_coefficient_proved':'197/100','cheeger_coefficient_two_corollary':True,
    'universal_optimal_poincare_range':['4','500'],
    'lower_bound_witness':'centered unit exponential law with exact Poincare constant 4',
    'exact_openai_endpoint':'OAI.LeanBlast.KLS.KLSStatement',
    'upstream_model_source_sha256':sha(SRC/'OAI/Analysis/KLS/Model.lean'),
    'new_proof_module_warnings':0,
    'baseline_warning_count':warnings['baseline_warning_count'],
    'accepted_additional_warning_count':warnings['accepted_additional_warning_count'],
    'all_accepted_warning_lines_unchanged':True,
    'original_sources_changed':False,'constants_optimized_during_audit':False,
    'proof_build_receipt_sha256':sha(D/completion['build_receipt_file']),
    'build_completion_sha256':sha(D/'build-completion.json'),
    'all_fresh_artifacts_including_ir_and_sig_sha256':sha(D/'fresh-build-artifact-inventory.json'),
    'audit_execution_sha256':sha(D/'audit-execution.json'),
    'companion_execution_sha256':sha(D/'generated-helper-execution.json'),
    'actual_endpoint_types_sha256':sha(D/'actual-endpoint-types.txt'),
    'review_status':'pending','final_accepted_input_recheck':post}
write(D/'verification-summary.json',summary)
print(json.dumps({k:summary[k] for k in ['success','fresh_math_modules','fresh_audit_modules',
    'checked_declarations','checked_theorems','strict_name_origin_kind_gates']},indent=2))
