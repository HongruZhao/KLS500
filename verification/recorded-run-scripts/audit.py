"""Audit every declaration in the freshly rebuilt final dependency closure."""
from pathlib import Path
import ast
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time

from rebuild import D, E, B, ACCEPTED, BASE, PRIOR, SRC, LIB, LOGS, LEAN, FLAGS
from rebuild import sha, read, write, rel, verify_sources, check_accepted

COMPLETION = read(D / 'build-completion.json')
M = read(D / COMPLETION['prepare_receipt_file'])
BUILD = read(D / COMPLETION['build_receipt_file'])
assert BUILD['success'] and BUILD['completed'] == M['source_modules'] == 1710
assert not BUILD['old_project_objects_imported']
assert COMPLETION['success'] and COMPLETION['all_scheduler_and_post_build_checks_complete']
assert COMPLETION['build_receipt_sha256'] == sha(D/COMPLETION['build_receipt_file'])
assert COMPLETION['prepare_receipt_sha256'] == sha(D/COMPLETION['prepare_receipt_file'])
assert COMPLETION['post_build_input_check_sha256'] == sha(D/COMPLETION['post_build_input_check_file'])
assert COMPLETION['artifact_inventory_sha256'] == sha(D/'fresh-build-artifact-inventory.json')
for p,v in COMPLETION['repair_and_range_extension_ancestry_sha256'].items():
    assert sha(D/p) == v,p
FRESH_ARTIFACTS = read(D/'fresh-build-artifact-inventory.json')
for p,v in FRESH_ARTIFACTS.items():
    assert sha(LIB/p)==v,p
verify_sources(M)
for e in BUILD['results']:
    assert e['exit_status'] == 0 and e['fresh_object']
    assert sha(e['log']) == e['log_sha256']
    assert e['errors'] == 0
    for p, v in e['artifacts'].items():
        assert sha(LIB / p) == v

sources = M['source_provenance']
warning_rows = []
new_public_modules = {'CheegerTwoReverification','FinalKLS500','FinalKLSRange'}
accepted_roots = {Path(e['path']) for e in read(ACCEPTED/'accepted-dependency-paths.json')} | {ACCEPTED}
for e in BUILD['results']:
    if not e['warnings']:
        continue
    m = e['module']
    assert m not in new_public_modules, ('new public-module warnings', m)
    if sources[m]['baseline']:
        old_log = BASE / 'evidence/source-rebuild' / (m + '.log')
    else:
        owner = Path(sources[m]['source']).parent
        assert owner in accepted_roots, ('unaccepted warning source',m,owner)
        old_log = owner/'logs'/(m+'.log')
        old_inventory = read(owner/'evidence-sha256.json')
        assert old_inventory[str(old_log.relative_to(owner))] == sha(old_log)
    old_lines = [s for s in old_log.read_text().splitlines() if 'warning:' in s]
    new_lines = [s for s in Path(e['log']).read_text().splitlines() if 'warning:' in s]
    assert new_lines == old_lines, ('changed accepted warnings', m)
    warning_rows.append({'module':m,'warning_count':e['warnings'],
                         'baseline_module':sources[m]['baseline'],
                         'accepted_log':str(old_log),'accepted_log_sha256':sha(old_log),
                         'warning_lines_exactly_equal_accepted_log':True,
                         'warning_lines':new_lines})
write(D / 'warning-review.json', {'new_proof_module_warnings':0,
      'baseline_warning_count':sum(e['warning_count'] for e in warning_rows if e['baseline_module']),
      'accepted_additional_warning_count':sum(e['warning_count'] for e in warning_rows if not e['baseline_module']),
      'all_warning_lines_unchanged':True,'modules':warning_rows})
prior_receipt = read(ACCEPTED / 'accepted-baseline-receipt.json')
assert sha(PRIOR/'receipt.json') == sha(ACCEPTED/'accepted-baseline-receipt.json')
for f in ['expected-all-declarations.json','expected-canonical-gates.json']:
    assert sha(PRIOR/f) == prior_receipt['evidence_sha256'][f],f
baseline_expected = read(PRIOR / 'expected-all-declarations.json')
expected = {n: {'module': e['origin'], 'kind': e['kind'], 'axioms': sorted(e['axioms'])}
            for n, e in baseline_expected.items() if e['origin'] in sources}
generated_origin_overlaps = []
for e in read(ACCEPTED / 'all-origin-declarations.json'):
    if e['module'] in sources:
        if e['name'] in expected:
            assert e['name'] == 'KLS.hessianSquare.eq_1', e
            old = expected[e['name']]
            assert old['module'] == 'KLS.WeightedSuccessorDomain'
            assert e['module'] == 'ResolventGradientKato'
            assert old['kind'] == e['kind'] == 'theorem'
            assert old['axioms'] == e['axioms'] == ['Classical.choice','Quot.sound','propext']
            generated_origin_overlaps.append({'name':e['name'],'baseline':old,
                'accepted_final':{k:e[k] for k in ['module','kind','axioms']},
                'explanation':'Lean generates this reflexive unfolding theorem on demand in multiple modules. The accepted final environment selects ResolventGradientKato; the fresh environment must match that exact origin and the literal type.'})
        expected[e['name']] = {k: e[k] for k in ['module','kind','axioms']}
assert len(generated_origin_overlaps) == 1
write(D/'generated-unfolding-origin-overlap.json',generated_origin_overlaps)

gates = {n: {'name':n,'module':e['origin'],
             'kind': 'def' if e['kind'] == 'definition' else e['kind']}
         for n,e in read(PRIOR / 'expected-canonical-gates.json').items()
         if e['origin'] in sources}
for e in read(ACCEPTED / 'required-declarations.json'):
    if e['module'] in sources:
        assert e['name'] not in gates
        gates[e['name']] = e

endpoints = [
    'OAI.LeanBlast.KLS.poincareBound500',
    'OAI.LeanBlast.KLS.klsStatement500',
    'OAI.LeanBlast.KLS.fullStatement500',
    'KLS.admissibleMeasure.real_poincare_coupledRankYoung',
    'KLS.entropyCheegerCoefficient_lt_two',
    'KLS.admissibleMeasure.cheeger_lower_entropy197_500',
    'KLS.exactOpenAIKLSStatement_entropy197_500',
    'KLS.dimensionFree500_and_cheeger197',
    'KLS.FinalDustCheegerReview.coefficient_two_comparison',
    'KLS.FinalDustCheegerReview.original_admissible_cheeger_two',
    'KLS.FinalDustCheegerReview.original_density_cheeger_two',
    'KLS.FinalDustCheegerReview.exact_openai_poincare500_and_original_cheeger_two',
    'KLS.Final.openaiKLS',
    'KLS.Final.openaiPoincare500',
    'KLS.Final.cheegerTwo',
    'KLS.Final.cheeger197',
    'KLS.Final.openaiDensityBounds',
    'KLS.Final.universalPoincareRange',
    'KLS.Final.poincareKLS',
    'KLS.Final.cheegerKLS',
    'KLS.Final.fullCheegerKLS',
    'KLS.four_le_universalPoincareConstant',
    'KLS.CenteredExponential.admissible_and_poincareConstant_eq_four',
]
for name in endpoints:
    if name.startswith('KLS.FinalDustCheegerReview.'):
        module = 'CheegerTwoReverification'
    elif name.startswith('KLS.Final.'):
        module = ('FinalKLSRange' if name in ['KLS.Final.universalPoincareRange',
                  'KLS.Final.poincareKLS','KLS.Final.cheegerKLS','KLS.Final.fullCheegerKLS']
                  else 'FinalKLS500')
    else:
        module = expected[name]['module']
    if name not in gates:
        gates[name] = {'name':name, 'module':module, 'kind':'theorem'}
new_names = {n for n,e in gates.items() if e['module'] in ['CheegerTwoReverification','FinalKLS500','FinalKLSRange']}

tree = ast.parse((E / 'replay_cumulant32_independent.py').read_text())
body = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)
            and any(isinstance(t,ast.Name) and t.id == 'body' for t in n.targets))
body = body.replace('for (gate, origin, theoremOnly) in gates do',
                    'for (gate, origin, wantedKind) in gates do')
body = body.replace('| some (.thmInfo _) => unless theoremOnly do throwError "Expected definition: {gate}"',
                    '| some (.thmInfo _) => unless wantedKind == "theorem" do throwError "Expected other declaration kind: {gate}"')
body = body.replace('| some (.defnInfo _) => if theoremOnly then throwError "Expected theorem: {gate}"',
                    '| some (.defnInfo _) => unless wantedKind == "def" do throwError "Expected other declaration kind: {gate}"\n    | some (.inductInfo _) => unless wantedKind == "inductive" do throwError "Expected other declaration kind: {gate}"')
gate_list = list(gates.values())
chunks = []
for i in range(0,len(gate_list),200):
    chunk = gate_list[i:i+200]
    chunks.append('@[noinline] private def auditGateChunk'+str(i//200)+
                  ' : Array (Name × Name × String) := #[\n'+
                  ',\n'.join('    (`'+e['name']+', `'+e['module']+', "'+e['kind']+'")' for e in chunk)+']\n')
head = ('import FinalKLSRange\nimport Lean.Util.CollectAxioms\n'
        'set_option maxRecDepth 8192\nset_option maxHeartbeats 0\nopen Lean Elab Command\nopen scoped BigOperators\n')
head += '\n'.join(chunks)
head += '\nrun_cmd do\n  let env ← getEnv\n'
head += '  let origins : Array Name := #['+', '.join('`'+m for m in sources)+']\n'
head += '  let gateGroups : Array (Array (Name × Name × String)) := #['+', '.join('auditGateChunk'+str(i) for i in range(len(chunks)))+']\n'
head += '  let gates := gateGroups.foldl (fun a b => a ++ b) #[]\n'
model_definitions = ['KLSStatement','PoincareBound','IsTestFunction','variance','dirichletEnergy']
tail = '\n'+ '\n'.join('#check '+n+'\n#print axioms '+n for n in endpoints)+'\n'
tail += '\n'.join('#print OAI.LeanBlast.KLS.'+n for n in model_definitions)+'\n'
tail += ('#check (KLS.hessianSquare.eq_1 : ∀ {n : ℕ} (g : KLS.Space n → ℝ) '
         '(x : KLS.Space n), KLS.hessianSquare g x = '
         '∑ i : Fin n, ∑ j : Fin n, (KLS.coordinateHessian g x i j) ^ 2)\n')
audit_name = 'FinalKLS500Audit'
src, obj, log = SRC/(audit_name+'.lean'), LIB/(audit_name+'.olean'), LOGS/(audit_name+'.log')
assert not src.exists() and not obj.exists()
src.write_text(head+body+tail)
write(D/'required-declarations.json',gate_list)
write(D/'expected-prior-declarations.json',expected)
env = dict(os.environ,LEAN_PATH=os.pathsep.join(M['LEAN_PATH']),LEAN_NUM_THREADS='1',
           OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1')
cmd=[str(LEAN),*FLAGS,'-o',str(obj),str(src.relative_to(SRC))]
started=time.monotonic()
with log.open('w') as out:
    status=subprocess.run(cmd,cwd=SRC,env=env,stdout=out,stderr=subprocess.STDOUT).returncode
execution={'command':cmd,'exit_status':status,'seconds':round(time.monotonic()-started,3),
           'source_sha256':sha(src),'log':str(log),'log_sha256':sha(log),
           'object_sha256':sha(obj) if obj.exists() else None,'fresh_object':True}
write(D/'audit-execution.json',execution)
assert status == 0, log
text=log.read_text()
assert 'warning:' not in text and 'error:' not in text
rows=[{'name':n,'module':m,'kind':k,'axioms':sorted(x.strip() for x in a.split(',') if x.strip())}
      for n,m,k,a in re.findall(r'^ORIGIN_AXIOMS ([^\n|]+)\|([^\n|]+)\|([^\n|]+)\|\[([^\]]*)\]',text,re.M)]
counts=re.search(r'^ALL_ORIGINS_PASSED (\d+)\|(\d+)$',text,re.M)
assert counts is not None
count,theorems=map(int,counts.groups())
actual={e['name']:{k:e[k] for k in ['module','kind','axioms']} for e in rows}
assert count==len(rows)==len(actual)
assert theorems==sum(e['kind']=='theorem' for e in rows)
assert set(actual)==set(expected)|new_names, (set(actual)-set(expected)-new_names,set(expected)-set(actual))
for n,e in expected.items():
    assert actual[n]==e,(n,actual[n],e)
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(e['axioms'])<=allowed for e in rows)
for n in endpoints:
    assert actual[n]['kind']=='theorem' and set(actual[n]['axioms'])==allowed,n
assert 'GATES_PASSED '+str(len(gate_list)) in text
assert all(e['module'] in sources for e in rows)
write(D/'all-declaration-axioms.json',rows)
printed=text.split('ALL_ORIGINS_PASSED '+str(count)+'|'+str(theorems)+'\n',1)[1]
(D/'actual-endpoint-types.txt').write_text(printed)
verify_sources(M)
for p,v in FRESH_ARTIFACTS.items():
    assert sha(LIB/p)==v,p
post=check_accepted()
for p,v in COMPLETION['repair_and_range_extension_ancestry_sha256'].items():
    assert sha(D/p) == v,p
write(D/'post-audit-input-check.json',post)
summary={'success':True,'kernel_trust_level':0,'fresh_math_modules':len(sources),
         'baseline_math_modules':M['baseline_modules'],'additional_math_modules':M['additional_modules'],
         'fresh_audit_modules':1,'all_project_objects_fresh':True,
         'old_project_object_search_paths':[], 'external_pinned_dependency_cache_reused':True,
         'checked_declarations':count,'checked_theorems':theorems,
         'strict_name_origin_kind_gates':len(gate_list),
         'exact_prior_declaration_names_kinds_and_axioms_preserved':True,
         'prior_origins_preserved_except_one_documented_generated_unfolding':True,
         'generated_unfolding_origin_overlap_sha256':sha(D/'generated-unfolding-origin-overlap.json'),
         'all_declaration_axioms_subset_standard_three':True,
         'all_endpoint_axioms_exactly_standard_three':True,
         'endpoint_names':endpoints,'poincare_bound':500,
         'cheeger_coefficient_proved':'197/100','cheeger_coefficient_two_corollary':True,
         'universal_optimal_poincare_range':['4','500'],
         'lower_bound_witness':'centered unit exponential law with exact Poincare constant 4',
         'exact_openai_endpoint':'OAI.LeanBlast.KLS.KLSStatement',
         'upstream_model_source_sha256':sha(SRC/'OAI/Analysis/KLS/Model.lean'),
         'new_proof_module_warnings':0,
         'baseline_warning_count':sum(e['warning_count'] for e in warning_rows if e['baseline_module']),
         'accepted_additional_warning_count':sum(e['warning_count'] for e in warning_rows if not e['baseline_module']),
         'baseline_warning_lines_unchanged':True,
         'original_sources_changed':False,'constants_optimized_during_audit':False,
         'proof_build_receipt_sha256':sha(D/COMPLETION['build_receipt_file']),
         'build_completion_sha256':sha(D/'build-completion.json'),
         'all_fresh_artifacts_including_ir_and_sig_sha256':sha(D/'fresh-build-artifact-inventory.json'),
         'audit_execution_sha256':sha(D/'audit-execution.json'),
         'actual_endpoint_types_sha256':sha(D/'actual-endpoint-types.txt'),
         'review_status':'pending','final_accepted_input_recheck':post}
write(D/'verification-summary.json',summary)
print(json.dumps({k:summary[k] for k in ['success','fresh_math_modules','checked_declarations','checked_theorems','strict_name_origin_kind_gates','poincare_bound','cheeger_coefficient_proved','cheeger_coefficient_two_corollary']},indent=2),flush=True)
