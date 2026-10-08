from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
root=Path('/Users/avatar/Documents/Codex/2026-10-06/hel')
e=root/'work/constant-reduction-20261007/endpoint-report'
a=e/'final-dust-audit'; r=a/'definition-review'; b=root/'outputs/kls-verification/lean'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def source(p,lines,purpose):
 return {'path':str(p),'sha256':sha(p),'lines':lines,'review_purpose':purpose}
upstream=json.loads((r/'upstream-byte-comparison.json').read_text())
assert upstream['byte_identical'] and sha(a/'clean-lean/OAI/Analysis/KLS/Model.lean')==upstream['upstream_sha256']
public=source(a/'FinalKLS500.lean',[[11,19],[21,29],[32,40]],'Exact upstream statement and fixed witness; unchanged original Cheeger constant; both bounds for the same upstream density.')
public['clean_copy_path']=str(a/'clean-lean/FinalKLS500.lean')
public['clean_copy_sha256']=sha(a/'clean-lean/FinalKLS500.lean')
public['clean_copy_byte_identical']=(a/'FinalKLS500.lean').read_bytes()==(a/'clean-lean/FinalKLS500.lean').read_bytes()
assert public['clean_copy_byte_identical']
cheeger=source(a/'cheeger-review/CheegerTwoReverification.lean',[[8,23],[25,33]],'Positive-denominator comparison weakens 1.97 to 2; both original law classes and exact upstream Poincare endpoint are used.')
cheeger['clean_copy_byte_identical']=(a/'cheeger-review/CheegerTwoReverification.lean').read_bytes()==(a/'clean-lean/CheegerTwoReverification.lean').read_bytes()
assert cheeger['clean_copy_byte_identical']
receipts=[]
for name in ['DefinitionIdentityAudit','DefinitionOriginsAudit']:
 d=json.loads((r/f'{name}-build.json').read_text())
 assert d['exit_status']==0 and d['fresh_artifact']
 assert d['source_sha256']==sha(r/f'{name}.lean') and d['log_sha256']==sha(r/f'{name}.log') and d['artifact_sha256']==sha(r/f'{name}.olean')
 receipts.append({'module':name,'receipt_path':str(r/f'{name}-build.json'),'receipt_sha256':sha(r/f'{name}-build.json'), **{k:v for k,v in d.items() if k not in ['command','LEAN_PATH']}})
log=(r/'DefinitionOriginsAudit.log').read_text(); assert 'DEFINITION_ORIGINS_PASSED 31' in log
baseline=json.loads((r/'baseline-source-comparison.json').read_text())
for x in baseline:
 assert x['matches'] and x['sha256']==sha(Path(x['path']))
review={
 'success':True,
 'status':'ACCEPTED',
 'reviewer':'definition_audit',
 'created_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'Definition identity, quantifiers, law and test classes, measure/variance/energy fidelity, local-class equivalence and upstream inclusion, nonvacuity, public endpoint source review, and two freshly compiled independent probes. The parent owns the separate fresh rebuild of the entire dependency closure.',
 'findings':[],
 'accepted_input_sources_changed':False,
 'upstream_identity':{
  'repository':'https://github.com/openai/math',
  'commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a',
  'relative_path':'lean/OAI/Analysis/KLS/Model.lean',
  'official_raw_url':upstream['url'],
  'fetched_utc':upstream['fetched_utc'],
  'bytes':2437,
  'sha256':upstream['upstream_sha256'],
  'accepted_model_byte_identical':True,
  'fresh_rebuild_source_byte_identical':True,
  'evidence':str(r/'upstream-byte-comparison.json'),
  'scope_note':'Exact identity is with this pinned official OpenAI commit, not an assertion about every future upstream revision.'},
 'upstream_semantics':[
  {'lines':[12,16],'verified':'The space is ordinary EuclideanSpace over the reals and densityMeasure is Lebesgue volume.withDensity of ENNReal.ofReal rho.'},
  {'lines':[20,24],'verified':'The density is pointwise nonnegative and measurable, induces a probability measure, and log rho is concave on its convex positive support. No Poincare or Cheeger bound is part of the law hypothesis.'},
  {'lines':[27,32],'verified':'Every coordinate and coordinate product is explicitly integrable; the mean is zero and the second-moment matrix is identity.'},
  {'lines':[34,41],'verified':'Variance is the literal centered-square real integral; Dirichlet energy is the literal squared Euclidean gradient norm integral.'},
  {'lines':[44,49],'verified':'Every globally smooth compactly supported real function is tested by the direct Poincare inequality.'},
  {'lines':[53,58],'verified':'One positive real C is existentially chosen before every n >= 1, every admissible density, and every test. FullStatement is an abbreviation of this same proposition.'}],
 'semantic_bridge':{
  'source':source(e/'openai12500-independent/OpenAIKLSBridge.lean',[[17,65],[67,94]],'Read in full: all upstream laws included and actual real integrals recovered.'),
  'law_inclusion':'Every density satisfying both upstream hypotheses gives an original local admissibleMeasure, with zero-density boundary cases handled in the pointwise log-concavity proof.',
  'isotropy':'Coordinate integrability is converted to finite-dimensional Bochner integrability; the same mean and moment identities are retained.',
  'test_and_integral_bridge':'For each upstream smooth compact test, derivative integrability proves finite Dirichlet energy; the real endpoint supplies L2 membership before the variance identity. The final formula is the actual centered-square integral and actual gradient-energy integral.',
  'precise_equivalence_scope':'KLS.admissibleMeasure_iff_isKLSMeasure is the proved equivalence of the two original local measure classes. OpenAIBridge.admissible is the sufficient inclusion of all upstream densities into that class; this review does not label it an upstream/local biconditional.',
  'local_class_equivalence_sources':[
   source(b/'KLS/Definitions.lean',[[74,78],[105,120],[129,178]],'Original law classes contain probability, log-concavity, and isotropy, not desired functional inequalities.'),
   source(b/'KLS/DensityToClass.lean',[[90,93]],'Actual equivalence theorem of the two original local law classes.'),
   source(b/'KLS/ClassToDensity.lean',[[19,35]],'Reverse direction derives a density for each admissible law.'),
   source(b/'KLS/LogConcavityAbsoluteContinuity.lean',[[1,112]],'Absolute continuity is derived for nondegenerate isotropic log-concave laws.'),
   source(b/'KLS/LogConcaveDensityPotential.lean',[[1,98]],'The canonical density is converted into the original convex-potential density formulation.'),
   source(b/'KLS/RealEndpoint.lean',[[16,51]],'Finite energy and L2 membership precede real-integral variance formula.')]
 },
 'fixed500_endpoint':{
  'accepted':True,
  'source':source(e/'openai500-independent/OpenAIKLS500.lean',[[10,20]],'Exact upstream bound with fixed C=500 and exact upstream KLSStatement/FullStatement.'),
  'uniform_local_premise_source':source(e/'coupled500-full-independent/CoupledRankYoungFullVerification.lean',[[12,36],[50,58]],'The full original admissible law class receives 500 in poincareConstants; regularity assumptions are discharged by approximation.'),
  'meaning':'For every n >= 1 and every upstream isotropic log-concave probability density, every upstream test satisfies Var_mu(f) <= 500 integral ||gradient f||^2 dmu. The number 500 is independent of dimension, law, and test.'},
 'cheeger_endpoint':{
  'accepted':True,
  'original_definition':source(b/'KLS/Definitions.lean',[[82,99]],'The literal original closed Euclidean enlargement, Minkowski boundary liminf, and infimum over nontrivial measurable sets.'),
  'nontrivial_sets_source':source(b/'KLS/CheegerNonvacuity.lean',[[69,77]],'Every positive-dimensional isotropic probability law admits a nontrivial measurable halfspace.'),
  'stronger_endpoint':source(e/'entropy197500-final-independent/Entropy197500FullVerification.lean',[[13,35],[39,47]],'Full original law classes receive 100/(197 sqrt 500); exact upstream proposition is preserved.'),
  'requested_two_corollary':cheeger,
  'meaning':'The original closed-neighborhood Cheeger constant is at least 1/(2 sqrt 500), obtained by weakening the proved stronger lower bound 100/(197 sqrt 500). No altered boundary, restricted law class, or definition change is used.'},
 'public_final_entry':public,
 'nonvacuity':{
  'fresh_probe':str(r/'DefinitionIdentityAudit.lean'),
  'upstream_density_class':'An explicit standard Gaussian real density is formally shown to induce the standard Gaussian measure and satisfy upstream log-concavity and isotropy in every dimension.',
  'original_law_class':'The standard Gaussian is formally exhibited in the original admissibleMeasure class.',
  'upstream_test_class':'A smooth compactly supported bump function with value 1 at the origin is formally exhibited in every dimension.',
  'cheeger_test_class':'The existing theorem KLS.IsIsotropic.exists_cheeger_test provides a measurable set with strictly intermediate mass for every n >= 1.'},
 'compiled_probes':{
  'receipts':receipts,
  'literal_expansion_checks':'upstream_poincare_literal and upstream_statement_literal close by Iff.rfl; fixed500_literal is the fully expanded real-integral inequality with constant 500.',
  'origin_gate_count':31,
  'origin_gates_passed':True,
  'origin_gate_scope':'Checks expected declaration kind, actual defining module, and transitive axiom set for eleven upstream model declarations, eleven original local declarations, and nine bridge/endpoint theorems.',
  'allowed_axioms':['propext','Classical.choice','Quot.sound'],
  'nonstandard_axioms_found':False,
  'freshness_scope':'These two probe artifacts were deleted/recompiled from the displayed source against previously accepted dependencies. This is an independent probe rebuild, not the parent-owned fresh rebuild of all project dependencies.'},
 'original_baseline_comparison':{'all_ten_sources_match_accepted_inventory':True,'evidence':str(r/'baseline-source-comparison.json')},
 'verification_limit':'This review seals definition and endpoint semantics and independent probe results. Publication as freshly rebuilt remains contingent on the parent-owned clean full-closure build, strict endpoint axiom/origin audit, and source/object inventory sealing. It does not assert that that still-running build has already completed.'
}
(r/'review.json').write_text(json.dumps(review,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'path':str(r/'review.json'),'sha256':sha(r/'review.json'),'status':review['status'],'public_source_sha256':public['sha256'],'model_sha256':upstream['upstream_sha256']},indent=2))
