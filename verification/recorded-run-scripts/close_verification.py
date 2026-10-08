"""Seal the passed proof audit, three reviews, publication text, and PDF QA."""
from pathlib import Path
import datetime
import re
import shutil
from rebuild import D, SRC, LIB, LOGS, sha, read, write

assert not (D/'final-verification-receipt.json').exists()
summary = read(D/'verification-summary.json')
assert summary['success'] and summary['review_status']=='pending'
assert summary['fresh_math_modules']==1710 and summary['fresh_audit_modules']==2
assert summary['checked_declarations']==22017 and summary['checked_theorems']==19686
assert summary['strict_name_origin_kind_gates']==3658
for field,file in [
    ('proof_build_receipt_sha256','effective-build-receipt.json'),
    ('build_completion_sha256','build-completion.json'),
    ('audit_execution_sha256','audit-execution.json'),
    ('companion_execution_sha256','generated-helper-execution.json'),
    ('selected_origin_reconciliation_sha256','selected-origin-reconciliation.json'),
    ('registry_recovery_receipt_sha256','registry-comparison-recovery.json'),
    ('actual_endpoint_types_sha256','actual-endpoint-types.txt')]:
    assert summary[field]==sha(D/file),file
for receipt_name,module in [('audit-execution.json','FinalKLS500Audit'),
                            ('generated-helper-execution.json','GeneratedProvenanceAudit')]:
    e=read(D/receipt_name)
    assert e['exit_status']==0 and e['fresh_object']
    assert e['source_sha256']==sha(SRC/(module+'.lean'))
    assert e['log_sha256']==sha(LOGS/(module+'.log'))
    assert e['object_sha256']==sha(LIB/(module+'.olean'))

review_pins = {
    'definition-review/review.json':'247b445809845b387b54e0039707a74106db6ad24bd80c22060629782ed552e2',
    'definition-review/wrapper-comment-addendum.json':'09ce8b9625770029fb1fe663c8e915cd68a51c5718bc5d40a4c2702fcd37f5e0',
    'definition-review/report-semantic-review.json':'3f25c1e639f67304be357b24b2f954ed07f60804e6a7b218a0b61a7e54b52069',
    'definition-review/registry-reconciliation-review.json':'bf30f41716d61b4ee21f703624da0049e5d2ce53ec3947fdbc126bf5754ba3a4',
    'definition-review/registry-recovery-runner-review.json':'73e896197120a67aeafff08d010c84e80d0e17c40e85fa5f4c8025d151523386',
    'poincare-review/review.json':'77fba0558b6b32e004159d480e4c148370467bf6dc6ef261f098a6c7f6d0df56',
    'poincare-review/runner-review.json':'28e0bbe182bf3cc512e11fc3b18943175aa6b677e2ec2cb013cadf695e4948f3',
    'poincare-review/recovery-range-report-addendum.json':'5073cd82f2f8666ef6735f47e03f32b5b7370f03039457f5f49fd7b484410512',
    'poincare-review/ir-signature-seal-addendum.json':'19ae055f2d60cc534e500b76041b97607f9d93e9f540ba3b98494485542db923',
    'poincare-review/warning-classification-addendum.json':'2a0225f80fec10e09f4d4271154c2ad82ffacbb100fce2404e2722bb5cb6392e',
    'poincare-review/three-origin-cases-addendum.json':'ffd466cd111c056ff595af20364b3a1a20a533a88984edb025134625b0051341',
    'cheeger-review/semantic-review.json':'12d2abbb0e6c1d98c15ef9c24cd9450e40cf890ad9a90f9e46616a9ee3a6b941',
    'range-review/semantic-review.json':'1f7fd139d999bf672e5105c4ece7594e97f51f06a33046afae07f247590133d6',
    'range-review/bkl-semantic-review.json':'44cfc36cc4104eee2903ece0f83e83b2d7c631ea3163f236fcc50ec1811da594',
    'generated-instance-review/semantic-review.json':'f7ec66e376f433215dcab60b7cb3a0c59d4c711fbe1c90118a64e13c1d4282ad',
    'report-song-semantic-addendum/final-semantic-review.json':'8080803e361720250f4a7b3f661625233fd400656a68a13f28d28a504c5de4cb',
}
for file,digest in review_pins.items():
    assert sha(D/file)==digest,file
    r=read(D/file)
    assert not r.get('findings',[]) and not r.get('substantive_findings',[]),file
    decision=r.get('status',r.get('decision',''))
    assert r.get('success') is True or decision.startswith(('PASS','ACCEPTED')),file
assert sha(D/'recover_registry.py')=='0c1755cc0cd9193952685c13e945c7b343722e5fc7360951e77da37fefe0d566'
scan=read(D/'final-source-scan.json')
assert scan['success'] and scan['mathematical_modules']==1710
assert all(not e['forbidden_tokens'] for e in scan['modules'])
for e in scan['modules']:
    assert sha(SRC/Path(*e['module'].split('.')).with_suffix('.lean'))==e['source_sha256']
qa=read(D/'report/pdf-qa.json')
assert qa['success'] and qa['pages']==4 and qa['all_fonts_embedded']
assert qa['compile_warnings']==qa['compile_errors']==qa['missing_glyphs']==0
assert qa['source_sha256']==sha(D/'report/KLS_Endpoint_Report.tex')=='c27bbb49f0c663c2f46c4abf88f1237650538dcd794824e26d20fe2f6019d8bb'
assert qa['pdf_sha256']==sha(D/'report/KLS_Endpoint_Report.pdf')=='b34d3d01eef5647e9e44a5d5ca687c21c95febe3c96b4a45b576713b11645f9f'
assert qa['all_four_pages_visually_reviewed_by']=='root' and not qa['visual_findings']
assert summary['upstream_model_source_sha256']==sha(SRC/'OAI/Analysis/KLS/Model.lean')=='28cddbf3c493afd43b3f7aba78f670952ea0c38909665c86bff883849e7f8dbc'

drafts=D/'publication-drafts'
archive=drafts/'reviewed-before-status'
assert not archive.exists()
archive.mkdir()
song=read(D/'report-song-semantic-addendum/final-semantic-review.json')
status_text={
    'github-brief.txt': 'Verification passed: 1,710 mathematical modules rebuilt from source at kernel trust level zero. The audit checked 22,017 declarations (19,686 theorems) and 3,658 exact name/origin/kind gates. Three separate agent reviews passed; complete sources, logs, receipts, and a four-page technical report accompany the release.',
    'zenodo-abstract.txt': 'A fresh source build verified 1,710 mathematical modules; exhaustive auditing covered 22,017 declarations. The archive includes the complete Lean source closure, a four-page technical report, and the verification records.',
    'endpoint-statement.txt': 'Verification passed: 1,710 freshly rebuilt mathematical modules, two fresh audit modules, 22,017 declarations (19,686 theorems), and 3,658 exact name/origin/kind gates. Three separate agent reviews passed. The accompanying verification receipt records the complete source, object, log, statement, and axiom checks.'}
finalization=[]
for name,status in status_text.items():
    p=drafts/name
    assert sha(p)==song['reviewed_artifact_sha256']['publication-drafts/'+name]
    old=p.read_text()
    assert len(re.findall(r'^\[VERIFICATION STATUS[^\n]*\]$',old,re.M))==1
    shutil.copyfile(p,archive/name)
    new=re.sub(r'^\[VERIFICATION STATUS[^\n]*\]$',status,old,flags=re.M)
    assert '[VERIFICATION STATUS' not in new
    p.write_text(new)
    finalization.append({'file':name,'reviewed_sha256':sha(archive/name),
                         'final_sha256':sha(p),'only_change':'Replace one explicit pending-verification marker by actual passed counts.'})
write(drafts/'status-finalization-receipt.json',{'success':True,'mathematical_text_unchanged':True,'files':finalization})
shutil.copyfile(D/'verification-summary.json',D/'verification-summary.provisional.json')
summary['review_status']='accepted'
summary['review_team']=['definition_audit','bkl_audit','song_zhang_audit']
summary['review_receipts_sha256']=review_pins
summary['final_source_scan_sha256']=sha(D/'final-source-scan.json')
summary['pdf_qa_sha256']=sha(D/'report/pdf-qa.json')
summary['root_closure_notes']=[
    'The original primary Lean audit succeeded; its Python registry assertion required the explicitly documented seven-case finite reconciliation.',
    'All eight import-origin overlaps, including the previously recorded hessian equation, have individually checked literal types, exact selected origins and unchanged standard axiom closures.',
    'The new wrapper required only an ordinary-comment syntax repair; its theorem statements and proof bodies were preserved.',
    'All 1710 mathematics sources, including the range extension, compiled freshly and passed the final forbidden-token scan.',
    'Previously accepted warnings exactly match their accepted logs; the three new public mathematics modules have no warnings.',
    'Earlier peer-review count forecasts are superseded by the successful final execution counts in this summary.',
    'The final four-page PDF was recompiled and visually checked after the report wording changes.'
]
write(D/'verification-summary.json',summary)
receipt={
    'success':True,'review_status':'accepted',
    'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'poincare_constant':500,'cheeger_coefficient':'197/100',
    'cheeger_two_corollary':True,'universal_poincare_range':['4','500'],
    'exact_openai_proposition':'OAI.LeanBlast.KLS.KLSStatement',
    'fresh_mathematical_modules':1710,'fresh_audit_modules':2,
    'checked_declarations':22017,'checked_theorems':19686,'strict_name_origin_kind_gates':3658,
    'kernel_trust_level':0,'endpoint_axioms':['propext','Classical.choice','Quot.sound'],
    'old_project_objects_imported':False,
    'verification_summary_sha256':sha(D/'verification-summary.json'),
    'build_completion_sha256':sha(D/'build-completion.json'),
    'registry_recovery_receipt_sha256':sha(D/'registry-comparison-recovery.json'),
    'final_source_scan_sha256':sha(D/'final-source-scan.json'),
    'pdf_qa_sha256':sha(D/'report/pdf-qa.json'),
    'report_source_sha256':qa['source_sha256'],'report_pdf_sha256':qa['pdf_sha256'],
    'publication_status_finalization_sha256':sha(drafts/'status-finalization-receipt.json'),
    'review_receipts_sha256':review_pins,'root_closure_runner_sha256':sha(D/'close_verification.py'),
    'scope':'Proof and report verification sealed. Portable packaging and its configuration/entry checks are recorded separately before delivery.'}
write(D/'final-verification-receipt.json',receipt)
print('PROOF_REPORT_AND_THREE_REVIEW_CLOSURE_ACCEPTED',sha(D/'final-verification-receipt.json'))
