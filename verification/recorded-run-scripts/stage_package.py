"""Prepare a portable source and report package after final verification."""
from pathlib import Path
import json
import shutil
from rebuild import D, B, BASE, SRC, sha, read, write, rel

receipt = read(D/'final-verification-receipt.json')
assert receipt['success'] and receipt['review_status']=='accepted'
summary = read(D/'verification-summary.json')
assert summary['success'] and summary['review_status']=='accepted'
assert receipt['verification_summary_sha256']==sha(D/'verification-summary.json')
assert receipt['root_closure_runner_sha256']==sha(D/'close_verification.py')
assert receipt['final_source_scan_sha256']==sha(D/'final-source-scan.json')
finalization=read(D/'publication-drafts/status-finalization-receipt.json')
assert receipt['publication_status_finalization_sha256']==sha(D/'publication-drafts/status-finalization-receipt.json')
assert finalization['success'] and finalization['mathematical_text_unchanged']
assert {e['file'] for e in finalization['files']}=={'github-brief.txt','zenodo-abstract.txt','endpoint-statement.txt'}
assert len(finalization['files'])==3
for e in finalization['files']:
    assert sha(D/'publication-drafts'/e['file'])==e['final_sha256']
    assert sha(D/'publication-drafts/reviewed-before-status'/e['file'])==e['reviewed_sha256']
qa = read(D/'report/pdf-qa.json')
assert qa['success'] and qa['pages']==4
assert receipt['pdf_qa_sha256']==sha(D/'report/pdf-qa.json')
assert qa['source_sha256']==sha(D/'report/KLS_Endpoint_Report.tex')
assert qa['pdf_sha256']==sha(D/'report/KLS_Endpoint_Report.pdf')
manifest = read(D/'effective-prepare-receipt.json')
assert manifest['source_modules']==1710
assert len(manifest['source_provenance'])==1710
completion=read(D/'build-completion.json')
assert completion['prepare_receipt_sha256']==sha(D/'effective-prepare-receipt.json')
assert summary['build_completion_sha256']==sha(D/'build-completion.json')
execution=read(D/'audit-execution.json')
assert summary['audit_execution_sha256']==sha(D/'audit-execution.json')
assert execution['source_sha256']==sha(SRC/'FinalKLS500Audit.lean')
companion=read(D/'generated-helper-execution.json')
assert summary['companion_execution_sha256']==sha(D/'generated-helper-execution.json')
assert companion['success'] and companion['exit_status']==0 and companion['fresh_object']
assert companion['source_sha256']==sha(SRC/'GeneratedProvenanceAudit.lean')
assert summary['fresh_math_modules']==1710 and summary['fresh_audit_modules']==2
assert summary['strict_name_origin_kind_gates']==3658
assert summary['selected_origin_reconciliation_sha256']==sha(D/'selected-origin-reconciliation.json')
assert summary['registry_recovery_receipt_sha256']==sha(D/'registry-comparison-recovery.json')
for name in ['github-brief.txt','zenodo-abstract.txt','endpoint-statement.txt']:
    assert '[VERIFICATION STATUS' not in (D/'publication-drafts'/name).read_text()
stage = D/'release-stage'
assert not stage.exists(), 'Preserve existing staged packages instead of overwriting them.'
stage.mkdir()
lean = stage/'lean'
lean.mkdir()
source_inventory = {}
for module,e in manifest['source_provenance'].items():
    source = SRC/rel(module).with_suffix('.lean')
    assert sha(source)==e['source_sha256']
    target = lean/rel(module).with_suffix('.lean')
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)
    assert sha(target)==e['source_sha256']
    source_inventory[str(target.relative_to(stage))]=sha(target)
audit_sources={'FinalKLS500Audit':execution,'GeneratedProvenanceAudit':companion}
for module,audit_receipt in audit_sources.items():
    target=lean/(module+'.lean')
    shutil.copyfile(SRC/(module+'.lean'),target)
    assert sha(target)==audit_receipt['source_sha256']
    source_inventory[str(target.relative_to(stage))]=sha(target)
assert len(source_inventory)==1712
for name in ['lean-toolchain','lake-manifest.json']:
    shutil.copyfile(SRC/name,lean/name)
modules = sorted(set(manifest['source_provenance'])|set(audit_sources))
assert len(modules)==1712
module_array = '[\n' + ',\n'.join('  '+json.dumps(m) for m in modules) + '\n]'
config = ('name = "KLSVerification"\nversion = "0.1.0"\n'
          'defaultTargets = ["KLSFinal"]\n'
          'moreLeanArgs = ["-j1", "-M12288", "-t0", "-DmaxSynthPendingDepth=3"]\n\n'
          '[[require]]\nname = "mathlib"\n'
          'git = "https://github.com/leanprover-community/mathlib4.git"\n'
          'rev = "4beb549110aa44b87d699166cece6e3642bddf34"\n\n'
          '[[lean_lib]]\nname = "KLSFinal"\nroots = ' + module_array
          + '\nglobs = ' + module_array + '\n')
(lean/'lakefile.toml').write_text(config)
for source in sorted((BASE/'lean').glob('*LICENSE*')):
    shutil.copyfile(source,lean/source.name)
shutil.copytree(BASE/'third_party',stage/'third_party')
shutil.copytree(D/'upstream-openai',stage/'third_party/openai-model')
for name in ['KLS_Endpoint_Report.tex','KLS_Endpoint_Report.pdf']:
    shutil.copyfile(D/'report'/name,stage/name)
assert sha(stage/'KLS_Endpoint_Report.tex')==qa['source_sha256']
assert sha(stage/'KLS_Endpoint_Report.pdf')==qa['pdf_sha256']
verification = stage/'verification'
verification.mkdir()
for name in ['final-verification-receipt.json','verification-summary.json',
             'verification-summary.provisional.json',
             'actual-endpoint-types.txt','all-declaration-axioms.json',
             'required-declarations.json','expected-prior-declarations.json',
             'effective-prepare-receipt.json','effective-build-receipt.json',
             'effective-post-build-input-check.json','post-audit-input-check.json',
             'build-completion.json','fresh-build-artifact-inventory.json',
             'audit-execution.json','generated-helper-execution.json','warning-review.json',
             'selected-origin-reconciliation.json','registry-comparison-recovery.json',
             'generated-unfolding-origin-overlap.json','wrapper-comment-repair.json',
             'initial-prepare-receipt.json','initial-build-receipt.json',
             'initial-wrapper-source.lean','prepare-receipt.json','build-receipt.json',
             'post-build-input-check.json','source-scan.json','final-source-scan.json',
             'artifact-suffix-repair.json']:
    shutil.copyfile(D/name,verification/name)
for directory in ['definition-review','poincare-review','cheeger-review','range-review',
                  'generated-instance-review','two-name-companion','report-song-semantic-addendum',
                  'publication-drafts']:
    shutil.copytree(D/directory,verification/directory,
                    ignore=shutil.ignore_patterns('__pycache__','.lake'))
shutil.copytree(D/'logs',verification/'logs')
shutil.copyfile(D/'report/pdf-qa.json',verification/'pdf-qa.json')
shutil.copyfile(D/'report/KLS_Endpoint_Report.log',verification/'latex-compile.log')
shutil.copytree(D/'report',verification/'report',
                ignore=shutil.ignore_patterns('__pycache__','.lake'))
recorded_scripts=verification/'recorded-run-scripts'
recorded_scripts.mkdir()
for source in sorted(D.glob('*.py')):
    shutil.copyfile(source,recorded_scripts/source.name)
for original,new in [('github-brief.txt','github-brief.md'),
                     ('zenodo-abstract.txt','zenodo-description.txt'),
                     ('endpoint-statement.txt','endpoint-statement.txt')]:
    text=(D/'publication-drafts'/original).read_text()
    assert '[VERIFICATION STATUS' not in text
    (stage/new).write_text(text)
    if original=='github-brief.txt':
        (stage/'README.md').write_text('# '+text.split('\n',1)[0]+'\n'+text.split('\n',1)[1]+
            '\n## Files and reproduction\n\n'
            'The four-page report is `KLS_Endpoint_Report.pdf`; its editable source is '
            '`KLS_Endpoint_Report.tex`. The exact endpoint statements are in '
            '`endpoint-statement.txt`. The short Zenodo description is '
            '`zenodo-description.txt`.\n\n'
            'The Lean entry is `lean/FinalKLSRange.lean`; '
            '`lean/FinalKLS500.lean` exposes the numerical bounds. '
            '`lean/FinalKLS500Audit.lean` checks the names, origins, declaration '
            'kinds, and axiom closures. `lean/GeneratedProvenanceAudit.lean` checks '
            'the seven individually documented selected-origin cases with exact '
            'types, origins, declaration kinds, and axiom sets. The source package '
            'contains all 1,710 mathematical modules needed by the entry, plus '
            'these two audit sources.\n\n'
            'With Elan and Lake installed, run the following from `lean/`:\n\n'
            '```sh\nlake exe cache get\nlake build KLSFinal\n```\n\n'
            'The recorded verification used a direct, dependency-ordered Lean '
            'rebuild with four compiler processes and kernel trust level zero; '
            'its complete receipts and logs are in `verification/`. The included '
            'Lake configuration covers exactly that mathematical closure and both audits. '
            'External dependencies are pinned in `lake-manifest.json`; their '
            'compiled cache is not bundled. Historical receipts retain paths from '
            'the recorded verification environment; the recorded-run scripts also '
            'refer to that environment. The portable reproduction path is the '
            'Lake command above. Independent reviewer artifacts are retained '
            'under verification and are outside the Lean import search path. '
            '`verification/report` preserves historical source and render snapshots; '
            'the final render paths are identified in `verification/pdf-qa.json`.\n\n'
            'Existing source notices and third-party licenses are preserved. '
            'No author, DOI, or additional release license is assigned by this package.\n')
write(stage/'verification/portable-source-inventory.json',source_inventory)
(stage/'.gitignore').write_text('lean/.lake/\n*.aux\n/KLS_Endpoint_Report.log\n*.out\n*.synctex.gz\n')
write(D/'staging-receipt.json',{
    'success':True,'stage':str(stage),'mathematical_modules':1710,
    'audit_modules':2,'portable_source_inventory_sha256':sha(verification/'portable-source-inventory.json'),
    'final_verification_receipt_sha256':sha(D/'final-verification-receipt.json'),
    'pdf_qa_sha256':sha(D/'report/pdf-qa.json'),
    'registry_recovery_receipt_sha256':sha(D/'registry-comparison-recovery.json'),
    'companion_execution_sha256':sha(D/'generated-helper-execution.json'),
    'stage_runner_sha256':sha(D/'stage_package.py'),
    'prior_stage_runner_sha256':sha(D/'stage_package.single-audit.py'),
    'lake_config_status':'prepared; separate configuration and entry check pending'})
print('SOURCE_AND_REPORT_STAGE_PREPARED',stage)
