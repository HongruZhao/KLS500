"""Preserve the checked stage, create final local outputs, and verify the ZIP."""
from pathlib import Path
import datetime
import json
import shutil
import zipfile
from rebuild import D, B, PRIOR, ACCEPTED, sha, read, write

stage=D/'release-stage'
output=B/'outputs/kls-final-500-2'
assert stage.is_dir() and not output.exists()
assert read(D/'final-verification-receipt.json')['review_status']=='accepted'
configuration=read(D/'portable-configuration-check.json')
assert configuration['success'] and configuration['all_temporary_links_removed']
assert not (stage/'lean/.lake').exists()
assert len(list((stage/'lean').rglob('*.lean')))==1712
assert sha(stage/'KLS_Endpoint_Report.pdf')==read(D/'report/pdf-qa.json')['pdf_sha256']
for name in ['github-brief.md','zenodo-description.txt','endpoint-statement.txt','README.md']:
    assert '[VERIFICATION STATUS' not in (stage/name).read_text()
package_reviews={
    'definition-review/package-preparation-review.json':'d7a16b744c135be07819c7bcdb3b3a0789930bdb15b2dbcb1214f0eb8e68a6d2',
    'definition-review/package-two-audits-addendum.json':'9415b41010ea6e9e380d9dc4fc5160c189a6240de9d755e6c04cf4451ae57a99',
    'definition-review/package-evidence-completeness-addendum.json':'0f0ba41dc14c38355c23776c663c20e5ea45d3d4e0e423088c223edb04a08352'}
for file,digest in package_reviews.items():
    assert sha(D/file)==digest
    review=read(D/file)
    assert review['success'] and not review['findings']
assert sha(D/'stage_package.py')=='2e786c6bd26eda0273acbbf2091d2c487c7122cad499cdb37c1d552acaedb539'
staging=read(D/'staging-receipt.json')
staging['lake_config_status']='passed configuration and additional entry check; complete source rebuild recorded separately'
staging['portable_configuration_check_sha256']=sha(D/'portable-configuration-check.json')
write(D/'staging-receipt.json',staging)
shutil.copyfile(D/'staging-receipt.json',stage/'verification/staging-receipt.json')
provenance=stage/'verification/baseline-expectations'
provenance.mkdir()
for source,target in [
    (PRIOR/'expected-all-declarations.json','expected-all-declarations.json'),
    (PRIOR/'expected-canonical-gates.json','expected-canonical-gates.json'),
    (ACCEPTED/'accepted-baseline-receipt.json','accepted-baseline-receipt.json'),
    (ACCEPTED/'dependency-pins.json','dependency-pins.json'),
    (ACCEPTED/'receipt.json','accepted-final-input-receipt.json'),
    (ACCEPTED/'evidence-sha256.json','accepted-final-input-evidence-sha256.json')]:
    shutil.copyfile(source,provenance/target)
    assert sha(source)==sha(provenance/target)
shutil.copyfile(D/'deliver_package.py',stage/'verification/recorded-run-scripts/deliver_package.py')
publication_receipt={
    'success':True,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'report_pages':4,'mathematical_modules':1710,'audit_modules':2,
    'checked_declarations':22017,'checked_theorems':19686,'strict_gates':3658,
    'proof_verification_receipt_sha256':sha(D/'final-verification-receipt.json'),
    'pdf_qa_sha256':sha(D/'report/pdf-qa.json'),
    'portable_configuration_check_sha256':sha(D/'portable-configuration-check.json'),
    'staging_receipt_sha256':sha(D/'staging-receipt.json'),
    'package_reviews_sha256':package_reviews,
    'public_files_sha256':{name:sha(stage/name) for name in [
        'KLS_Endpoint_Report.pdf','KLS_Endpoint_Report.tex','github-brief.md',
        'zenodo-description.txt','endpoint-statement.txt','README.md']},
    'external_dependency_binaries_bundled':False,
    'temporary_build_links_bundled':False,
    'external_publication_performed':False,
    'initial_configuration_attempt_note':'The first invocation used the system Python without tomllib and exited before any package mutation. The successful configuration and entry check used the bundled modern Python; no source or proof change was needed.',
    'delivery_runner_sha256':sha(D/'deliver_package.py')}
write(D/'publication-package-receipt.json',publication_receipt)
shutil.copyfile(D/'publication-package-receipt.json',stage/'verification/publication-package-receipt.json')
assert not any(p.is_symlink() for p in stage.rglob('*'))
output.parent.mkdir(parents=True,exist_ok=True)
shutil.copytree(stage,output)
files={str(p.relative_to(output)):sha(p) for p in sorted(output.rglob('*')) if p.is_file()}
assert all(sha(stage/p)==v for p,v in files.items())
write(output/'release-inventory.json',{'success':True,'file_count':len(files),'files_sha256':files,
    'inventory_excludes_itself_and_SHA256SUMS':True})
sums={**files,'release-inventory.json':sha(output/'release-inventory.json')}
(output/'SHA256SUMS').write_text(''.join(digest+'  '+name+'\n' for name,digest in sorted(sums.items())))
all_files={str(p.relative_to(output)):sha(p) for p in sorted(output.rglob('*')) if p.is_file()}
archive=output.parent/'KLS_Final_500_197.zip'
assert not archive.exists()
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name in all_files:
        z.write(output/name,output.name+'/'+name)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    assert len(z.namelist())==len(all_files)
    import hashlib
    for name,digest in all_files.items():
        assert hashlib.sha256(z.read(output.name+'/'+name)).hexdigest()==digest,name
receipt={'success':True,'output_directory':str(output),'source_archive':str(archive),
    'archive_sha256':sha(archive),'archive_bytes':archive.stat().st_size,
    'archive_crc_and_all_member_hashes_verified':True,'file_count':len(all_files),
    'release_inventory_sha256':sha(output/'release-inventory.json'),
    'sha256sums_sha256':sha(output/'SHA256SUMS'),
    'publication_package_receipt_sha256':sha(output/'verification/publication-package-receipt.json'),
    'all_copied_files_equal_checked_stage':True}
write(D/'delivery-receipt.json',receipt)
write(output.parent/'KLS_Final_500_197.delivery.json',receipt)
print(json.dumps(receipt,indent=2),flush=True)
