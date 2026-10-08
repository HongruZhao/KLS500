"""Seal every fresh artifact only after the rebuild's final checks complete."""
from pathlib import Path
import datetime
from rebuild import D, SRC, LIB, LOGS, FLAGS, sha, read, write, verify_sources, check_accepted

prefix = 'effective-' if (D/'effective-build-receipt.json').exists() else ''
prepare_file = prefix+'prepare-receipt.json'
build_file = prefix+'build-receipt.json'
post_file = prefix+'post-build-input-check.json'
manifest = read(D / prepare_file)
receipt = read(D / build_file)
assert receipt['success'] and receipt['completed'] == manifest['source_modules']
assert not receipt['running'] and not receipt['unbuilt']
assert receipt['flags'] == FLAGS and not receipt['old_project_objects_imported']
# This file is emitted only after the scheduler, source recheck and accepted-input recheck.
post = read(D / post_file)
assert post['success'] and post == manifest['accepted_input_check']
verify_sources(manifest)
assert check_accepted() == post
assert prefix == 'effective-'
repair = read(D/'wrapper-comment-repair.json')
initial_prepare = read(D/'initial-prepare-receipt.json')
base_prepare = read(D/'prepare-receipt.json')
base_build = read(D/'build-receipt.json')
plan = read(D/'range-review/addon-plan.json')
assert repair['success'] and not repair['accepted_mathematical_sources_changed']
assert repair['initial_prepare_receipt_sha256'] == sha(D/'initial-prepare-receipt.json')
assert repair['initial_build_receipt_sha256'] == sha(D/'initial-build-receipt.json')
assert repair['initial_source_sha256'] == sha(D/'initial-wrapper-source.lean')
assert repair['initial_failure_log_sha256'] == sha(LOGS/'FinalKLS500.first-attempt.log')
assert repair['repaired_source_sha256'] == sha(SRC/'FinalKLS500.lean')
assert base_prepare['initial_prepare_receipt_sha256'] == sha(D/'initial-prepare-receipt.json')
assert base_build['initial_failed_attempt_receipt_sha256'] == sha(D/'initial-build-receipt.json')
assert base_build['prepare_receipt_sha256'] == sha(D/'prepare-receipt.json')
assert manifest['repaired_base_prepare_receipt_sha256'] == sha(D/'prepare-receipt.json')
assert receipt['base_build_receipt_sha256'] == sha(D/'build-receipt.json')
assert manifest['addon_plan_sha256'] == receipt['addon_plan_sha256'] == sha(D/'range-review/addon-plan.json')
assert plan['current_prepare_receipt_sha256'] == sha(D/'initial-prepare-receipt.json')
assert initial_prepare['source_modules'] == base_prepare['source_modules'] == 1699
assert base_build['success'] and base_build['completed'] == 1699
assert manifest['source_modules'] == receipt['completed'] == 1710
ancestry_files = ['finish_proofs.py','wrapper-comment-repair.json',
                 'initial-prepare-receipt.json','initial-build-receipt.json',
                 'initial-wrapper-source.lean','logs/FinalKLS500.first-attempt.log',
                 'prepare-receipt.json','build-receipt.json','post-build-input-check.json',
                 'range-review/addon-plan.json']
ancestry = {p:sha(D/p) for p in ancestry_files}
for e in receipt['results']:
    assert e['exit_status'] == 0 and e['fresh_object'] and e['errors'] == 0
    assert sha(e['log']) == e['log_sha256']
    for p, value in e['artifacts'].items():
        assert sha(LIB / p) == value
files = {str(p.relative_to(LIB)): sha(p) for p in sorted(LIB.rglob('*')) if p.is_file()}
assert sum(p.endswith('.olean') for p in files) == manifest['source_modules']
allowed_suffixes = ['.olean.private','.olean.server','.olean','.ir.sig','.ir']
for f in files:
    suffix = next((s for s in allowed_suffixes if f.endswith(s)), None)
    assert suffix is not None, f
    module = f[:-len(suffix)].replace('/','.')
    assert module in manifest['source_provenance'], (f,module)
write(D / 'fresh-build-artifact-inventory.json',files)
completion = {'success':True,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'all_scheduler_and_post_build_checks_complete':True,
              'prepare_receipt_file':prepare_file,'build_receipt_file':build_file,
              'post_build_input_check_file':post_file,
              'prepare_receipt_sha256':sha(D/prepare_file),
              'build_receipt_sha256':sha(D/build_file),
              'post_build_input_check_sha256':sha(D/post_file),
              'artifact_inventory_sha256':sha(D/'fresh-build-artifact-inventory.json'),
              'artifact_count':len(files),'fresh_math_modules':manifest['source_modules'],
              'artifact_suffix_counts':{s:sum(f.endswith(s) for f in files) for s in allowed_suffixes},
              'rebuild_runner_sha256':sha(D/'rebuild.py'),
              'repair_and_range_extension_ancestry_sha256':ancestry,
              'seal_runner_sha256':sha(Path(__file__))}
write(D/'build-completion.json',completion)
print(completion,flush=True)
