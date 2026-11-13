#!/usr/bin/env python3
"""Synthetic non-Lean tests; no compiler, original files or Git invoked."""
import importlib.util, tempfile, unittest, json, gzip, os, sys, contextlib, io
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('candidate',HERE/'verify_evidence_bounded.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
class VerificationTests(unittest.TestCase):
 def fixture(self, mutation=None):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'build-reports').mkdir();(root/'scripts').mkdir();(root/'scripts/check.py').write_text('fixture')
   src=root/'A.lean';src.write_text('#audit_namespace A\n')
   obj=root/'build/A.olean';obj.parent.mkdir();art=[obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]
   for p in art:p.write_bytes(b'object')
   frozen=root/'frozen';frozen.write_text(v.sha(src)+'  A.lean\n')
   log=root/'build-reports/log';log.write_text('AXIOMS A.exact: [propext]\nAXIOM_AUDIT_PASS A: 1 theorems\n')
   row={'module':'A','source_sha256':v.sha(src),'returncode':0,'log':'build-reports/log'}
   for name,rc in [('001',0),('002',0),('003',1)]:
    (root/f'build-reports/{name}.json').write_text(json.dumps({**v.PROFILE,'modules':[{**row,'returncode':rc}]}))
   if mutation: mutation(root,src,log)
   old=(v.ROOT,v.REPO,v.HERE,v.checker.BUILD,v.checker.source_for,v.inherited_records,sys.argv)
   v.ROOT=v.REPO=v.HERE=root;v.checker.BUILD=obj.parent;v.checker.source_for=lambda m:src if m=='A' else None
   v.inherited_records=lambda *a:{'unexpected_changes':[]}
   sys.argv=['test','--gate','A','--alias','A.exact','--frozen-file',str(frozen)]
   try:
    with contextlib.redirect_stdout(io.StringIO()): code=v.main()
    run=next((root/'runs').iterdir());report=json.loads((run/'REPORT.json').read_text())
    with gzip.open(run/'SOURCE-AND-OBJECTS.json.gz','rt') as f:rows=json.load(f)
    with gzip.open(run/'ATTEMPTS.jsonl.gz','rt') as f:attempts=[json.loads(x) for x in f]
    with gzip.open(run/'FAILED-RECEIPTS.jsonl.gz','rt') as f:failures=[json.loads(x) for x in f]
    return code,report,rows,attempts,failures
   finally:v.ROOT,v.REPO,v.HERE,v.checker.BUILD,v.checker.source_for,v.inherited_records,sys.argv=old
 def test_latest_success_failure_preserved(self):
  code,r,rows,a,f=self.fixture();self.assertEqual(code,0);self.assertEqual(rows[0]['receipt'],'build-reports/002.json');self.assertEqual(len(a),3);self.assertEqual(len(f),1)
 def test_profile_rejected(self):
  def mutate(r,*_):
   p=r/'build-reports/002.json';d=json.loads(p.read_text());d['threads']=2;p.write_text(json.dumps(d))
  self.assertTrue(any('Wrong native profile' in e for e in self.fixture(mutate)[1]['errors']))
 def test_forbidden_axiom_rejected(self):
  self.assertTrue(any('Forbidden axioms' in e for e in self.fixture(lambda r,s,l:l.write_text('AXIOMS A.exact: [sorryAx]\nAXIOM_AUDIT_PASS A: 1 theorems\n'))[1]['errors']))
 def test_audit_and_alias_required(self):
  errors=self.fixture(lambda r,s,l:l.write_text(''))[1]['errors'];self.assertTrue(any('Missing namespace' in e for e in errors));self.assertTrue(any('Missing exact alias' in e for e in errors))
 def test_missing_object_rejected(self):
  self.assertTrue(any('Missing native outputs' in e for e in self.fixture(lambda r,*_:(r/'build/A.ir').unlink())[1]['errors']))
 def test_stale_object_rejected(self):
  self.assertTrue(any('Stale native' in e for e in self.fixture(lambda r,s,l:os.utime(r/'build/A.olean',ns=(1,1)))[1]['errors']))
 def test_unreadable_preserved_as_error(self):
  self.assertTrue(any('Unreadable receipt' in e for e in self.fixture(lambda r,*_:(r/'build-reports/004.json').write_text('{'))[1]['errors']))
 def test_placeholder_rejected(self):
  with self.assertRaisesRegex(ValueError,'Forbidden placeholder'): self.fixture(lambda r,s,l:s.write_text('theorem x := sorry'))
 def test_frozen_mismatch_rejected(self):
  self.assertTrue(any('Frozen specification mismatch' in e for e in self.fixture(lambda r,*_:(r/'frozen').write_text('0'*64+'  A.lean\n'))[1]['errors']))
 def test_source_race_rejected(self):
  original=v.jsonline
  def during_archive(out,value):
   original(out,value)
   if 'text' in value: (v.ROOT/'A.lean').write_text('#audit_namespace A\n-- race\n')
  v.jsonline=during_archive
  try:self.assertTrue(any('Source changed since receipt selection' in e for e in self.fixture()[1]['errors']))
  finally:v.jsonline=original
 def test_log_race_rejected(self):
  original=v.jsonline
  def during_archive(out,value):
   original(out,value)
   if 'text' in value: (v.ROOT/value['path']).write_text(value['text']+'changed\n')
  v.jsonline=during_archive
  try:self.assertTrue(any('Selected native log changed' in e for e in self.fixture()[1]['errors']))
  finally:v.jsonline=original
if __name__=='__main__':unittest.main()
