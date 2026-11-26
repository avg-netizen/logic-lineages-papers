"""Artifact reuse regressions with a stub compiler; no mathematical axioms change."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest


class CheckedCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'scripts').mkdir()
        shutil.copyfile(Path(__file__).with_name('check.py'), self.root / 'scripts/check.py')
        (self.root / '.lake/packages').mkdir(parents=True)
        (self.root / 'locks').mkdir()
        (self.root / 'bin').mkdir()
        self.calls = self.root / 'calls'
        compiler = self.root / 'bin/lean'
        compiler.write_text(f'#!{sys.executable}\n' + '''
from pathlib import Path
import hashlib, os, sys
source = Path(sys.argv[-1])
target = Path(sys.argv[sys.argv.index('-o') + 1])
with Path(os.environ['CACHE_TEST_CALLS']).open('a') as log:
    log.write(source.stem + '\\n')
payload = hashlib.sha256(source.read_bytes()).hexdigest()
if source.stem == 'B':
    payload += (target.parent / 'A.olean').read_text()
for p in [target, Path(str(target)+'.private'), Path(str(target)+'.server'), target.with_suffix('.ir')]:
    p.write_text(payload)
if 'FAIL' in source.read_text():
    sys.exit(1)
print('checked fixture ' + source.stem)
''')
        compiler.chmod(0o755)
        (self.root / 'lean-toolchain').write_text('fixture-v1\n')
        (self.root / 'A.lean').write_text('def a : Nat := 1\n')
        (self.root / 'B.lean').write_text('import A\ndef b : Nat := a\n')
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'],
                        LEAN_CHECK_LOCK_DIR=str(self.root / 'locks'), CACHE_TEST_CALLS=str(self.calls))

    def tearDown(self):
        self.temp.cleanup()

    def run_check(self, *options, success=True):
        start = self.calls.read_text().splitlines() if self.calls.exists() else []
        result = subprocess.run([sys.executable, str(self.root / 'scripts/check.py'),
                                 '--timeout', '5', '--cpu-seconds', '5', '--min-free-mib', '0',
                                 *options, 'B'], cwd=self.root, env=self.env,
                                text=True, capture_output=True, timeout=15)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = self.calls.read_text().splitlines() if self.calls.exists() else []
        return calls[len(start):], result

    def object(self, module='A', suffix='.olean'):
        return self.root / '.lake/build/lib/lean' / (module + suffix)

    def warm(self):
        self.assertEqual(self.run_check()[0], ['A', 'B'])

    def test_unchanged_requested_gate_is_reused_with_original_native_evidence(self):
        self.warm()
        calls, result = self.run_check()
        self.assertEqual(calls, [])
        self.assertIn('CACHE_HIT B', result.stdout)
        receipt = json.loads((self.root / 'build-reports/latest.json').read_text())
        for row in receipt['modules']:
            self.assertEqual(row['status'], 'verified-cache-hit')
            self.assertEqual(row['returncode'], 0)
            self.assertTrue(Path(row['verified_from']).is_file())

    def test_source_only_touch_reuses_both_modules(self):
        self.warm()
        path = self.root / 'A.lean'
        future = self.object().stat().st_mtime_ns + 5_000_000_000
        os.utime(path, ns=(path.stat().st_atime_ns, future))
        self.assertEqual(self.run_check()[0], [])
        self.assertGreaterEqual(self.object().stat().st_mtime_ns, future)

    def test_changed_source_with_preserved_timestamp_rebuilds_dependents(self):
        self.warm()
        path = self.root / 'A.lean'
        old = path.stat()
        path.write_text('def a : Nat := 2\n')
        os.utime(path, ns=(old.st_atime_ns, old.st_mtime_ns))
        self.assertEqual(self.run_check()[0], ['A', 'B'])

    def test_changed_object_companion_is_rebuilt(self):
        self.warm()
        self.object(suffix='.ir').write_text('changed imported compiled code')
        self.assertEqual(self.run_check()[0], ['A'])

    def test_missing_object_companion_is_rebuilt(self):
        self.warm()
        self.object(suffix='.olean.private').unlink()
        self.assertEqual(self.run_check()[0], ['A'])

    def test_changed_compiler_invalidates_cached_modules(self):
        self.warm()
        with (self.root / 'bin/lean').open('a') as f:
            f.write('\n# compiler changed\n')
        self.assertEqual(self.run_check()[0], ['A', 'B'])

    def test_changed_toolchain_pin_invalidates_cached_modules(self):
        self.warm()
        (self.root / 'lean-toolchain').write_text('fixture-v2\n')
        self.assertEqual(self.run_check()[0], ['A', 'B'])

    def test_changed_original_log_is_not_a_cache_hit(self):
        self.warm()
        entry = json.loads(self.object(suffix='.checked.json').read_text())
        (self.root / entry['native_row']['log']).write_text('replaced proof log')
        self.assertEqual(self.run_check()[0], ['A'])

    def test_invalidated_original_receipt_is_not_a_cache_hit(self):
        self.warm()
        entry = json.loads(self.object(suffix='.checked.json').read_text())
        receipt = Path(entry['native_receipt'])
        data = json.loads(receipt.read_text())
        data['modules'][0]['returncode'] = 1
        receipt.write_text(json.dumps(data))
        # A is freshly checked against identical bytes; B's own successful
        # native row and exact imported object remain valid independently.
        self.assertEqual(self.run_check()[0], ['A'])

    def test_changed_native_resource_profile_is_not_a_cache_hit(self):
        self.warm()
        entry = json.loads(self.object(suffix='.checked.json').read_text())
        receipt = Path(entry['native_receipt'])
        data = json.loads(receipt.read_text())
        data['cpu_seconds'] = 999
        receipt.write_text(json.dumps(data))
        self.assertEqual(self.run_check()[0], ['A', 'B'])

    def test_corrupt_record_rebuilds(self):
        self.warm()
        self.object(suffix='.checked.json').write_text('{broken')
        self.assertEqual(self.run_check()[0], ['A'])

    def test_fresh_bypasses_all_cache_entries(self):
        self.warm()
        self.assertEqual(self.run_check('--fresh')[0], ['A', 'B'])

    def test_placeholder_scan_still_runs_before_reuse(self):
        self.warm()
        (self.root / 'B.lean').write_text('import A\ntheorem bad : False := by sorry\n')
        calls, result = self.run_check(success=False)
        self.assertEqual(calls, [])
        self.assertIn('Forbidden proof placeholder', result.stderr)

    def test_failed_compiler_cannot_leave_a_reusable_bundle(self):
        self.warm()
        (self.root / 'A.lean').write_text('def a : Nat := 1 -- FAIL\n')
        self.assertEqual(self.run_check(success=False)[0], ['A'])
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ir', '.checked.json']:
            self.assertFalse(self.object(suffix=suffix).exists())


if __name__ == '__main__':
    unittest.main()
