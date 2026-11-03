"""Cross-project lock regressions using real subprocesses and a stub compiler."""
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch


REPOSITORY = Path(__file__).resolve().parents[2]
RUNNERS = {
    'papers': REPOSITORY / 'formalization/scripts/check.py',
    'calculator': REPOSITORY / '04-pure-r1-calculator/scripts/check_lean.py',
}


def load_runner(name):
    spec = importlib.util.spec_from_file_location('lock_test_' + name, RUNNERS[name])
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class SharedLockTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.locks = self.root / 'locks'
        self.locks.mkdir()
        self.paths = {}
        for name, source in RUNNERS.items():
            destination = self.root / source.relative_to(REPOSITORY)
            destination.parent.mkdir(parents=True)
            shutil.copyfile(source, destination)
            self.paths[name] = destination
            project = (self.root / 'formalization' if name == 'papers' else
                       self.root / '04-pure-r1-calculator/lean')
            (project / '.lake/packages').mkdir(parents=True)
            (project / 'LockProbe.lean').write_text('def lockProbe : Nat := 0\n')
        compiler = self.root / 'bin/lean'
        compiler.parent.mkdir()
        compiler.write_text(f'#!{sys.executable}\n' + '''
import os
from pathlib import Path
import sys
import time

Path(os.environ['LEAN_LOCK_TEST_MARKER']).write_text('compiler started')
release = os.environ.get('LEAN_LOCK_TEST_RELEASE')
deadline = time.monotonic() + 10
while release and not Path(release).exists():
    if time.monotonic() >= deadline:
        sys.exit(99)
    time.sleep(0.01)
Path(sys.argv[sys.argv.index('-o') + 1]).write_text('test fixture')
''')
        compiler.chmod(0o755)
        self.env = os.environ.copy()
        self.env['PATH'] = str(compiler.parent) + os.pathsep + self.env.get('PATH', '')
        self.env['LEAN_CHECK_LOCK_DIR'] = str(self.locks)

    def tearDown(self):
        self.temp.cleanup()

    def command(self, name):
        module = 'LockProbe' if name == 'papers' else 'LockProbe.lean'
        return [sys.executable, str(self.paths[name]), module]

    def run_helper(self, name, env):
        return subprocess.run(self.command(name), env=env, text=True,
                              capture_output=True, timeout=10)

    def test_default_directory_stays_tmp(self):
        with patch.dict(os.environ, {}, clear=True):
            for name in RUNNERS:
                with self.subTest(name=name), patch.object(Path, 'is_dir', return_value=True):
                    self.assertEqual(load_runner(name).shared_lock_directory(), Path('/tmp'))

    def test_both_helpers_select_same_existing_directory(self):
        with patch.dict(os.environ, {'LEAN_CHECK_LOCK_DIR': str(self.locks)}):
            for name in RUNNERS:
                with self.subTest(name=name):
                    self.assertEqual(load_runner(name).shared_lock_directory(), self.locks)

    def test_invalid_directories_fail_closed_before_compiler(self):
        regular_file = self.root / 'regular-file'
        regular_file.touch()
        invalid = ['', '.', 'relative/locks', str(self.root / 'missing'), str(regular_file)]
        for name in RUNNERS:
            marker = self.root / (name + '-invalid-started')
            for directory in invalid:
                with self.subTest(name=name, directory=directory):
                    env = dict(self.env, LEAN_CHECK_LOCK_DIR=directory,
                               LEAN_LOCK_TEST_MARKER=str(marker))
                    result = self.run_helper(name, env)
                    self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                    self.assertIn('existing absolute directory', result.stderr)
                    self.assertFalse(marker.exists())
        self.assertFalse((self.root / 'missing').exists())
        self.assertEqual(list(self.locks.iterdir()), [])

    def test_calculator_lock_excludes_paper_compiler_and_releases(self):
        calculator_started = self.root / 'calculator-started'
        paper_started = self.root / 'paper-started'
        release = self.root / 'release-calculator'
        calculator_env = dict(self.env, LEAN_LOCK_TEST_MARKER=str(calculator_started),
                              LEAN_LOCK_TEST_RELEASE=str(release))
        paper_env = dict(self.env, LEAN_LOCK_TEST_MARKER=str(paper_started))
        calculator = subprocess.Popen(self.command('calculator'), env=calculator_env,
                                      text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            deadline = time.monotonic() + 5
            while not calculator_started.exists() and calculator.poll() is None:
                if time.monotonic() >= deadline:
                    self.fail('Calculator fixture did not acquire its lock in time')
                time.sleep(0.01)
            self.assertTrue(calculator_started.exists(), 'Calculator fixture exited early')
            blocked = self.run_helper('papers', paper_env)
            self.assertEqual(blocked.returncode, 75, blocked.stdout + blocked.stderr)
            self.assertIn('COMPILER_BUSY', blocked.stdout)
            self.assertFalse(paper_started.exists())
            self.assertEqual({path.name for path in self.locks.iterdir()},
                             {'logic-lineages-papers-lean.lock', 'pure-r1-calculator-lean.lock'})
            release.touch()
            output, errors = calculator.communicate(timeout=5)
            self.assertEqual(calculator.returncode, 0, output + errors)
            unblocked = self.run_helper('papers', paper_env)
            self.assertEqual(unblocked.returncode, 0, unblocked.stdout + unblocked.stderr)
            self.assertTrue(paper_started.exists())
        finally:
            if calculator.poll() is None:
                calculator.terminate()
            calculator.communicate(timeout=5)


if __name__ == '__main__':
    unittest.main()
