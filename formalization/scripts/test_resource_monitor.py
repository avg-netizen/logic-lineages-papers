"""Resource-monitor regressions; these tests do not launch Lean."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch, Mock

spec = importlib.util.spec_from_file_location('bounded_check', Path(__file__).with_name('check.py'))
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)

class ResourceMonitorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.proc = Path(self.temp.name)
    def tearDown(self):
        self.temp.cleanup()
    def process(self, pid, parent, rss, children=None):
        root = self.proc / str(pid); root.mkdir()
        (root / 'status').write_text(f'Name:\tfixture\nState:\tS (sleeping)\nPPid:\t{parent}\nVmRSS:\t{rss} kB\n')
        if children is not None:
            task = root / 'task' / str(pid); task.mkdir(parents=True)
            (task / 'children').write_text(' '.join(map(str, children)))
    def test_missing_children_retains_own_rss(self):
        self.process(10, 1, 800)
        self.assertEqual(check.resident_kib(10, self.proc), 800)
    def test_ppid_fallback_counts_descendants_not_siblings(self):
        self.process(10, 1, 800); self.process(11, 10, 400)
        self.process(12, 11, 200); self.process(13, 1, 999)
        self.assertEqual(check.resident_kib(10, self.proc), 1400)
    def test_normal_children_path(self):
        self.process(10, 1, 800, [11]); self.process(11, 10, 400, [])
        self.assertEqual(check.resident_kib(10, self.proc), 1200)
    def test_disappearing_process(self):
        self.process(10, 1, 800, [11])
        self.assertEqual(check.resident_kib(10, self.proc), 800)
        self.assertEqual(check.resident_kib(12, self.proc), 0)
    def test_malformed_live_status_fails_closed(self):
        self.process(10, 1, 800)
        (self.proc / '10/status').write_text('State:\tS (sleeping)\nPPid:\t1\n')
        with self.assertRaises(RuntimeError): check.resident_kib(10, self.proc)
    def test_permission_error_is_not_zero(self):
        with patch.object(Path, 'read_text', side_effect=PermissionError('blocked')):
            with self.assertRaises(PermissionError): check.resident_kib(10, self.proc)
    def test_zombie_is_not_live_memory(self):
        root = self.proc / '10'; root.mkdir()
        (root/'status').write_text('State:\tZ (zombie)\nPPid:\t1\n')
        self.assertEqual(check.resident_kib(10, self.proc), 0)
    def test_diagnostic_permission_failure_still_kills(self):
        process = Mock(pid=123)
        with patch.object(Path, 'glob', side_effect=PermissionError('no diagnostics')), \
             patch.object(check.os, 'killpg') as kill:
            self.assertEqual(check.stop_process_tree(process, self.proc), [])
            kill.assert_called_once_with(123, check.signal.SIGKILL)
            process.wait.assert_called_once()
    def test_unexpected_diagnostic_failure_still_kills(self):
        process = Mock(pid=123)
        with patch.object(Path, 'glob', side_effect=RuntimeError('unexpected')), \
             patch.object(check.os, 'killpg') as kill:
            with self.assertRaises(RuntimeError): check.stop_process_tree(process, self.proc)
            kill.assert_called_once_with(123, check.signal.SIGKILL)
            process.wait.assert_called_once()
    def test_already_exited_stop_reaps(self):
        process = Mock(pid=123)
        with patch.object(check.os, 'killpg', side_effect=ProcessLookupError):
            check.stop_process_tree(process, self.proc)
        process.wait.assert_called_once()
    def test_exit_race_is_not_a_live_observation_failure(self):
        process = Mock(pid=123); process.poll.return_value = 1
        with patch.object(check, 'resident_kib', side_effect=RuntimeError('teardown')):
            self.assertIsNone(check.sample_resident_kib(process))
    def test_live_observation_failure_is_not_ignored(self):
        process = Mock(pid=123); process.poll.return_value = None
        with patch.object(check, 'resident_kib', side_effect=RuntimeError('live failure')):
            with self.assertRaises(RuntimeError): check.sample_resident_kib(process)
    def test_statm_fallback_measures_resident_pages(self):
        self.process(10, 1, 800)
        (self.proc/'10/status').write_text('State:\tS (sleeping)\nPPid:\t1\n')
        (self.proc/'10/statm').write_text('1000 25 10 0 0 0 0\n')
        with patch.object(check.os, 'sysconf', return_value=4096):
            self.assertEqual(check.resident_kib(10, self.proc), 100)
    def test_statm_explicit_zero_is_a_measurement(self):
        self.process(10, 1, 800)
        (self.proc/'10/status').write_text('State:\tR (running)\nPPid:\t1\n')
        (self.proc/'10/statm').write_text('0 0 0 0 0 0 0\n')
        self.assertEqual(check.resident_kib(10, self.proc), 0)
    def test_statm_malformed_values_fail_closed(self):
        self.process(10, 1, 800)
        (self.proc/'10/status').write_text('State:\tS (sleeping)\nPPid:\t1\n')
        for value in ['0 -1', '0 no', '', '0']:
            with self.subTest(value=value):
                (self.proc/'10/statm').write_text(value)
                with self.assertRaises(RuntimeError): check.resident_kib(10, self.proc)
    def test_statm_invalid_page_size_fails_closed(self):
        self.process(10, 1, 800)
        (self.proc/'10/status').write_text('State:\tS (sleeping)\nPPid:\t1\n')
        (self.proc/'10/statm').write_text('100 20')
        with patch.object(check.os, 'sysconf', return_value=0):
            with self.assertRaises(RuntimeError): check.resident_kib(10, self.proc)
    def test_unexpected_snapshot_failure_still_kills(self):
        process = Mock(pid=123)
        with patch.object(Path, 'read_text', side_effect=RuntimeError('snapshot failure')), \
             patch.object(check.os, 'killpg') as kill:
            with self.assertRaises(RuntimeError):
                check.stop_process_tree(process, self.proc, memory_snapshot={})
            kill.assert_called_once_with(123, check.signal.SIGKILL)
            process.wait.assert_called_once()
    def test_snapshot_decode_failure_still_kills(self):
        process = Mock(pid=123); snapshot = {}
        with patch.object(Path, 'read_text', side_effect=UnicodeError('decode failure')), \
             patch.object(check.os, 'killpg') as kill:
            check.stop_process_tree(process, self.proc, memory_snapshot=snapshot)
            kill.assert_called_once_with(123, check.signal.SIGKILL)
            process.wait.assert_called_once()
            self.assertEqual(set(snapshot), {'status', 'statm'})
    def test_failed_outputs_removed_without_touching_neighbor(self):
        target = self.proc / 'Candidate.olean'
        artifacts = [target, Path(str(target)+'.private'), Path(str(target)+'.server'),
                     target.with_suffix('.ir'), target.with_suffix('.ilean')]
        neighbor = self.proc / 'Accepted.olean'; neighbor.write_text('accepted')
        for path in artifacts: path.write_text('failed compiler output')
        self.assertEqual(set(check.discard_failed_outputs(target)), set(artifacts))
        self.assertTrue(all(not p.exists() for p in artifacts))
        self.assertEqual(neighbor.read_text(), 'accepted')
        self.assertEqual(check.discard_failed_outputs(target), [])
    def test_failed_output_cleanup_permission_failure_is_not_hidden(self):
        with patch.object(Path, 'unlink', side_effect=PermissionError('cannot invalidate')):
            with self.assertRaises(PermissionError):
                check.discard_failed_outputs(self.proc / 'Candidate.olean')
    def test_real_sleep_reports_positive_memory(self):
        child = subprocess.Popen(['sleep', '2'])
        try:
            # Give exec a chance to expose its live memory.
            import time; time.sleep(0.05)
            self.assertGreater(check.resident_kib(child.pid), 0)
        finally:
            child.terminate(); child.wait()

if __name__ == '__main__': unittest.main()
