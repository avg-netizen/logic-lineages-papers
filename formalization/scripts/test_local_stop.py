"""Local cutoff boundary tests; never launch Lean or stop live workers."""
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('bounded_check_stop', Path(__file__).with_name('check.py'))
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class LocalStopTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / 'policy.json'
        self.cutoff = datetime(2026, 10, 30, 3, 0, tzinfo=timezone.utc)

    def policy(self, value):
        self.path.write_text(json.dumps(value))

    def test_fresh_clone_has_no_cutoff(self):
        self.assertIsNone(check.local_stop_reason(self.path, self.cutoff))

    def test_before_cutoff_is_released(self):
        self.policy({'stop_at_utc': '2026-10-30T03:00:00+00:00'})
        self.assertIsNone(check.local_stop_reason(self.path, self.cutoff.replace(hour=2, minute=59)))

    def test_exact_cutoff_and_later_stop(self):
        self.policy({'stop_at_utc': '2026-10-30T03:00:00Z'})
        self.assertIsNotNone(check.local_stop_reason(self.path, self.cutoff))
        self.assertIsNotNone(check.local_stop_reason(self.path, self.cutoff.replace(hour=4)))

    def test_explicit_pause_stops_before_time(self):
        self.policy({'paused': True, 'stop_at_utc': '2027-01-01T00:00:00Z'})
        self.assertIsNotNone(check.local_stop_reason(self.path, self.cutoff))

    def test_malformed_policy_fails_closed(self):
        for value in ([], {'stop_at_utc': 3}, {'stop_at_utc': '2026-10-30T03:00:00'}):
            self.policy(value)
            self.assertIsNotNone(check.local_stop_reason(self.path, self.cutoff))
        self.path.write_text('unfinished JSON')
        self.assertIsNotNone(check.local_stop_reason(self.path, self.cutoff))


if __name__ == '__main__':
    unittest.main()
