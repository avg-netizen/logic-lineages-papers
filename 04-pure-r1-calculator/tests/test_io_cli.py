import base64
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
import zipfile

import r1calc as r
from r1calc import _build
from r1calc.jsonio import loads

ROOT = Path(__file__).resolve().parents[1]


class IOTests(unittest.TestCase):
    def test_json_roundtrips_and_schema(self):
        a = r.parse_ordinal("w^(w+1)*3+w^2+7")
        data = r.cnf_to_data(a)
        self.assertEqual(r.cnf_from_data(loads(json.dumps(data))), a)
        self.assertEqual(r.cnf_from_data({"schema": "r1calc.ordinal.v1", "cnf": data}), a)
        p = r.pure_r1_trace((r.OMEGA, r.parse_ordinal("w+1")), marked=1)
        self.assertEqual(r.pattern_from_data(loads(json.dumps(r.pattern_to_data(p)))), p)

    def test_json_rejects_malformed_or_ambiguous_input(self):
        for text in ('{"n":1,"n":2}', 'NaN', 'Infinity', '"x" trailing'):
            with self.assertRaises(ValueError):
                loads(text)
        for data in ([[[], 0]], [[[], True]], [[[], 1], [[], 1]],
                     {"schema": "r1calc.ordinal.v2", "cnf": []},
                     [[[], 1], [[[[], 1]], 1]]):
            with self.assertRaises(ValueError):
                r.cnf_from_data(data)
        for data in ({"n": True, "relations": [[]], "marked": None},
                     {"n": 2, "relations": [[[0, 1], [0, 1]]], "marked": None},
                     {"n": 2, "relations": [[[False, 1]]], "marked": None},
                     {"n": 2, "relations": [[]], "marked": 0, "extra": 1},
                     {"schema": "wrong", "n": 0, "relations": [[]], "marked": None}):
            with self.assertRaises(ValueError):
                r.pattern_from_data(data)
        with self.assertRaises(r.InputLimitError):
            r.cnf_from_data([[[[[], 1]], 1]], max_depth=1)
        with self.assertRaises(r.InputLimitError):
            r.pattern_from_data({"n": 3, "relations": [[]], "marked": None}, max_nodes=2)

    def run_cli(self, *args, input=None, cwd=ROOT, env=None):
        return subprocess.run([sys.executable, "-m", "r1calc", *args], cwd=cwd,
                              input=input, text=True, capture_output=True, timeout=10, env=env)

    def test_cli_arithmetic_json_and_stdin(self):
        p = self.run_cli("endpoint", "w^w", "--json")
        self.assertEqual(p.returncode, 0, p.stderr)
        data = json.loads(p.stdout)
        self.assertEqual(data["schema"], "r1calc.result.v1")
        self.assertTrue(data["complete"])
        self.assertEqual(data["result"]["text"], "w^(w) + w + 1")
        p = self.run_cli("add", "2", "w")
        self.assertEqual(p.stdout.strip(), "w")
        p = self.run_cli("endpoint", "@-", input="[[[[[],1]],1]]")
        self.assertEqual(p.returncode, 0, p.stdout)
        self.assertEqual(p.stdout.strip(), "w + 1")
        p = self.run_cli("resembles", "w", "w+2", "--json")
        self.assertEqual(p.returncode, 0)
        self.assertIs(json.loads(p.stdout)["result"], False)
        p = self.run_cli("mul-nat", "w+1", "3", "--json")
        self.assertEqual(json.loads(p.stdout)["multiplier"], 3)
        p = self.run_cli("endpoint", "__import__('os')", "--json")
        self.assertEqual(p.returncode, 2)
        self.assertFalse(json.loads(p.stdout)["complete"])

    def test_cli_finite_limits_and_inherited_trace(self):
        p = self.run_cli("trace", "w", "w+1", "--marked", "1")
        self.assertEqual(p.returncode, 0)
        result = json.loads(p.stdout)
        self.assertTrue(result["inherited"])
        self.assertEqual(result["pattern"]["relations"], [[[0, 1]]])
        p = self.run_cli("patterns", "3", "--limit", "1")
        self.assertEqual(p.returncode, 3)
        self.assertFalse(json.loads(p.stdout)["complete"])
        p = self.run_cli("patterns", "2", "--order", "1", "--limit", "10")
        self.assertEqual(p.returncode, 0)
        self.assertEqual(len(json.loads(p.stdout)["patterns"]), 2)
        self.assertEqual(json.loads(p.stdout)["order"], 1)
        with tempfile.TemporaryDirectory() as tmp:
            a, b = Path(tmp)/'a.json', Path(tmp)/'b.json'
            a.write_text(json.dumps(r.pattern_to_data(r.Pattern(2, (frozenset(),)))))
            b.write_text(json.dumps(r.pattern_to_data(r.Pattern(2, (frozenset({(0, 1)}),)))))
            p = self.run_cli("maps", str(a), str(b))
            self.assertIs(json.loads(p.stdout)["exists"], True)
            p = self.run_cli("maps", str(a), str(b), "--induced")
            self.assertIs(json.loads(p.stdout)["exists"], False)
            p = self.run_cli("maps", str(a), str(b), "--all", "--induced")
            self.assertIs(json.loads(p.stdout)["induced"], True)
            p = self.run_cli("maps", str(a), str(b), "--max-candidates", "0")
            self.assertEqual(p.returncode, 3)
            result = json.loads(p.stdout)
            self.assertFalse(result["complete"])
            self.assertIsNone(result["exists"])

    def test_stdlib_wheel_is_self_contained_and_records_match(self):
        with tempfile.TemporaryDirectory() as tmp:
            filename = _build.build_wheel(tmp)
            with zipfile.ZipFile(Path(tmp)/filename) as archive:
                rows = csv.reader(io.StringIO(archive.read(f'{_build.DIST}/RECORD').decode()))
                for name, digest, size in rows:
                    if digest:
                        data = archive.read(name)
                        expected = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b'=').decode()
                        self.assertEqual(digest, 'sha256='+expected)
                        self.assertEqual(int(size), len(data))
                package = Path(tmp)/'installed'
                archive.extractall(package)
            env = dict(os.environ, PYTHONPATH=str(package))
            p = self.run_cli("endpoint", "w^2", cwd=tmp, env=env)
            self.assertEqual(p.returncode, 0, p.stderr)
            self.assertEqual(p.stdout.strip(), "w^(2) + 2")
            self.assertTrue((package/'r1calc/ordinals.py').is_file())
            self.assertEqual(set(_build.get_requires_for_build_wheel()), set())

    def test_sdist_has_only_project_local_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            filename = _build.build_sdist(tmp)
            with tarfile.open(Path(tmp)/filename) as archive:
                names = archive.getnames()
                self.assertTrue(any(n.endswith('/pyproject.toml') for n in names))
                self.assertTrue(any(n.endswith('/USAGE.md') for n in names))
                self.assertFalse(any('/.lake/' in n or '__pycache__' in n or '..' in n.split('/') for n in names))


if __name__ == "__main__":
    unittest.main()
