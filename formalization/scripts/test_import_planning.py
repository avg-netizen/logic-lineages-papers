"""Regression tests for both entry points on large or cyclic imports."""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import check
import mathlib_imports


class ImportPlanningTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.scripts = self.root / "scripts"
        self.scripts.mkdir()
        for script in ("check.py", "mathlib_imports.py"):
            shutil.copyfile(Path(__file__).with_name(script), self.scripts / script)
        package = self.root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib"
        package.mkdir(parents=True)
        (package / "Fixture.olean").write_text("stub upstream object")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.marker = self.root / "compiler-input"
        compiler = self.bin / "lean"
        compiler.write_text(f"#!{sys.executable}\n" + """from pathlib import Path
import os, sys
Path(os.environ['IMPORT_TEST_MARKER']).write_text(Path(sys.argv[-1]).stem)
sys.exit(7)
""")
        compiler.chmod(0o755)
        self.locks = self.root / "locks"
        self.locks.mkdir()
        self.env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ["PATH"],
                        LEAN_CHECK_LOCK_DIR=str(self.locks), IMPORT_TEST_MARKER=str(self.marker))

    def make_chain(self, end=1300, tail="import Mathlib.Fixture\n"):
        for n in range(end):
            (self.root / f"M{n}.lean").write_text(f"import M{n + 1}\n")
        (self.root / f"M{end}.lean").write_text(tail)
        return end

    def invoke(self, tool, *args):
        return subprocess.run([sys.executable, str(self.scripts / tool), *args],
                              cwd=self.root, env=self.env, text=True,
                              capture_output=True, timeout=15)

    def test_deep_chain(self):
        end = self.make_chain()
        with patch.object(check, "ROOT", self.root):
            plan, dependencies, upstream, roots = check.plan_sources(["M0"])
        self.assertEqual(plan, [f"M{n}" for n in reversed(range(end + 1))])
        self.assertEqual(dependencies["M0"], ["M1"])
        self.assertEqual(upstream[f"M{end}"], ["Mathlib.Fixture"])
        self.assertEqual(roots, {"Mathlib.Fixture"})
        acquire = self.invoke("mathlib_imports.py", "M0")
        self.assertEqual(acquire.returncode, 0, acquire.stderr)
        self.assertEqual(acquire.stdout, "Mathlib.Fixture\n")
        compile_first = self.invoke("check.py", "--min-free-mib", "0", "M0")
        # The stub fails immediately, proving the actual compiler entry point
        # got past the deep import walk and started at the deepest leaf.
        self.assertNotEqual(compile_first.returncode, 0, compile_first.stdout)
        self.assertIn(f"Compiling M{end}", compile_first.stdout)
        self.assertEqual(self.marker.read_text(), f"M{end}")

    def test_real_cycle_reports_module_not_recursion_error(self):
        self.make_chain(tail="import M570\n")
        for tool in ("check.py", "mathlib_imports.py"):
            with self.subTest(tool=tool):
                out = self.invoke(tool, "M0")
                self.assertNotEqual(out.returncode, 0)
                self.assertIn("Circular local import: M570", out.stderr)
                self.assertNotIn("RecursionError", out.stderr)
        self.assertFalse(self.marker.exists())

    def test_deep_placeholder_rejected_before_compilation(self):
        self.make_chain(tail="theorem bad : False := by sorry\n")
        out = self.invoke("check.py", "M0")
        self.assertNotEqual(out.returncode, 0)
        self.assertIn("Forbidden proof placeholder or axiom in M1300", out.stderr)
        self.assertFalse(self.marker.exists())

    def test_shared_dependencies_order_and_nested_comments(self):
        sources = {
            "TopA": "import First Shared Second\n",
            "TopB": "meta import Third Shared\n",
            "First": "public import Shared\n",
            "Second": "private import Shared\n",
            "Third": "import Second Mathlib.Zeta\n",
            "Shared": "/- import Missing /- sorry -/ -/\nimport Mathlib.Alpha -- unused\n",
        }
        for name, content in sources.items():
            (self.root / (name + ".lean")).write_text(content)
        with patch.object(check, "ROOT", self.root):
            order, deps, external, imports = check.plan_sources(["TopA", "TopB", "TopA"])
            found = mathlib_imports.collect_mathlib_imports(["TopA", "TopB"])
        self.assertEqual(order, ["Shared", "First", "Second", "TopA", "Third", "TopB"])
        self.assertEqual(deps["TopA"], ["First", "Shared", "Second"])
        self.assertEqual(external["Shared"], ["Mathlib.Alpha"])
        self.assertEqual(imports, {"Mathlib.Alpha", "Mathlib.Zeta"})
        self.assertEqual(found, ["Mathlib.Alpha", "Mathlib.Zeta"])

    def test_workflow_list_producer_is_fail_closed(self):
        workflow = (Path(__file__).resolve().parents[2] /
                    ".github/workflows/paper-components-lean.yml").read_text()
        producer = self.bin / "python3"
        producer.write_text("""#!/usr/bin/env bash
case "$IMPORT_PRODUCER_MODE" in
  fail) echo partial-result; exit 42 ;;
  empty) exit 0 ;;
  ok) printf 'first\nsecond\n' ;;
esac
""")
        producer.chmod(0o755)
        for filevar, array in (("module_list", "modules"), ("gate_list", "gates")):
            start = workflow.index(f"          {filevar}=")
            end = workflow.index("          fi\n", start) + len("          fi\n")
            fragment = "\n".join(line[10:] for line in workflow[start:end].splitlines())
            command = ("set -euo pipefail\n" + fragment +
                       f'\nprintf "%s\\n" "${{{array}[@]}}"\n')
            for mode, rc, stdout in (("ok", 0, "first\nsecond\n"),
                                     ("fail", 42, ""), ("empty", 1, "")):
                with self.subTest(filevar=filevar, mode=mode):
                    out = subprocess.run(["bash", "-c", command], cwd=self.root,
                        env=dict(self.env, IMPORT_PRODUCER_MODE=mode), text=True,
                        capture_output=True, timeout=15)
                    self.assertEqual(out.returncode, rc, out.stderr)
                    self.assertEqual(out.stdout, stdout)


if __name__ == "__main__":
    unittest.main()
