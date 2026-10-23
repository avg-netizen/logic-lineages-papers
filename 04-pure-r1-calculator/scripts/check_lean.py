#!/usr/bin/env python3
"""Compile selected Lean modules with bounded, serialized compiler processes.

Normal setup: install the pinned toolchain and dependencies with Lake. This
helper can also read an already populated .lake/packages directory; it never
updates or rebuilds dependencies. It writes only this project's build tree.
"""
from __future__ import annotations

import argparse
import fcntl
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+", help=".lean paths relative to lean/")
    parser.add_argument("--timeout", type=int, default=90)
    parser.add_argument("--memory-mib", type=int, default=2048)
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1] / "lean"
    build = project / ".lake/build/lib/lean"
    build.mkdir(parents=True, exist_ok=True)
    packages = project / ".lake/packages"
    if not packages.is_dir():
        parser.error("Missing Lake dependencies. Run lake update and lake exe cache get in lean/.")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    search = [build, project]
    search.extend(p / ".lake/build/lib/lean" for p in sorted(packages.iterdir()) if p.is_dir())
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in search)
    compiler = shutil.which("lean")
    if compiler is None:
        parser.error("Lean is unavailable; install the toolchain in lean/lean-toolchain.")

    def limits() -> None:
        # Lean maps compiled modules and reserves runtime arenas outside its
        # separately bounded managed heap. The virtual limit is not an RSS cap.
        resource.setrlimit(resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3))
        resource.setrlimit(resource.RLIMIT_CPU, (args.timeout, args.timeout + 2))

    with open("/tmp/pure-r1-calculator-lean.lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for name in args.modules:
            source = (project / name).resolve()
            if not source.is_relative_to(project.resolve()) or source.suffix != ".lean":
                parser.error(f"Not a local Lean module: {name}")
            if not source.is_file():
                parser.error(f"Lean module does not exist: {name}")
            target = build / source.relative_to(project.resolve()).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            command = [compiler, f"-M{args.memory_mib}", "-j1", "-o", str(target), str(source)]
            print(f"Compiling {name}", flush=True)
            try:
                result = subprocess.run(command, cwd=project, env=env, timeout=args.timeout,
                                        preexec_fn=limits, check=False)
            except subprocess.TimeoutExpired:
                print(f"TIMEOUT after {args.timeout}s: {name}", file=sys.stderr)
                return 124
            if result.returncode:
                return result.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
