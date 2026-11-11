#!/usr/bin/env python3
"""Compile local Lean modules with bounded, serialized workers and JSON receipts.

This helper never invokes Lake dependency updates or an upstream build. It
uses this package's dependencies when populated, or the included calculator's
same-pinned development cache. That cache path is not a source dependency.
Successful native modules retain checked artifacts keyed by source, imported
artifact bytes and the pinned compiler. --fresh bypasses this reuse.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CALCULATOR = ROOT.parent / "04-pure-r1-calculator/lean"
BUILD = ROOT / ".lake/build/lib/lean"
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", re.M)


def shared_lock_directory() -> Path:
    """Use the same existing absolute lock directory as the calculator runner."""
    directory = Path(os.environ.get("LEAN_CHECK_LOCK_DIR", "/tmp"))
    if not directory.is_absolute() or not directory.is_dir():
        raise ValueError("LEAN_CHECK_LOCK_DIR must name an existing absolute directory: "
                         + str(directory))
    return directory


def local_stop_reason(policy_path: Path | None = None, now: datetime | None = None) -> str | None:
    """Enforce this host's user-requested cutoff, without constraining clones.

    The optional control file is git-ignored. A malformed existing control
    fails closed; absence means the public package has no local time limit.
    """
    policy_path = ROOT / '.local-run-policy.json' if policy_path is None else policy_path
    try:
        policy = json.loads(policy_path.read_text())
    except FileNotFoundError:
        return None
    except (OSError, ValueError) as error:
        return f'Local stop policy unreadable: {error}'
    if not isinstance(policy, dict):
        return 'Local stop policy is not an object'
    if policy.get('paused') is True:
        return 'Local formalization is paused by user instruction'
    cutoff = policy.get('stop_at_utc')
    if cutoff is None:
        return None
    try:
        deadline = datetime.fromisoformat(cutoff.replace('Z', '+00:00'))
        if deadline.tzinfo is None:
            raise ValueError('deadline requires a timezone')
    except (AttributeError, TypeError, ValueError) as error:
        return f'Local stop deadline is malformed: {error}'
    if (datetime.now(timezone.utc) if now is None else now) >= deadline:
        return f'User-requested research cutoff reached ({deadline.isoformat()})'
    return None


def save_stop_receipt(requested: list[str], reason: str, rows: list[dict] | None = None) -> int:
    reports = ROOT / 'build-reports'
    reports.mkdir(exist_ok=True)
    path = reports / (str(time.time_ns()) + '-' + str(os.getpid()) + '.json')
    path.write_text(json.dumps({'requested': requested, 'outcome': 'scheduled-stop',
                               'reason': reason, 'modules': rows or []}, indent=2) + '\n')
    print('SCHEDULED_STOP: ' + reason, flush=True)
    print('BUILD_RECEIPT ' + str(path.relative_to(ROOT)), flush=True)
    return 78

def source_for(module: str) -> Path | None:
    if module == "R1Calculator" or module.startswith("R1Calculator."):
        path = CALCULATOR / (module.replace(".", "/") + ".lean")
    else:
        path = ROOT / (module.replace(".", "/") + ".lean")
    return path if path.is_file() else None

def resident_kib(pid: int, proc: Path = Path("/proc"), seen: set[int] | None = None) -> int:
    """Measure a process tree without losing own RSS when task/children is absent.

    Some procfs implementations expose status but not task/PID/children. Fall
    back to PPid discovery there. An unreadable/malformed live status is an
    observation failure, never an invented zero measurement.
    """
    seen = set() if seen is None else seen
    if pid in seen:
        return 0
    seen.add(pid)
    try:
        status = (proc / str(pid) / "status").read_text()
    except (FileNotFoundError, ProcessLookupError):
        return 0
    match = re.search(r"^VmRSS:\s+(\d+)\s+kB$", status, re.M)
    if match is None:
        if re.search(r"^State:\s+Z\b", status, re.M):
            return 0
        # During process setup/teardown some procfs implementations omit VmRSS
        # while statm still reports the actual resident-page count.
        try:
            fields = (proc / str(pid) / "statm").read_text().split()
            if len(fields) < 2 or not re.fullmatch(r"[0-9]+", fields[1]):
                raise ValueError("invalid resident-page count")
            page_bytes = os.sysconf("SC_PAGE_SIZE")
            if page_bytes <= 0:
                raise ValueError("invalid system page size")
            own = int(fields[1]) * page_bytes // 1024
        except (OSError, ValueError) as error:
            raise RuntimeError(f"Unavailable RSS for live process {pid}: {error}") from error
    else:
        own = int(match.group(1))
    try:
        children = [int(c) for c in
                    (proc / str(pid) / "task" / str(pid) / "children").read_text().split()]
    except (FileNotFoundError, ProcessLookupError):
        children = []
        for child in proc.iterdir():
            if not child.name.isdigit() or int(child.name) == pid:
                continue
            try:
                child_status = (child / "status").read_text()
            except (FileNotFoundError, ProcessLookupError):
                continue
            parent = re.search(r"^PPid:\s+(\d+)\s*$", child_status, re.M)
            if parent is None:
                raise RuntimeError(f"Missing PPid for process {child.name}")
            if int(parent.group(1)) == pid:
                children.append(int(child.name))
    return own + sum(resident_kib(child, proc, seen) for child in children)


def sample_resident_kib(process) -> int | None:
    """An already-exited child needs no live-memory observation."""
    try:
        return resident_kib(process.pid)
    except (OSError, ValueError, RuntimeError):
        if process.poll() is not None:
            return None
        raise


def stop_process_tree(process, proc: Path = Path("/proc"), memory_snapshot: dict | None = None) -> list[dict]:
    """Best-effort diagnostics must never prevent terminating a stopped job."""
    stopped = []
    try:
        if memory_snapshot is not None:
            for name in ("status", "statm"):
                try:
                    memory_snapshot[name] = (proc / str(process.pid) / name).read_text()[:16000]
                except (OSError, UnicodeError) as error:
                    memory_snapshot[name] = str(error)
        try:
            for task in (proc / str(process.pid) / "task").glob("*"):
                try:
                    stat = (task / "stat").read_text().rpartition(")")[2].split()
                    stopped.append({"tid": int(task.name), "state": stat[0],
                        "cpu_seconds": (int(stat[11]) + int(stat[12])) / os.sysconf("SC_CLK_TCK"),
                        "wait_channel": (task / "wchan").read_text().strip()})
                except (OSError, ValueError, IndexError):
                    pass
        except (OSError, ValueError, IndexError):
            pass
    finally:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        finally:
            process.wait()
    return stopped


def discard_failed_outputs(target: Path) -> list[Path]:
    """A failed compiler may emit objects; none may enter the incremental cache."""
    removed = []
    artifacts = [target, Path(str(target) + ".private"),
                 Path(str(target) + ".server"), target.with_suffix(".ir"),
                 target.with_suffix(".ilean"), target.with_suffix(".checked.json")]
    for artifact in artifacts:
        try:
            artifact.unlink()
            removed.append(artifact)
        except FileNotFoundError:
            pass
    return removed


_FILE_DIGESTS: dict[tuple, str] = {}
_RECEIPT_VALUES: dict[tuple, dict] = {}


def file_signature(path: Path) -> tuple:
    stat = path.stat()
    return (str(path), stat.st_dev, stat.st_ino, stat.st_size,
            stat.st_mtime_ns, stat.st_ctime_ns)


def file_digest(path: Path) -> str | None:
    try:
        signature = file_signature(path)
        if signature not in _FILE_DIGESTS:
            digest = hashlib.sha256()
            with path.open('rb') as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    digest.update(block)
            if signature != file_signature(path):
                raise RuntimeError('File changed while hashing: ' + str(path))
            _FILE_DIGESTS[signature] = digest.hexdigest()
        return _FILE_DIGESTS[signature]
    except FileNotFoundError:
        return None


def object_bundle(target: Path) -> dict[str, str | None]:
    """Include every loadable companion, so a partial/replaced bundle misses."""
    return {str(p): file_digest(p) for p in
            [target, Path(str(target) + '.private'), Path(str(target) + '.server'),
             target.with_suffix('.ir')]}


def checked_input_key(source: Path, dependencies: list[Path], context: dict) -> str:
    value = {'source_sha256': file_digest(source), 'context': context,
             'dependencies': {str(p): object_bundle(p) for p in dependencies}}
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def save_checked_cache(target: Path, key: str, row: dict, receipt: Path,
                       profile: dict) -> None:
    """Record a successful native row, never just the presence of an object."""
    if row.get('returncode') != 0 or not target.is_file():
        return
    log = ROOT / row['log']
    entry = {'schema': 1, 'input_key': key, 'outputs': object_bundle(target),
             'native_row': row, 'native_receipt': str(receipt),
             'native_profile': profile, 'log_sha256': file_digest(log)}
    path = target.with_suffix('.checked.json')
    temporary = path.with_name(path.name + f'.{os.getpid()}.tmp')
    temporary.write_text(json.dumps(entry, sort_keys=True) + '\n')
    temporary.replace(path)


def checked_cache_hit(target: Path, key: str, profile: dict) -> dict | None:
    """Reuse only the same inputs, exact native outputs and original proof log."""
    try:
        entry = json.loads(target.with_suffix('.checked.json').read_text())
        row = entry['native_row']
        if (entry['schema'] != 1 or entry['input_key'] != key or
                entry['native_profile'] != profile or row.get('returncode') != 0 or
                not target.is_file() or entry['outputs'] != object_bundle(target) or
                entry['log_sha256'] is None or
                entry['log_sha256'] != file_digest(ROOT / row['log'])):
            return None
        receipt_path = Path(entry['native_receipt'])
        signature = file_signature(receipt_path)
        if signature not in _RECEIPT_VALUES:
            _RECEIPT_VALUES[signature] = json.loads(receipt_path.read_text())
        receipt = _RECEIPT_VALUES[signature]
        if any(receipt.get(k) != v for k, v in profile.items()):
            return None
        if row not in receipt.get('modules', []):
            return None
        return {**row, 'status': 'verified-cache-hit',
                'verified_from': entry['native_receipt']}
    except (OSError, ValueError, KeyError, TypeError):
        return None


def checked_compiler_context(compiler: str, env: dict, external: set[str]) -> dict:
    """Bind cache entries to the compiler, pinned packages and imported objects."""
    executable = Path(compiler).resolve()
    context = {'compiler': str(executable), 'compiler_sha256': file_digest(executable),
               'lean_path': env['LEAN_PATH'], 'pins': {}, 'external_objects': {}}
    search = [Path(p) for p in env['LEAN_PATH'].split(os.pathsep)]
    # Elan is a selector: fingerprint the selected compiler as well as its shim.
    # Script-based test compilers need no probe and are never run unbounded here.
    with executable.open('rb') as binary:
        is_elf = binary.read(4) == b'\x7fELF'
    if is_elf:
        probe = subprocess.run([compiler, '--print-prefix'], cwd=ROOT, env=env,
                               capture_output=True, text=True, timeout=5)
        if probe.returncode:
            raise RuntimeError('Cannot identify selected Lean compiler for cache')
        prefix = Path(probe.stdout.strip())
        if not prefix.is_absolute():
            raise RuntimeError('Selected Lean compiler prefix is not absolute')
        context['selected_compiler'] = file_digest(prefix / 'bin/lean')
        search.append(prefix / 'lib/lean')
    for root in (ROOT, CALCULATOR):
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean'):
            path = root / name
            context['pins'][str(path)] = file_digest(path)
    for module in sorted(external):
        relative = Path(module.replace('.', '/') + '.olean')
        path = next((p / relative for p in search if (p / relative).is_file()), None)
        if path is None:
            raise RuntimeError('Cannot identify external cached import: ' + module)
        context['external_objects'][module] = object_bundle(path)
    return context


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--timeout", type=int, default=180,
                        help="wall seconds, including filesystem import waits")
    parser.add_argument("--cpu-seconds", type=int, default=90)
    parser.add_argument("--memory-mib", type=int, default=1536)
    parser.add_argument("--rss-mib", type=int, default=1024)
    parser.add_argument("--min-free-mib", type=int, default=None)
    parser.add_argument("--threads", type=int, choices=[1, 2], default=1)
    parser.add_argument("--core-profile", action="store_true",
                        help="verified Init/Lean/Std-only imports: 768 MiB free floor and tighter 512 MiB RSS cap")
    parser.add_argument("--fresh", action="store_true",
                        help="compile every local dependency, including calculator source")
    args = parser.parse_args()
    if reason := local_stop_reason():
        return save_stop_receipt(args.modules, reason)
    try:
        lock_directory = shared_lock_directory()
    except (OSError, ValueError) as error:
        parser.error(str(error))
    compiler = shutil.which("lean")
    if compiler is None:
        parser.error("Install the pinned Lean toolchain before compiling.")
    own_packages = ROOT / ".lake/packages"
    packages = own_packages if own_packages.is_dir() else CALCULATOR / ".lake/packages"
    if not packages.is_dir():
        parser.error("Pinned Mathlib cache absent. Acquire dependencies separately with Lake.")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = str(args.threads)
    search = [BUILD, ROOT]
    if not args.fresh:
        search.append(CALCULATOR / ".lake/build/lib/lean")
    search.extend(p / ".lake/build/lib/lean" for p in sorted(packages.iterdir()) if p.is_dir())
    env["LEAN_PATH"] = os.pathsep.join(str(p.resolve()) for p in search)
    requested = []
    for item in args.modules:
        if item.endswith(".lean"):
            path = Path(item)
            if not path.is_absolute():
                path = ROOT / path
            path = path.resolve()
            if not path.is_relative_to(ROOT):
                parser.error("Only local source files may be requested.")
            module = str(path.relative_to(ROOT).with_suffix("")).replace(os.sep, ".")
        else:
            module = item
        if source_for(module) is None:
            parser.error("Source not found: " + module)
        requested.append(module)
    order, visiting, visited, dependencies = [], set(), set(), {}
    external_dependencies = {}
    external_imports = set()
    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError("Circular local import: " + module)
        path = source_for(module)
        if path is None:
            return
        visiting.add(module)
        text = path.read_text()
        # Scan declarations after removing nested block and line comments.
        code, i, depth = [], 0, 0
        while i < len(text):
            if text.startswith('/-', i):
                depth += 1; code.append('  '); i += 2
            elif depth and text.startswith('-/', i):
                depth -= 1; code.append('  '); i += 2
            elif not depth and text.startswith('--', i):
                end = text.find('\n', i)
                if end < 0: break
                code.append('\n'); i = end + 1
            else:
                code.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
        clean = ''.join(code)
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b", clean, re.M):
            raise RuntimeError("Forbidden proof placeholder or axiom in " + module)
        dependencies[module] = []
        external_dependencies[module] = []
        for line in IMPORT.findall(clean):
            for dependency in line.split():
                if source_for(dependency) is not None:
                    dependencies[module].append(dependency)
                    visit(dependency)
                else:
                    external_imports.add(dependency)
                    external_dependencies[module].append(dependency)
        visiting.remove(module); visited.add(module); order.append(module)
    for module in requested:
        visit(module)
    if args.core_profile:
        allowed_prefixes = ('Init', 'Lean', 'Std')
        forbidden = sorted(d for d in external_imports
                           if not any(d == p or d.startswith(p + '.') for p in allowed_prefixes))
        if forbidden or any(m.startswith('R1Calculator') for m in order):
            parser.error('Core profile requires an Init/Lean/Std-only import closure; found: '
                         + ', '.join(forbidden or ['R1Calculator']))
        args.rss_mib = min(args.rss_mib, 512)
        args.min_free_mib = max(768, args.min_free_mib or 0, args.rss_mib + 256)
    elif args.min_free_mib is None:
        args.min_free_mib = 1024
    locks=[]
    try:
        for name in ["logic-lineages-papers-lean.lock", "pure-r1-calculator-lean.lock"]:
            lock=open(lock_directory / name,"a")
            try:
                fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                print("COMPILER_BUSY: another serialized Lean job owns the lock.")
                lock.close()
                return 75
            locks.append(lock)
        BUILD.mkdir(parents=True,exist_ok=True)
        reports=ROOT/"build-reports"
        reports.mkdir(exist_ok=True)
        receipt_path=reports/(str(time.time_ns())+'-'+str(os.getpid())+'.json')
        rows=[]
        profile = {'heap_cap_mib':args.memory_mib, 'rss_cap_mib':args.rss_mib,
                   'wall_seconds':args.timeout, 'cpu_seconds':args.cpu_seconds,
                   'minimum_free_mib':args.min_free_mib, 'core_only_profile':args.core_profile,
                   'single_thread':args.threads==1, 'threads':args.threads,
                   'upstream_cache_only':True}
        cache_context = checked_compiler_context(compiler, env, external_imports)
        def limits():
            resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,16*1024**3))
            resource.setrlimit(resource.RLIMIT_CPU,(args.cpu_seconds,args.cpu_seconds+2))
        for module in order:
            if reason := local_stop_reason():
                return save_stop_receipt(requested, reason, rows)
            path=source_for(module)
            target=BUILD/(module.replace('.', '/')+'.olean')
            borrowed=CALCULATOR/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean')
            if not args.fresh and module.startswith('R1Calculator') and borrowed.is_file():
                rows.append({'module':module,'status':'existing-calculator-object','source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
                continue
            dep_objects = []
            for dependency in dependencies[module]:
                dep_object = BUILD/(dependency.replace('.', '/')+'.olean')
                if not dep_object.is_file() and dependency.startswith('R1Calculator'):
                    dep_object = CALCULATOR/'.lake/build/lib/lean'/(dependency.replace('.', '/')+'.olean')
                dep_objects.append(dep_object)
            module_context = {**cache_context, 'external_objects':
                              {d: cache_context['external_objects'][d]
                               for d in external_dependencies[module]}}
            key = checked_input_key(path, dep_objects, module_context)
            cached = None if args.fresh else checked_cache_hit(target, key, profile)
            if cached is not None:
                rows.append(cached)
                # Keep legacy timestamp-based consumers compatible after a
                # source-only touch; hashes above established the exact bytes.
                newest_input = max(p.stat().st_mtime_ns for p in [path, *dep_objects])
                if newest_input > target.stat().st_mtime_ns:
                    os.utime(target, ns=(target.stat().st_atime_ns,
                                        max(time.time_ns(), newest_input)))
                print('CACHE_HIT '+module, flush=True)
                continue
            if (not args.fresh and module not in requested and target.is_file()
                    and not target.with_suffix('.checked.json').exists()):
                local_inputs = [path, *dep_objects]
                if all(p.is_file() and target.stat().st_mtime_ns >= p.stat().st_mtime_ns
                       for p in local_inputs):
                    continue
            available=int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text()).group(1))//1024
            if available<args.min_free_mib:
                print(f'MEMORY_GATE: {available} MiB available; require {args.min_free_mib}. No compiler launched.')
                receipt={'requested':requested, 'outcome':'memory-gate',
                         'available_mib':available, 'minimum_free_mib':args.min_free_mib,
                         'modules':rows}
                (reports/'latest.json').write_text(json.dumps(receipt,indent=2)+'\n')
                receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
                print('BUILD_RECEIPT '+str(receipt_path.relative_to(ROOT)),flush=True)
                return 76
            target.parent.mkdir(parents=True,exist_ok=True)
            command=[compiler,f'-M{args.memory_mib}',f'-j{args.threads}','-o',str(target),str(path)]
            started=time.monotonic()
            print('Compiling '+module,flush=True)
            log=reports/(receipt_path.stem+'-'+module.replace('.','-')+'.log')
            peak_rss=0
            cpu_seconds=0.0
            wait_channel='unknown'
            stopped_threads=[]
            memory_observation_failure={}
            with log.open('w') as stream:
                p=subprocess.Popen(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
                reason=None
                while p.poll() is None:
                    if deadline_reason := local_stop_reason():
                        reason = 'scheduled-stop: ' + deadline_reason
                        break
                    try:
                        sampled_rss = sample_resident_kib(p)
                        if sampled_rss is None:
                            break
                        peak_rss=max(peak_rss,sampled_rss)
                    except (OSError, ValueError, RuntimeError) as error:
                        reason=f'resident-memory observation failed: {error}'
                        break
                    try:
                        stat=Path(f'/proc/{p.pid}/stat').read_text().rpartition(')')[2].split()
                        cpu_seconds=(int(stat[11])+int(stat[12]))/os.sysconf('SC_CLK_TCK')
                        wait_channel=Path(f'/proc/{p.pid}/wchan').read_text().strip()
                    except (FileNotFoundError,ProcessLookupError):pass
                    free=int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text()).group(1))//1024
                    if time.monotonic()-started>args.timeout:
                        reason='wall-time limit'; break
                    if peak_rss>args.rss_mib*1024 or free<256:
                        reason='resident-memory safety limit'; break
                    time.sleep(0.05)
                if reason:
                    # A waiting main thread does not distinguish I/O from a
                    # stalled worker pool. Preserve all worker states before
                    # terminating a bounded resource failure.
                    stopped_threads = stop_process_tree(p, memory_snapshot=memory_observation_failure)
                    status=124 if reason=='wall-time limit' else 77
                    stream.write('\nRESOURCE_STOP: '+reason+'\n')
                else:
                    status=p.returncode
            output=log.read_text(errors='replace')
            if not status and checked_input_key(path, dep_objects, module_context) != key:
                status = 79
                output += '\nINPUT_CHANGED: source or imported objects changed during compilation.\n'
                log.write_text(output)
            discarded = discard_failed_outputs(target) if status else []
            row={'module':module,'returncode':status,'seconds':round(time.monotonic()-started,3),'observed_cpu_seconds':cpu_seconds,'last_wait_channel':wait_channel,'stopped_threads':stopped_threads,'peak_process_tree_rss_kib':peak_rss,'memory_observation_failure':memory_observation_failure,'discarded_failed_outputs':[str(p.relative_to(ROOT)) for p in discarded],'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'log':str(log.relative_to(ROOT))}
            rows.append(row)
            receipt={'requested':requested,'heap_cap_mib':args.memory_mib,'rss_cap_mib':args.rss_mib,'wall_seconds':args.timeout,'cpu_seconds':args.cpu_seconds,'minimum_free_mib':args.min_free_mib,'core_only_profile':args.core_profile,'single_thread':args.threads==1,'threads':args.threads,'upstream_cache_only':True,'calculator_objects_borrowed':not args.fresh,'modules':rows}
            if reason and reason.startswith('scheduled-stop:'):
                receipt.update(outcome='scheduled-stop', reason=reason)
            (reports/'latest.json').write_text(json.dumps(receipt,indent=2)+'\n')
            receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
            if output:
                print(output[-16000:],end='' if output.endswith('\n') else '\n')
            if status:
                print(f'COMPILE_FAILED {module}: {status}',flush=True)
                print('BUILD_RECEIPT '+str(receipt_path.relative_to(ROOT)),flush=True)
                return status if status>0 else 1
            save_checked_cache(target, key, row, receipt_path, profile)
            print('COMPILE_PASS '+module,flush=True)
        receipt = {'requested':requested, **profile,
                   'calculator_objects_borrowed':not args.fresh, 'modules':rows}
        (reports/'latest.json').write_text(json.dumps(receipt,indent=2)+'\n')
        receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
        print('BUILD_RECEIPT '+str(receipt_path.relative_to(ROOT)),flush=True)
        return 0
    finally:
        for lock in reversed(locks):lock.close()

if __name__=='__main__':
    raise SystemExit(main())
