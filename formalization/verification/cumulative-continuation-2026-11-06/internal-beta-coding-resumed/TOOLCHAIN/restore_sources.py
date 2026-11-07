"""Restore exact source archives without invoking a compiler or modifying Git."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import datetime
import hashlib
import json
import shutil
import tarfile
import time
import urllib.request

BASE = Path('/workspace/scratch/95d226e72a26/toolchain')
ROOT = Path('/workspace/scratch/95d226e72a26/logic-lineages-papers/formalization')
PKG = BASE / 'packages'
ARCHIVES = BASE / 'source-archives'
PKG.mkdir(exist_ok=True)
ARCHIVES.mkdir(exist_ok=True)
manifest_path = ROOT / 'lake-manifest.json'
manifest = json.loads(manifest_path.read_text())

def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def restore(package):
    name, rev = package['name'], package['rev']
    owner_repo = package['url'].removeprefix('https://github.com/').removesuffix('.git')
    url = f'https://codeload.github.com/{owner_repo}/tar.gz/{rev}'
    archive = ARCHIVES / f'{name}-{rev}.tar.gz'
    temporary = archive.with_suffix(archive.suffix + '.part')
    if not archive.exists():
        for attempt in range(3):
            try:
                request = urllib.request.Request(url, headers={'User-Agent': 'logic-lineages-pinned-source-restore'})
                with urllib.request.urlopen(request, timeout=45) as response, temporary.open('wb') as target:
                    shutil.copyfileobj(response, target, 1024 * 1024)
                temporary.replace(archive)
                break
            except Exception:
                temporary.unlink(missing_ok=True)
                if attempt == 2:
                    raise
                time.sleep(1)
    destination = PKG / name
    if not destination.exists():
        unpack = BASE / f'unpack-{name}'
        unpack.mkdir(exist_ok=True)
        with tarfile.open(archive, 'r:gz') as tar:
            roots = {member.name.split('/')[0] for member in tar.getmembers()}
            if len(roots) != 1 or not next(iter(roots)).endswith('-' + rev):
                raise RuntimeError(f'Archive root does not name the pinned revision for {name}: {roots}')
            tar.extractall(unpack, filter='data')
        (unpack / next(iter(roots))).rename(destination)
        unpack.rmdir()
    result = {
        'name': name, 'source_url': package['url'], 'revision': rev,
        'archive_url': url, 'archive': str(archive),
        'archive_sha256': digest(archive), 'archive_bytes': archive.stat().st_size,
        'source_directory': str(destination),
    }
    print(f'Restored {name} at {rev}', flush=True)
    return result

packages = [package for package in manifest['packages'] if package['type'] == 'git']
results = []
with ThreadPoolExecutor(max_workers=4) as pool:
    futures = [pool.submit(restore, package) for package in packages]
    for future in as_completed(futures):
        results.append(future.result())

lake = ROOT / '.lake'
lake.mkdir(exist_ok=True)
runtime_link = lake / 'packages'
if runtime_link.exists() or runtime_link.is_symlink():
    if not runtime_link.is_symlink() or runtime_link.resolve() != PKG.resolve():
        raise RuntimeError(f'Existing runtime packages path is not the restoration link: {runtime_link}')
else:
    runtime_link.symlink_to(PKG, target_is_directory=True)

report = {
    'schema': 'pinned-source-archive-restoration-v1',
    'recorded_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'package_manifest': str(manifest_path), 'package_manifest_sha256': digest(manifest_path),
    'packages': sorted(results, key=lambda result: result['name']),
    'runtime_packages_link': str(runtime_link),
    'compiler_invocations': 0, 'upstream_builds': 0, 'tracked_files_modified': False,
}
(BASE / 'SOURCE-RESTORATION.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'Complete: {len(results)} source packages; no compiler invoked.', flush=True)
