"""Small standard-library-only PEP517 wheel/sdist backend.

No dependency downloads, generated proofs or files outside this project are
needed to install the Python calculator. Shared paper/Lean builds are separate.
"""
import base64
import csv
import hashlib
import io
from pathlib import Path
import tarfile
import zipfile

from . import __version__

NAME = "pure_r1_calculator"
DIST = f"{NAME}-{__version__}.dist-info"
ROOT = Path(__file__).resolve().parent.parent


def _metadata():
    return ("Metadata-Version: 2.1\nName: pure-r1-calculator\n"
            f"Version: {__version__}\n"
            "Summary: Hereditary CNF endpoint arithmetic and finite respecting patterns\n"
            "Requires-Python: >=3.10\n\n").encode()


def _dist_files():
    files = {f"{DIST}/METADATA": _metadata(),
            f"{DIST}/WHEEL": ("Wheel-Version: 1.0\nGenerator: r1calc\n"
                                "Root-Is-Purelib: true\nTag: py3-none-any\n").encode(),
            f"{DIST}/entry_points.txt": b"[console_scripts]\nr1calc = r1calc.cli:main\n"}
    if (ROOT/'USAGE.md').is_file():
        files[f"{DIST}/USAGE.md"] = (ROOT/'USAGE.md').read_bytes()
    return files


def get_requires_for_build_wheel(config_settings=None):
    return []


def get_requires_for_build_sdist(config_settings=None):
    return []


def prepare_metadata_for_build_wheel(metadata_directory, config_settings=None):
    for name, data in _dist_files().items():
        path = Path(metadata_directory)/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return DIST


def build_wheel(wheel_directory, config_settings=None, metadata_directory=None):
    files = {str(p.relative_to(ROOT)): p.read_bytes()
             for p in sorted((ROOT/'r1calc').glob('*.py'))}
    files.update(_dist_files())
    record = io.StringIO(newline="")
    writer = csv.writer(record, lineterminator="\n")
    for name, data in files.items():
        digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b"=").decode()
        writer.writerow((name, "sha256="+digest, len(data)))
    writer.writerow((f"{DIST}/RECORD", "", ""))
    files[f"{DIST}/RECORD"] = record.getvalue().encode()
    filename = f"{NAME}-{__version__}-py3-none-any.whl"
    Path(wheel_directory).mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(Path(wheel_directory)/filename, 'w', zipfile.ZIP_DEFLATED) as archive:
        for name, data in files.items():
            archive.writestr(name, data)
    return filename


def build_sdist(sdist_directory, config_settings=None):
    stem = f"{NAME}-{__version__}"
    filename = stem+".tar.gz"
    paths = [ROOT/'pyproject.toml', ROOT/'USAGE.md']
    paths += sorted((ROOT/'r1calc').glob('*.py'))
    paths += sorted((ROOT/'tests').glob('*.py'))
    paths += [p for p in (ROOT/'README.md', ROOT/'LICENSE') if p.is_file()]
    Path(sdist_directory).mkdir(parents=True, exist_ok=True)
    with tarfile.open(Path(sdist_directory)/filename, 'w:gz') as archive:
        for path in paths:
            archive.add(path, arcname=f"{stem}/{path.relative_to(ROOT)}", recursive=False)
        info = tarfile.TarInfo(f"{stem}/PKG-INFO")
        data = _metadata()
        info.size = len(data)
        archive.addfile(info, io.BytesIO(data))
    return filename
