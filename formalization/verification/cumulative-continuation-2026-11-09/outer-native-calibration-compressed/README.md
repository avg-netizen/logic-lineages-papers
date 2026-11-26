# Lossless transport of the Outer native calibration evidence

This evidence-only packet recovers every byte of the approved original
`outer-native-calibration/portable` packet, including its original README and
publication manifest. The original packet remains unchanged. Its five Lean
sources are already published and byte-verified at
`4045ff79e572870fda90b8d9b4c8dbfaae5e441c`; no source is duplicated here.

## Storage and recovery

Only the large sanitized `SOURCE-NATIVE-COVERAGE.json` is compressed. The gzip
file uses level 9, timestamp zero, empty stored filename and OS marker 255.
Every other original evidence file is byte-identical. `ORIGINAL-README.md`
and `ORIGINAL-MANIFEST.json` are renamed copies, not revised documents.

`MANIFEST.json` records original and stored byte lengths and SHA-256 hashes
for all ten original evidence files. Its `payload_files` plus itself are the
exact evidence-only publication allowlist. Original source hashes remain in
`SOURCE-PINS.json` and `ORIGINAL-MANIFEST.json`; they are not upload actions.

To recover and verify into a new directory, run from the repository root:

```python
from pathlib import Path
import gzip, hashlib, json
base = Path("formalization/verification/cumulative-continuation-2026-11-09/outer-native-calibration-compressed")
m = json.loads((base / "MANIFEST.json").read_text())
out = Path("recovered-outer-native-calibration-evidence")
out.mkdir(exist_ok=False)
for original, info in m["original_files"].items():
    stored = Path(info["stored_path"]).read_bytes()
    assert len(stored) == info["stored_bytes"]
    assert hashlib.sha256(stored).hexdigest() == info["stored_sha256"]
    raw = gzip.decompress(stored) if info["encoding"] == "gzip" else stored
    assert len(raw) == info["original_bytes"]
    assert hashlib.sha256(raw).hexdigest() == info["original_sha256"]
    (out / Path(original).name).write_bytes(raw)
print("All ten original evidence files recovered and verified.")
```

## Unchanged evidence scope

Four exact supporting native targets and all 14 own theorem closures passed
with only standard axioms. All 1,343 current local candidate import-closure
sources have individually source-matched successful native rows across 13
receipts. Four contributing invocations FAILED overall; only successful
matching rows count. The first own candidate's failure and subsequent
proof-only repair remain explicit. The separate Preflight module is additional
owned successful evidence outside that candidate closure. This is not a fresh
full-closure/root build or remote-CI claim.

This package makes no mathematical change. It calibrates the same selected
Data, original scalar/typed wrappers, base computability and full inactive
fallbacks. Complete global source selection, resultOption success/result/
application/lift, positive/source calibration and paper06ID1 remain outside
this packet's scope. It includes no raw full logs, private paths, unfrozen
designs, source edits, root imports, register or manuscript changes.

For bounded publication, upload `.gz` as base64 and text as UTF-8, then create
a tree using blob hashes. Each individual serialized blob request must remain
below 250 KiB; `MANIFEST.json` provides conservative request-size bounds with
16 KiB reserved for routing/envelope fields. No large original JSON is uploaded.
