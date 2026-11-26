# Lossless transport of the R005 certificate evidence

This evidence-only packet recovers every byte of the independently reviewed
`uniform-certificate-downward` evidence packet, including its original README
and manifest. The original packet is unchanged. The fourteen approved Lean
source files are not duplicated here; their original paths and SHA-256 hashes
remain in `ORIGINAL-MANIFEST.json` and `SOURCES.json`.

## Storage and recovery

Only the two large sanitized JSON files are compressed:

- `CLOSURE-PINS.json.gz` recovers the original 1,666-source pin table.
- `SOURCE-NATIVE-UNION.json.gz` recovers the complete source-matched native union.

They use gzip level 9, timestamp zero, an empty stored filename and OS marker
255. The remaining evidence is byte-identical. `ORIGINAL-README.md` and
`ORIGINAL-MANIFEST.json` are renamed copies, not revised documents.
`MANIFEST.json` records both stored and original byte lengths and SHA-256 hashes
for all eleven original evidence files. Its `payload_files` plus itself are
the exact evidence-only publication allowlist.

To recover and verify the original packet into a new directory, run this
Python snippet from the repository root. It does not compile or modify proofs.

```python
from pathlib import Path
import gzip, hashlib, json
base = Path("formalization/verification/continuation-2026-11-09/uniform-certificate-downward-compressed")
m = json.loads((base / "MANIFEST.json").read_text())
out = Path("recovered-r005-evidence")
out.mkdir(exist_ok=False)
for original, info in m["original_files"].items():
    stored = Path(info["stored_path"]).read_bytes()
    assert len(stored) == info["stored_bytes"]
    assert hashlib.sha256(stored).hexdigest() == info["stored_sha256"]
    raw = gzip.decompress(stored) if info["encoding"] == "gzip" else stored
    assert len(raw) == info["original_bytes"]
    assert hashlib.sha256(raw).hexdigest() == info["original_sha256"]
    (out / Path(original).name).write_bytes(raw)
print("All eleven original evidence files recovered and verified.")
```

## Evidence scope remains unchanged

The frozen internal concrete certificate/downward package and original
unqualified application lift passed their exact gate. Actual axiom collection
covers 50 theorem declarations across 23 namespaces, using only `propext`,
`Classical.choice` and `Quot.sound`. Every one of the 1,666 current source hashes
has a successful native row in the twelve-receipt union. Seven contributing
invocations failed overall after earlier successful rows; they remain failed.
The audit05 failure is preserved separately and is not a successful contributor.

This packaging changes no mathematical or verification data. All-input
calibrated existential selection and closed all-term accessibility remain
separate. There is no register promotion, whole-root/remote-CI claim, raw log,
private path, draft source or provisional runtime design in this packet.

For bounded publication, upload binary `.gz` blobs with base64 encoding and
text files as UTF-8, then create a tree using their blob hashes. Each individual
serialized blob request is below 150 KiB; no large uncompressed JSON is uploaded.
