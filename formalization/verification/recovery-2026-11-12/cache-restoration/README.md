# Compiler-free official cache recovery

This utility ports the pinned official Mathlib cache hash algorithm using the official Lean runtime C hashing functions. It downloads only official `mathlib4-master` and legacy `mathlib4` artifacts, then optionally extracts them with bundled `leantar`. It never invokes Lean compilation, `lake build`, or a cache bootstrap. `lean --version` only verifies the runtime. It does not establish any local proof result.

1. Clone the desired repository checkpoint. Preserve its toolchain and manifest pins.
2. Download and extract the official Lean release linked in `PROVENANCE.json`.
3. Restore each Git dependency under `formalization/.lake/packages/<name>` at exactly the `rev` in `formalization/lake-manifest.json`. Do not run `lake update` or rewrite manifests. Path dependencies remain in the repository.
4. Run with your own absolute paths:

```sh
python restore_official_cache.py --formalization "$REPO/formalization" --toolchain "$LEAN_DIR" --cache-dir "$CACHE_DIR" --hash-only Mathlib.Init
python restore_official_cache.py --formalization "$REPO/formalization" --toolchain "$LEAN_DIR" --cache-dir "$CACHE_DIR" --workers 8 --unpack Mathlib
```

The smoke-test root hash is `4cc6b9c393376069`; Mathlib.Init has 61 modules in this snapshot. For a smaller recovery, replace `Mathlib` with specific external module roots from `python scripts/mathlib_imports.py YOUR_LOCAL_GATE` run inside formalization. The utility recursively adds their dependencies.

Run extraction before compiler work, not concurrently. Existing archives are downloaded again rather than blindly trusted. Downloads use temporary files; provenance and artifact SHA-256 digests are saved in the cache directory. Check failure output and do not interpret an incomplete cache as proof verification. Resume local proof work only through the repository's existing bounded checker.

This script is deliberately restricted to the documented Linux Lean4.32.0-rc1 and Mathlib pin. Its comment/import parser is a Python port validated on that source tree, not a general Lean parser. A source or pin mismatch requires review, not removing validation. Original cache hashing source attribution and Apache-2.0 notice appear in the script; see upstream mathlib4 LICENSE for license terms.
