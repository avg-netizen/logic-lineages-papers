# Independent migration review

Reviewed 18 November 2026. Read-only review; no compiler run, mathematical proof
acceptance, source modification, register promotion or Git publication performed.

## Verified preservation

- All 80 `MANIFEST.json` entries have matching byte counts and SHA-256 bytes at
  both their archived path and original root compatibility path. The six root
  entry points 05–10 are symlinks into the archive.
- Compared with formalization base `92459c206c0d1fc636062ce7481c6d70871f8857`,
  all **20,650** existing files under `formalization/LogicLineages/` are byte
  identical, and `formalization/TARGETS.json` is byte identical. New namespaces
  do not replace the old proof tree.
- Of the 80 archived files, 74 match that base exactly. The six README files
  incorporate the historical-edition/new-reading navigation imported from the
  explanatory-paper branch (and retain later existing status where applicable).
  Thus the manifest records the post-import archive bytes, not a claim that
  every README is the unchanged base edition. No mathematical TeX/PDF/source
  repair or checked counterexample was changed by this migration.
- All **76** tracked files in the five new paper directories match source commit
  `17377d6d02d20b26b0cf34ab50bb9d52d7c32305` byte-for-byte, including mathematical
  TeX, PDFs, bibliographies, document receipts and scripts.

## Independent inventory check

Followed literal `\\input`/`\\include` edges recursively from each `paper.tex`,
stripping TeX line comments. No included file was missing. All theorem-bearing
files reached by this graph are present in the new register's source file pins.
All theorem/lemma/proposition/corollary environments were counted, and matched
unique labeled statement entries, full source text, source line, kind and hash.
The existing verifier was also run successfully, but the input-graph check and
Git blob comparisons above were independent of it.

| Paper | Reached TeX files | Labeled statements | Statements in root paper.tex |
| --- | ---: | ---: | ---: |
| 16 | 6 | 38 | 1 |
| 17 | 9 | 33 | 1 |
| 18 | 10 | 50 | 0 |
| 19 | 9 | 21 | 0 |
| 20 | 8 | 25 | 1 |
| Total | 42 | 167 | 3 |

All 167 entries and all five paper-level statuses are `pending`. No old checked
status is mechanically transferred. Definition/example/remark environments are
not silently counted as proved theorems. This inventory is not proof validation
or a statement that all implicit mathematical dependencies have been enumerated.

## Navigation finding and verified repair

Direct access through original compatibility paths succeeds for all 80 files.
However, **17 relative links in archived README files** do not resolve from their
physical archive directory. Examples include `../16-persistent-marking-termination-ordering`,
`../formalization`, and `../COMPARISON-RESOLUTION-GUIDE.md`. Root symlinks alone do
not repair these archive-relative references. Recommended non-destructive repair:
add archive-parent compatibility links to the referenced current directories and
root guide, keeping all archived file bytes and hashes unchanged. GitHub's web
rendering of directory symlinks has not been tested, so no broad web-navigation
claim is made.

The coordinator subsequently added seven archive-parent compatibility symlinks
(five current-paper directories, formalization, and the resolution guide) and a
browser-oriented index containing direct archive-relative PDF/TeX/README links.
Rechecked 69 local relative links across that index and the six archived READMEs:
all resolve. All 80 archived hashes and sizes remain unchanged. The index's
18 direct archive document targets are ordinary files, not directory-symlink
routes. No live GitHub browser rendering was performed.

## Verdict

Source preservation, the 167-statement pending register, and repaired local
archive-relative navigation pass. Mathematical TeX/PDF bytes remain preserved.
The six historical README banner/navigation changes were inherited from the
imported explanatory source branch, not changes to mathematical claims or
proof artifacts. No additional work or compiler run followed this review.
