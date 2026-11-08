# Validation of parameterized numeric iteration

- Frozen specification: `f434ffbd70a5e83575da3622e4d2b6ab47fec351fbb1f094dc3e1f0f4d6c6e40`.
- Comparator preflight passed unchanged before authorship: `build-reports/1794152009133778143-6.json`.
- Final seven exact aliases and standard-axiom gate: `build-reports/1794152490593227063-6.json`.
- Actual axiom closures are printed in `exact-checks.log`; all are subsets of
  propext, Classical.choice and Quot.sound.
- Own proof namespaces and exact aliases account for 48 audited declarations.
- All 1078 current local proof/preflight sources match successful module rows
  across 19 immutable native receipts, with matching SHA-256 source bytes,
  immutable receipt/log hashes, and the unchanged bounded profile. Successful
  rows remain usable when a later module of the same run failed. All 1071 broader frozen Lean inputs also match.
- No current component warnings; existing supplier warnings were not edited.
- Native profile: 2048 MiB heap, 1536 MiB process-tree RSS, 2048 MiB minimum
  free memory, one thread, 90-second CPU and 180-second wall caps, pinned
  upstream cache only. Peak component RSS: 1105868 KiB.
- All ten checker sessions completed. Failed module outputs from four
  partially failing attempts are excluded; all module rows and native
  receipts/logs remain retained, including usable successful rows. Final successful sources are
  pinned separately from the retained exact-02 source snapshot.
- Both shared locks were free when the sole slot was released at
  `2026-11-08T15:41:49.010217+00:00`. No further compiler is scheduled.

`CLOSURE-SOURCE-PINS.json` is the portable source inventory. Detailed current
source-to-receipt/log matches, the preflight and exact receipts, wider frozen
input matches, failed attempt logs, and slot-release record remain local.
`collect-evidence-local.py` checks that evidence without running a compiler.
No existing source, frozen target, dependency, resource policy, register,
or Git state was changed. This is a focused supporting result, not a
full-root build, remote-CI result or completion of the uniform canonical
pipeline or paper 06 lem:id1.
