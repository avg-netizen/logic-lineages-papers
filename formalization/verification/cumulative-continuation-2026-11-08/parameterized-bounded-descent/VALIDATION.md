# Validation of parameterized bounded descent

- Frozen specification: `c31e73c450c020897911be708c93355717f89391bf4c8acb9eac84952a2313b1`.
- Independent specification review accepted all six targets before authorship.
- Comparator preflight passed unchanged before proof authorship:
  `build-reports/1794152978502086406-10.json`.
- Six exact aliases and actual standard-axiom gate:
  `build-reports/1794153203210562738-6.json`.
- Actual axiom closures are printed in `exact-checks.log`; all are subsets of
  `propext`, `Classical.choice`, and `Quot.sound`.
- Own proof namespaces and exact aliases contain **65 audited declarations**:
  syntax 20, support 7, step support 7, step 10, induction 9, final targets 6,
  exact aliases 6.
- All **1,087** current local proof/preflight sources match successful module
  rows in **23 immutable numeric native receipts**, with matching source hashes
  and immutable receipt/log hashes. All **1,072** broader frozen Lean inputs
  also match successful rows. All **1,080** frozen/prerequisite pins remain exact.
- Successful supplier rows remain usable when a later module in that supplier
  run failed. Both new runs passed in full; there are no failed component
  attempts. The first proof candidate is retained in the local attempt snapshot.
- There are no current component warnings. Existing warnings in 63 supplier
  modules were not changed; their native evidence remains available locally.
- The accepted parameterized iteration supplier's portable manifest is
  `7f7af8d2a350387bd4c71999ac822018c8951de9296120b1e35b7787c2b775eb`.
  Only its internal zero/front-successor/fixed-point laws are used; the
  separate external evaluation theorem is not a reflection principle.
- Native profile: 2048 MiB heap, 1536 MiB process-tree RSS, 2048 MiB minimum
  free memory, one thread, 90-second CPU and 180-second wall caps, pinned
  upstream cache only. Peak component RSS was **1,062,748 KiB**; the maximum
  across all matched supplier rows was **1,176,760 KiB**.
- Both checker sessions finished. The actual shared locks were free when
  the sole compiler slot was released at **2026-11-08T15:53:49.677142+00:00**.
  No further compiler run is scheduled.

`CLOSURE-SOURCE-PINS.json` is the portable current source inventory. The
complete source-to-receipt/log matches, broader frozen-input matches,
preflight/exact receipts, first-candidate snapshot, collection script, and
slot-release record remain local evidence, not public proof dependencies.
The collector checks existing receipts and never invokes a compiler.

The frozen specification and correspondence preserve their original pre-proof
status; `ACCEPTANCE.json` and `STATUS.md` record the subsequent checked result.
No existing source, frozen target, dependency, resource policy, global source
register, or Git state was changed. This focused supporting result does not
complete the uniform canonical pipeline or paper 06 `lem:id1` and is not a
full-root build or remote-CI result.
