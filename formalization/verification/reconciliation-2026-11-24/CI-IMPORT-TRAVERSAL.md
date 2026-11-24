# Pre-merge CI import traversal correction

Draft PR #12 exposed the same inherited Python call-stack overflow in
two validation entry points. In Checked paper components run
45372810780, initially the upstream cache collector
(`scripts/mathlib_imports.py`, line 45) overflowed; later the fresh Lean
checker (`scripts/check.py`, line 396) failed before invoking Lean.
The first traceback occurred in process substitution. The final job
failed at the fresh local build step. Pure R1 Lean verification run
45372810895 succeeded.

The default Python recursion limit is 1,000. On these exact sources the
public accepted-gate plan contains 2,019 requested gates and 15,456
reachable local modules, with a longest import chain of 1,657. The
standalone Mathlib collector now returns all 355 of its sorted cache
roots. These are planning numbers, not a build success.

Both tools now use the same explicit enter/exit depth-first traversal
and unchanged nested-comment scanner. The native compile order remains
dependency-first and deterministic in source import order. Real local
cycles report their module, and the native placeholder scan still
runs before any compiler launch. Source resolution, artifact cache
binding, lock checks, resource controls and pins are unchanged.
In the existing workflow, both list producers now write to checked
temporary files and must succeed with a nonempty list before the cache
or gate consumer runs. That closes the process-substitution error
path without changing any triggers, steps, limits or verification scope.
No recursion limit bump, suppression, or skipped suite.

Twenty-eight immutable older acceptance records pin the previous
checker bytes. The reconciliation preserves that exact historical
tool file and validates precisely those record IDs against it, without
rewriting past evidence or treating it as the current checker.

The 1,301-node fixture exercises both entry points. The collector
returns the deepest leaf's Mathlib root; the native entry point invokes
an isolated stub at that exact deepest source. A real cycle through the
same depth is rejected in both tools, and a forbidden proof placeholder
in the deepest file still prevents compiler launch. A separate diamond
checks shared imports, multiple roots, source ordering and nested
comments. The workflow plumbing is also tested against a successful
two-item producer, a producer that fails after partial output, and
a producer that reports success but gives an empty list. The complete
local Python test suite (49 tests) passes.

The pre-merge candidate's focused Lean recheck was already running
with the previous checker invocation when this traversal bug in the
unrelated full aggregate closure was observed; those exact Lean sources
are unchanged. The corrected CI is distinct from that focused gate.
