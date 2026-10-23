# Working on the pure R1 calculator

Keep this package independently usable: no private repository imports or
private document identifiers in the paper, implementation, or public guides.
Cite established theorems normally. Preserve Computer Modern in the paper.
The formalization must compile without sorry, admit, new axioms, or hidden
assumptions. State its actual theorem coverage; Carlson's semantic theorem
must not be disguised as a kernel-checked definition.

Ownership during initial preparation: L1 owns lean/R1Calculator/Ordinal.lean;
L2 owns lean/R1Calculator/Patterns.lean; L3 owns r1calc/, tests/, pyproject.toml
and USAGE.md. Root owns integration, aggregate Lean modules, paper, README,
source/provenance guides, build infrastructure and Git publication. Coordinate
interfaces before touching another owner's file.

Run Lean through scripts/check_lean.py. It serializes jobs using a shared
lock and caps memory/time. No concurrent Lean jobs, dependency rebuilds,
large cold imports or unbounded searches. Stop and report a repeated build
block rather than relaunching the same expensive command. Cached dependencies
are development aids; the committed Lake configuration pins public sources.
No Git operations or nested agents from the lanes. Checkpoint honest scope
and stop when the assigned package component is complete.
