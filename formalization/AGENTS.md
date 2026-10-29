# Formalizing the public papers

Local Codex lanes and the managed Claude loop are paused by the user's explicit
29 October 2026 instruction. Do not restart them automatically. A separately
user-authorized external agent may continue from `EXTERNAL-HANDOFF.md`; the local
pause does not require that agent to obtain another approval for its assigned
mathematical work. Local lane-ownership names below describe the saved split.

All fifteen papers are in scope, including cited mathematical suppliers absent
from Lean/Mathlib. Full targets are pending until their entire formal dependency
chain is proved. Do not replace a missing theorem by an axiom, class field,
oracle or new premise and report the resulting implication as completion.
Keep the actual source domains, semantics, quantifiers and effectiveness claims.

No `sorry`, `admit`, added axioms, `native_decide` or unsafe proof shortcuts.
Accepted declarations may depend only on the usual `propext`, `Classical.choice`
and `Quot.sound` foundations. Definitions of target propositions are useful
specifications; definitions engineered to make the desired mathematics true
are not proofs of the paper's semantics.

Codex writes and freezes the exact comparison statement BEFORE Claude authors
proof steps. Keep comparator/semantics files separate from candidate proof files.
Record paper correspondence and hashes. Compile first. If compilation succeeds,
check the theorem against the frozen type and audit its actual axiom closure;
do not routinely repeat a full hand proof audit. Repair compiler failures or
statement mismatches without silently weakening the target.

Run compilers only through `python3 scripts/check.py MODULE_OR_FILE ...` from
this directory. The helper serializes Lean with the calculator's lock as well
as this programme's lock, sets one worker and bounded heap/CPU/wall limits,
and never downloads or rebuilds upstream dependencies. It can borrow the
already pinned local Mathlib cache for development; no private source import
may be required by a public proof. An incomplete target must remain explicitly
pending even when its intermediate lemmas compile.

Ownership: ordinal lane writes `LogicLineages/OrdinalComparison/` and its status;
models/algebra lane writes `LogicLineages/ModelsAlgebra/` and its status; the
Claude-loop lead writes `LogicLineages/ComputabilityKnowledge/` and its status.
Main owns `LogicLineages/Ultrafilters/`, `LogicLineages/RL/`, root specifications,
package configuration, shared audit/build tools, global target register and Git.
No concurrent compiler, cold upstream rebuild, unrelated research or automatic
Git operation. Reused 3.1.3 modules require a checked import closure, provenance
and a statement match; the old aggregate project is not a blanket dependency.
