Local workers paused at the user-requested 10 p.m. America/Chicago cutoff (30 October 2026 03:00 UTC). No automatic local resume. Separately authorized external work and fresh-clone builds remain possible.

# Formalizing the public papers

The user explicitly resumed local formalization on 29 October 2026 after the
external continuation at `abb52d9`: two independent Codex lanes, one Codex-led
Claude loop, and the main thread. Start from `EXTERNAL-CONTINUATION.md`, not the
earlier pause counts. Papers 11 and 13 have their registered mathematical scope
checked. The older pause receipts remain historical evidence. This release
does not resume private II5/post-ETH/SHA research or authorize Git publication.

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
models/algebra lane writes the PGroups and Differential subdirectories of
`LogicLineages/ModelsAlgebra/` and its status; the Claude-loop lead writes
`LogicLineages/ComputabilityKnowledge/`, its status and the private formalization
author subject. Main now owns `LogicLineages/ModelsAlgebra/Forests/` and paper 03,
alongside the completed Ultrafilters/RL streams, root specifications, package
configuration, shared audit/build tools, global target register and Git.
No concurrent compiler, cold upstream rebuild, unrelated research or automatic
Git operation. Reused 3.1.3 modules require a checked import closure, provenance
and a statement match; the old aggregate project is not a blanket dependency.

Use the measured external Mathlib profile explicitly for focused checks:
`python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 MODULE`.
Core-only closures may use the existing stricter core profile. Shared locks,
single-thread limits, CPU/wall caps and system-memory guards remain active.
Do not repeatedly hit the old default RSS ceiling or raise limits in response
to proof failures. Coordinate native compiler turns with the main thread.
Claude R004 retained its original author/compiler locks until its return. From R005,
the reviewed private runner may overlap the exact read-only author (512 MiB
observed RSS cap) with one serialized native compiler when at least 3072 MiB
is available at author launch. Otherwise it falls back to serialized authoring.
The same-session author lock, native compiler locks, process observation and
memory-floor checks stay active; no current process's locks are released.
